"""Tests for src/integration/zusd_api.py — zUSD REST API handlers."""

from __future__ import annotations

import json
import sys
import types

import pytest

from src.integration import perps_api as perps_demo_api
import src.integration.zusd_tau_gate as zusd_tau_gate
from src.core.zusd import E8
from src.integration.zusd_api import handle_zusd_request, reset_demo_state


@pytest.fixture(autouse=True)
def _reset_state_and_env(monkeypatch):
    reset_demo_state()
    perps_demo_api.reset_demo_state()
    monkeypatch.setenv("ZUSD_TAU_GATE_ENABLED", "0")
    monkeypatch.delenv("ZUSD_TAU_BIN", raising=False)
    monkeypatch.delenv("ZUSD_TAU_ALLOW_PATH_LOOKUP", raising=False)
    monkeypatch.delenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", raising=False)
    monkeypatch.delenv("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", raising=False)
    monkeypatch.delenv("ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS", raising=False)
    monkeypatch.delenv("ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG", raising=False)
    yield
    reset_demo_state()
    perps_demo_api.reset_demo_state()


def _post(path: str, body: dict) -> tuple[int, dict]:
    raw = json.dumps(body).encode("utf-8")
    return handle_zusd_request("POST", path, raw)


class TestGetState:
    def test_single_state_defaults(self):
        status, body = handle_zusd_request("GET", "/api/zusd/state", None)
        assert status == 200
        assert body["ok"] is True
        assert body["mode"] == "single"
        assert body["state"]["debt_e8"] == 0

    def test_multi_state_defaults(self):
        status, body = handle_zusd_request("GET", "/api/zusd/multi/state", None)
        assert status == 200
        assert body["ok"] is True
        assert body["mode"] == "multi"
        assert body["state"]["vault_a"]["debt_e8"] == 0
        assert body["state"]["vault_b"]["debt_e8"] == 0


class TestSingleFlow:
    def test_bootstrap_deposit_mint(self):
        s1, b1 = _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        assert s1 == 200
        assert b1["ok"] is True

        s2, b2 = _post("/api/zusd/step", {"tag": "deposit_collateral", "args": {"amount_e8": 2 * E8}})
        assert s2 == 200
        assert b2["ok"] is True

        s3, b3 = _post("/api/zusd/step", {"tag": "mint_zusd", "args": {"amount_e8": 100 * E8}})
        assert s3 == 200
        assert b3["ok"] is True
        assert b3["state"]["debt_e8"] == 100 * E8
        assert b3["state"]["free_debt_e8"] == 100 * E8

    def test_rejected_action_returns_400(self):
        status, body = _post("/api/zusd/step", {"tag": "mint_zusd", "args": {"amount_e8": 1}})
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"


class TestMultiFlow:
    def test_multi_bootstrap_and_mint(self):
        s1, _b1 = _post("/api/zusd/multi/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        assert s1 == 200

        s2, _b2 = _post("/api/zusd/multi/step", {"tag": "deposit_collateral", "args": {"vault": "a", "amount_e8": 2 * E8}})
        assert s2 == 200

        s3, b3 = _post("/api/zusd/multi/step", {"tag": "mint_zusd", "args": {"vault": "a", "amount_e8": 100 * E8}})
        assert s3 == 200
        assert b3["state"]["vault_a"]["debt_e8"] == 100 * E8


class TestPerpOracleSyncGate:
    def test_sync_gate_accepts_aligned_price_and_epoch_lag(self, monkeypatch):
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", "1")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", "TAU-USD")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS", "0")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG", "5000")

        status, body = _post(
            "/api/zusd/step",
            {"tag": "bootstrap_oracle", "args": {"price_e8": 50_000_000, "auth_ok": True}},
        )
        assert status == 200
        assert body["ok"] is True
        assert body["state"]["price_e8"] == 50_000_000

    def test_sync_gate_rejects_price_divergence(self, monkeypatch):
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", "1")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", "TAU-USD")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS", "100")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG", "5000")

        status, body = _post(
            "/api/zusd/step",
            {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}},
        )
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_sync_divergence" in str(body.get("detail", ""))

    def test_sync_gate_rejects_epoch_lag(self, monkeypatch):
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", "1")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", "TAU-USD")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS", "0")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_EPOCH_LAG", "0")

        status, body = _post(
            "/api/zusd/step",
            {"tag": "bootstrap_oracle", "args": {"price_e8": 50_000_000, "auth_ok": True}},
        )
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_sync_epoch_lag" in str(body.get("detail", ""))


class TestTauGateWiring:
    def test_tau_gate_enabled_and_passing(self, monkeypatch):
        monkeypatch.setenv("ZUSD_TAU_GATE_ENABLED", "1")
        monkeypatch.setenv("ZUSD_TAU_BIN", sys.executable)
        monkeypatch.setenv("ZUSD_TAU_ALLOW_PATH_LOOKUP", "0")

        def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
            assert len(steps) == 1
            return {0: {"o4": 1}}

        monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _fake_tau)

        _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        _post("/api/zusd/step", {"tag": "deposit_collateral", "args": {"amount_e8": 2 * E8}})
        status, body = _post("/api/zusd/step", {"tag": "mint_zusd", "args": {"amount_e8": 100 * E8}})

        assert status == 200
        assert body["ok"] is True
        assert body["tauGate"]["enabled"] is True

    def test_tau_gate_enabled_and_failing(self, monkeypatch):
        monkeypatch.setenv("ZUSD_TAU_GATE_ENABLED", "1")
        monkeypatch.setenv("ZUSD_TAU_BIN", sys.executable)
        monkeypatch.setenv("ZUSD_TAU_ALLOW_PATH_LOOKUP", "0")

        def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
            if spec_path.name == "zusd_mint_guard_v1.tau":
                return {0: {"o4": 0}}
            return {0: {"o4": 1}}

        monkeypatch.setattr(zusd_tau_gate, "run_tau_spec_steps", _fake_tau)

        _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        _post("/api/zusd/step", {"tag": "deposit_collateral", "args": {"amount_e8": 2 * E8}})
        status, body = _post("/api/zusd/step", {"tag": "mint_zusd", "args": {"amount_e8": 100 * E8}})

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "tau_gate_rejected" in str(body.get("detail", ""))


class TestRouting:
    def test_unknown_get(self):
        status, body = handle_zusd_request("GET", "/api/zusd/unknown", None)
        assert status == 404
        assert body["error"] == "not_found"

    def test_unknown_post_no_body(self):
        status, body = handle_zusd_request("POST", "/api/zusd/unknown", None)
        assert status == 404
        assert body["error"] == "not_found"

    def test_method_not_allowed(self):
        status, body = handle_zusd_request("DELETE", "/api/zusd/state", None)
        assert status == 405
        assert body["error"] == "method_not_allowed"


class TestHistoryAndReset:
    def test_history_and_reset(self):
        _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        hs, hb = handle_zusd_request("GET", "/api/zusd/history", None)
        assert hs == 200
        assert hb["ok"] is True
        assert len(hb["history"]) >= 1

        rs, rb = _post("/api/zusd/reset", {})
        assert rs == 200
        assert rb["ok"] is True
        assert rb["state"]["debt_e8"] == 0


class TestApiServerZusdGate:
    def test_zusd_api_gated_off_returns_404(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = False

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/state"
        h.headers = {}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 404
        assert captured["obj"]["error"] == "not_found"

    def test_zusd_api_gated_on_returns_200(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/state"
        h.headers = {}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True

    def test_zusd_post_gated_off_returns_404(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = False

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/step"
        h.headers = {"Content-Length": "2"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return json.dumps({"tag": "advance_epoch", "args": {"delta": 1}}).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 404

    def test_zusd_post_gated_on_returns_200(self, monkeypatch):
        from src.integration.api_server import _Handler

        monkeypatch.setenv("ZUSD_TAU_GATE_ENABLED", "0")

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/step"
        h.headers = {"Content-Length": "2"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return json.dumps({"tag": "advance_epoch", "args": {"delta": 1}}).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True

    def test_zusd_api_token_required_returns_401(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/state"
        h.headers = {}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 401
        assert captured["obj"]["error"] == "unauthorized"

    def test_zusd_api_token_allows_valid_bearer(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/state"
        h.headers = {"Authorization": "Bearer sekret"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True

    def test_zusd_post_token_required_returns_401(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/step"
        h.headers = {"Content-Length": "2"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return json.dumps({"tag": "advance_epoch", "args": {"delta": 1}}).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 401
        assert captured["obj"]["error"] == "unauthorized"

    def test_zusd_post_token_allows_valid_bearer(self):
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            zusd_api_enabled = True
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/zusd/step"
        h.headers = {"Content-Length": "2", "Authorization": "Bearer sekret"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return json.dumps({"tag": "advance_epoch", "args": {"delta": 1}}).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True
