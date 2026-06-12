"""Tests for src/integration/zusd_api.py — zUSD REST API handlers."""

from __future__ import annotations

import json
import sys
import types

import pytest

import src.integration.zusd_tau_gate as zusd_tau_gate
from src.core.zusd import E8, ZUSDState
from src.integration import perps_api as perps_demo_api
from src.integration.zusd_api import (
    _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
    _zusd_oracle_runtime_facts,
    _tau_gate_config_from_env,
    handle_zusd_request,
    reset_demo_state,
)
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from tests.integration.oracle_authorization_test_helpers import authorization_bundle


@pytest.fixture(autouse=True)
def _reset_state_and_env(monkeypatch):
    reset_demo_state()
    perps_demo_api.reset_demo_state()
    monkeypatch.setenv("ZUSD_TAU_GATE_ENABLED", "0")
    monkeypatch.delenv("ZUSD_TAU_BIN", raising=False)
    monkeypatch.delenv("ZUSD_TAU_ALLOW_PATH_LOOKUP", raising=False)
    monkeypatch.delenv("ZUSD_ORACLE_ADAPTER_REQUIRED", raising=False)
    monkeypatch.delenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", raising=False)
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


def _hash(domain: str, name: str) -> str:
    return semantic_hash(domain, {"name": name})


def _authorization_for_runtime(
    runtime,  # type: ignore[no-untyped-def]
    *,
    value_e8: int,
    evidence_class: str = "O3",
    observed_epoch: int | None = None,
    expires_at_epoch: int | None = None,
    envelope_id: str = "econ:zusd-bootstrap-v1",
) -> dict:
    observed = int(runtime.now_epoch if observed_epoch is None else observed_epoch)
    authorization = {
        "consumer_module": runtime.consumer_module,
        "action_kind": runtime.action_kind,
        "action_id": runtime.action_id,
        "action_facts_hash": runtime.action_facts_hash,
        "pre_state_hash": runtime.pre_state_hash,
        "profile_id": runtime.profile_id,
        "query_id": runtime.query_id,
        "value_e8": value_e8,
        "value_hash": oracle_value_hash(
            query_id=runtime.query_id,
            value_e8=value_e8,
            observed_epoch=observed,
        ),
        "confidence_e8": 0,
        "deviation_bps": 0,
        "observed_epoch": observed,
        "expires_at_epoch": int(runtime.now_epoch if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:zusd-price:v1",
        "feed_registry_root": _hash("zenodex.feed_registry.v1", "zusd"),
        "query_policy_root": _hash("zenodex.query_policy.v1", "zusd"),
        "source_registry_root": _hash("zenodex.source_registry.v1", "zusd"),
        "reporter_registry_root": _hash("zenodex.reporter_registry.v1", "zusd"),
        "evidence_class": evidence_class,
        "economic_envelope_id": envelope_id,
        "receipt_graph_root": _hash("zenodex.receipt_graph.v1", "zusd"),
    }
    return authorization_bundle(authorization)


def _zusd_bootstrap_authorization(
    *,
    price_e8: int,
    query_id: str = "query:ZUSD/PRICE",
    evidence_class: str = "O3",
    observed_epoch: int | None = None,
    expires_at_epoch: int | None = None,
) -> dict:
    status, body = handle_zusd_request("GET", "/api/zusd/state", None)
    assert status == 200
    runtime = _zusd_oracle_runtime_facts(
        mode="single",
        state=ZUSDState(**body["state"]),
        tag="bootstrap_oracle",
        query_id=query_id,
        runtime_value_e8=price_e8,
    )
    return _authorization_for_runtime(
        runtime,
        value_e8=price_e8,
        evidence_class=evidence_class,
        observed_epoch=observed_epoch,
        expires_at_epoch=expires_at_epoch,
    )


def _zusd_mint_authorization(*, amount_e8: int, value_e8: int | None = None) -> dict:
    status, body = handle_zusd_request("GET", "/api/zusd/state", None)
    assert status == 200
    state = ZUSDState(**body["state"])
    args = {"amount_e8": amount_e8}
    runtime_value = int(state.price_e8 if value_e8 is None else value_e8)
    runtime = _zusd_oracle_runtime_facts(
        mode="single",
        state=state,
        tag="mint_zusd",
        args=args,
        query_id=_ORACLE_ZUSD_COLLATERAL_QUERY_ID,
        runtime_value_e8=runtime_value,
    )
    return _authorization_for_runtime(
        runtime,
        value_e8=runtime_value,
        envelope_id="econ:zusd-mint-v1",
    )


def _bootstrap_and_deposit() -> None:
    s1, b1 = _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
    assert s1 == 200
    assert b1["ok"] is True
    s2, b2 = _post("/api/zusd/step", {"tag": "deposit_collateral", "args": {"amount_e8": 2 * E8}})
    assert s2 == 200
    assert b2["ok"] is True


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


class TestOracleAuthorizationGate:
    def test_required_typed_oracle_authorization_accepts_matching_bootstrap(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        price_e8 = 100 * E8
        authorization = _zusd_bootstrap_authorization(price_e8=price_e8)

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": price_e8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 200
        assert body["ok"] is True
        assert body["state"]["price_e8"] == price_e8

    def test_required_typed_oracle_authorization_rejects_missing_bundle(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": 100 * E8,
                    "auth_ok": True,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert body["detail"] == "oracle_authorization_required"

    def test_required_typed_oracle_authorization_rejects_runtime_price_mismatch(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        authorization = _zusd_bootstrap_authorization(price_e8=100 * E8)

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": 101 * E8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "runtime_value_e8 mismatch" in body["detail"]

    def test_required_typed_oracle_authorization_rejects_below_o3_evidence(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        price_e8 = 100 * E8
        authorization = _zusd_bootstrap_authorization(price_e8=price_e8, evidence_class="O2")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": price_e8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "evidence_class below required O3" in body["detail"]

    def test_required_typed_oracle_authorization_rejects_expired_authorization(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        price_e8 = 100 * E8
        status, body = _post("/api/zusd/step", {"tag": "advance_epoch", "args": {"delta": 2}})
        assert status == 200
        assert body["ok"] is True
        authorization = _zusd_bootstrap_authorization(
            price_e8=price_e8,
            observed_epoch=1,
            expires_at_epoch=1,
        )

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": price_e8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "authorization expired" in body["detail"]

    def test_required_typed_oracle_authorization_invalid_env_fails_closed(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "tru")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "bootstrap_oracle",
                "args": {
                    "price_e8": 100 * E8,
                    "auth_ok": True,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_authorization_config_error" in body["detail"]

    def test_required_typed_oracle_authorization_mint_requires_authorization(self, monkeypatch):
        _bootstrap_and_deposit()
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "mint_zusd",
                "args": {
                    "amount_e8": 100 * E8,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert body["detail"] == "oracle_authorization_required"

    def test_required_typed_oracle_authorization_mint_accepts_bound_authorization(self, monkeypatch):
        _bootstrap_and_deposit()
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        amount_e8 = 100 * E8
        authorization = _zusd_mint_authorization(amount_e8=amount_e8)

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "mint_zusd",
                "args": {
                    "amount_e8": amount_e8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 200
        assert body["ok"] is True
        assert body["state"]["debt_e8"] == amount_e8

    def test_required_typed_oracle_authorization_mint_rejects_wrong_runtime_value(self, monkeypatch):
        _bootstrap_and_deposit()
        monkeypatch.setenv("ZUSD_ORACLE_AUTHORIZATION_REQUIRED", "1")
        amount_e8 = 100 * E8
        authorization = _zusd_mint_authorization(amount_e8=amount_e8, value_e8=101 * E8)

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "mint_zusd",
                "args": {
                    "amount_e8": amount_e8,
                    "oracle_authorization": authorization,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "runtime_value_e8 mismatch" in body["detail"]


class TestOracleAdapterGate:
    def test_oracle_adapter_mint_requires_bridge_when_configured(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_ADAPTER_REQUIRED", "1")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "mint_zusd",
                "args": {
                    "amount_e8": 1,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert body["detail"] == "mint requires oracle_adapter_bridge"

    def test_oracle_adapter_invalid_env_fails_closed(self, monkeypatch):
        monkeypatch.setenv("ZUSD_ORACLE_ADAPTER_REQUIRED", "maybe")

        status, body = _post(
            "/api/zusd/step",
            {
                "tag": "mint_zusd",
                "args": {
                    "amount_e8": 1,
                },
            },
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_adapter_config_error" in body["detail"]
        assert "ZUSD_ORACLE_ADAPTER_REQUIRED" in body["detail"]


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

    def test_sync_gate_rejects_malformed_enabled_flag(self, monkeypatch):
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", "maybe")

        status, body = _post(
            "/api/zusd/step",
            {"tag": "bootstrap_oracle", "args": {"price_e8": 50_000_000, "auth_ok": True}},
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_sync_config_error" in str(body.get("detail", ""))
        assert "ZUSD_PERP_ORACLE_SYNC_ENABLED" in str(body.get("detail", ""))

    def test_sync_gate_rejects_malformed_divergence_bound(self, monkeypatch):
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_ENABLED", "1")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MARKET_ID", "TAU-USD")
        monkeypatch.setenv("ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS", "nan")

        status, body = _post(
            "/api/zusd/step",
            {"tag": "bootstrap_oracle", "args": {"price_e8": 50_000_000, "auth_ok": True}},
        )

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "rejected"
        assert "oracle_sync_config_error" in str(body.get("detail", ""))
        assert "ZUSD_PERP_ORACLE_SYNC_MAX_DIVERGENCE_BPS" in str(body.get("detail", ""))


class TestTauGateWiring:
    def test_tau_gate_defaults_to_absolute_path_resolution(self, monkeypatch):
        monkeypatch.delenv("ZUSD_TAU_ALLOW_PATH_LOOKUP", raising=False)
        cfg = _tau_gate_config_from_env()
        assert cfg.allow_path_lookup is False

    def test_tau_gate_rejects_nonfinite_timeout_env(self, monkeypatch):
        monkeypatch.setenv("ZUSD_TAU_GATE_TIMEOUT_S", "nan")

        status, body = _post("/api/zusd/step", {"tag": "advance_epoch", "args": {"delta": 1}})

        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "config_error"
        assert "ZUSD_TAU_GATE_TIMEOUT_S" in body["detail"]

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


class TestOracleRecoveryLifecycleApi:
    def test_build_and_verify_oracle_recovery_lifecycle_packet(self):
        s1, b1 = _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        assert s1 == 200
        s2, b2 = _post("/api/zusd/step", {"tag": "advance_epoch", "args": {"delta": 150}})
        assert s2 == 200

        stale_state = b2["state"]
        s3, b3 = _post(
            "/api/zusd/build_oracle_pending_gate_contract",
            {"state": stale_state, "risky_requested": True, "tcr_ok": True},
        )
        assert s3 == 200
        assert b3["ok"] is True
        previous_pending = b3["contract"]
        assert previous_pending["action_allowed"] is False

        s4, _b4 = _post("/api/zusd/step", {"tag": "oracle_report", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        assert s4 == 200
        s5, b5 = _post("/api/zusd/step", {"tag": "oracle_commit", "args": {"auth_ok": True}})
        assert s5 == 200
        current_state = b5["state"]

        s6, b6 = _post(
            "/api/zusd/build_oracle_pending_gate_contract",
            {"state": current_state, "risky_requested": True, "tcr_ok": True},
        )
        assert s6 == 200
        assert b6["ok"] is True
        current_pending = b6["contract"]
        assert current_pending["action_allowed"] is True

        s7, b7 = _post(
            "/api/zusd/build_cross_module_oracle_sync_contract",
            {
                "market_id": "TAU-USD",
                "zusd_price_e8": current_state["price_e8"],
                "zusd_epoch": current_state["oracle_last_update_epoch"],
                "perp_price_e8": current_state["price_e8"],
                "perp_oracle_epoch": current_state["oracle_last_update_epoch"],
                "max_divergence_bps": 0,
                "max_epoch_lag": 0,
            },
        )
        assert s7 == 200
        assert b7["ok"] is True
        current_sync = b7["contract"]
        assert current_sync["sync_gate_ok"] is True

        s8, b8 = _post(
            "/api/zusd/build_oracle_recovery_lifecycle_packet",
            {
                "previous_pending_gate_contract": previous_pending,
                "current_pending_gate_contract": current_pending,
                "current_sync_contract": current_sync,
            },
        )
        assert s8 == 200
        assert b8["ok"] is True
        packet = b8["packet"]
        assert packet["risky_ops_reenabled"] is True
        assert packet["rejected_with_reason"] is False
        assert packet["lifecycle_ok"] is True

        s9, b9 = _post("/api/zusd/verify_oracle_pending_gate_contract", {"contract": previous_pending})
        assert s9 == 200
        assert b9["ok"] is True
        s10, b10 = _post("/api/zusd/verify_cross_module_oracle_sync_contract", {"contract": current_sync})
        assert s10 == 200
        assert b10["ok"] is True
        s11, b11 = _post("/api/zusd/verify_oracle_recovery_lifecycle_packet", {"packet": packet})
        assert s11 == 200
        assert b11["ok"] is True
        assert b11["error"] is None

    def test_verify_oracle_recovery_lifecycle_packet_rejects_tampering(self):
        s1, _b1 = _post("/api/zusd/step", {"tag": "bootstrap_oracle", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        assert s1 == 200
        s2, b2 = _post("/api/zusd/step", {"tag": "advance_epoch", "args": {"delta": 150}})
        assert s2 == 200
        stale_state = b2["state"]
        _, b3 = _post(
            "/api/zusd/build_oracle_pending_gate_contract",
            {"state": stale_state, "risky_requested": True, "tcr_ok": True},
        )
        _post("/api/zusd/step", {"tag": "oracle_report", "args": {"price_e8": 100 * E8, "auth_ok": True}})
        _, b5 = _post("/api/zusd/step", {"tag": "oracle_commit", "args": {"auth_ok": True}})
        current_state = b5["state"]
        _, b6 = _post(
            "/api/zusd/build_oracle_pending_gate_contract",
            {"state": current_state, "risky_requested": True, "tcr_ok": True},
        )
        _, b7 = _post(
            "/api/zusd/build_cross_module_oracle_sync_contract",
            {
                "market_id": "TAU-USD",
                "zusd_price_e8": current_state["price_e8"],
                "zusd_epoch": current_state["oracle_last_update_epoch"],
                "perp_price_e8": current_state["price_e8"],
                "perp_oracle_epoch": current_state["oracle_last_update_epoch"],
                "max_divergence_bps": 0,
                "max_epoch_lag": 0,
            },
        )
        _, b8 = _post(
            "/api/zusd/build_oracle_recovery_lifecycle_packet",
            {
                "previous_pending_gate_contract": b3["contract"],
                "current_pending_gate_contract": b6["contract"],
                "current_sync_contract": b7["contract"],
            },
        )
        packet = b8["packet"]
        packet["rejected_with_reason"] = True

        status, body = _post("/api/zusd/verify_oracle_recovery_lifecycle_packet", {"packet": packet})
        assert status == 200
        assert body["ok"] is False
        assert body["error"] == "rejected_with_reason mismatch"


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
