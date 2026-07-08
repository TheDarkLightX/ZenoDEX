"""Tests for src/integration/perps_api.py — perps REST API handlers.

All tests call ``handle_perps_request()`` directly (no HTTP server needed).
"""

from __future__ import annotations

import json

import pytest

from src.integration.perps_api import handle_perps_request, reset_demo_state


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def _reset_state():
    """Reset demo state before each test so tests are independent."""
    reset_demo_state()
    yield
    reset_demo_state()


def _post(path: str, body: dict) -> tuple[int, dict]:
    raw = json.dumps(body).encode("utf-8")
    return handle_perps_request("POST", path, raw)


# ---------------------------------------------------------------------------
# GET /api/perps/markets
# ---------------------------------------------------------------------------

class TestListMarkets:
    def test_returns_three_markets(self):
        status, body = handle_perps_request("GET", "/api/perps/markets", None)
        assert status == 200
        assert body["ok"] is True
        ids = {m["id"] for m in body["markets"]}
        assert ids == {"BTC-USD", "ETH-USD", "TAU-USD"}

    def test_market_summary_fields(self):
        status, body = handle_perps_request("GET", "/api/perps/markets", None)
        assert status == 200
        for m in body["markets"]:
            assert "indexPriceE8" in m
            assert "fundingRateBps" in m
            assert "epochPhase" in m
            assert "nowEpoch" in m

    def test_market_summary_includes_guard_fields(self):
        """Summary must include guard/math fields so UI fallback path works."""
        status, body = handle_perps_request("GET", "/api/perps/markets", None)
        assert status == 200
        checked = 0
        for m in body["markets"]:
            if not str(m.get("kind", "")).startswith("isolated"):
                continue
            checked += 1
            for field in ("initialMarginBps", "maintenanceMarginBps",
                          "depegBufferBps", "maxPositionAbs", "oracleSeen",
                          "oracleLastUpdateEpoch", "maxOracleStalenessEpochs",
                          "maxOracleMoveBps", "liquidationPenaltyBps",
                          "fundingCapBps"):
                assert field in m, f"Missing {field} in market summary for {m['id']}"
        assert checked > 0, "No isolated markets found to validate"


# ---------------------------------------------------------------------------
# GET /api/perps/markets/{id}
# ---------------------------------------------------------------------------

class TestGetMarket:
    def test_btc_found(self):
        status, body = handle_perps_request("GET", "/api/perps/markets/BTC-USD", None)
        assert status == 200
        assert body["ok"] is True
        market = body["market"]
        assert market["id"] == "BTC-USD"
        assert market["indexPriceE8"] == 4_200_000_000_000
        assert "initialMarginBps" in market
        assert "maintenanceMarginBps" in market

    def test_not_found(self):
        status, body = handle_perps_request("GET", "/api/perps/markets/DOGE-USD", None)
        assert status == 404
        assert body["error"] == "market_not_found"


# ---------------------------------------------------------------------------
# GET /api/perps/markets/{id}/positions/{pubkey}
# ---------------------------------------------------------------------------

class TestGetPosition:
    def test_default_empty_position(self):
        status, body = handle_perps_request(
            "GET", "/api/perps/markets/BTC-USD/positions/alice", None
        )
        assert status == 200
        assert body["ok"] is True
        pos = body["position"]
        assert pos["marketId"] == "BTC-USD"
        assert pos["pubkey"] == "alice"
        assert pos["positionBase"] == 0
        assert pos["collateralQuote"] == 0

    def test_market_not_found(self):
        status, body = handle_perps_request(
            "GET", "/api/perps/markets/DOGE-USD/positions/alice", None
        )
        assert status == 404

    def test_position_after_deposit(self):
        # Deposit first
        _post("/api/perps/collateral", {
            "marketId": "ETH-USD", "pubkey": "bob", "action": "deposit", "amount": 50000,
        })
        # Query position
        status, body = handle_perps_request(
            "GET", "/api/perps/markets/ETH-USD/positions/bob", None
        )
        assert status == 200
        assert body["position"]["collateralQuote"] == 50000


# ---------------------------------------------------------------------------
# GET /api/perps/positions/{pubkey}
# ---------------------------------------------------------------------------

class TestGetPositions:
    def test_positions_for_all_markets(self):
        status, body = handle_perps_request("GET", "/api/perps/positions/alice", None)
        assert status == 200
        assert body["ok"] is True
        positions = body["positions"]
        assert set(positions.keys()) == {"BTC-USD", "ETH-USD", "TAU-USD"}
        for market_id, pos in positions.items():
            assert pos["marketId"] == market_id
            assert pos["pubkey"] == "alice"

    def test_invalid_pubkey(self):
        status, body = handle_perps_request("GET", "/api/perps/positions/a b", None)
        assert status == 400
        assert body["ok"] is False
        assert body["error"] == "invalid_pubkey"


# ---------------------------------------------------------------------------
# POST /api/perps/collateral
# ---------------------------------------------------------------------------

class TestPostCollateral:
    def test_deposit(self):
        status, body = _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 10000,
        })
        assert status == 200
        assert body["ok"] is True
        assert body["position"]["collateralQuote"] == 10000

    def test_withdraw_after_deposit(self):
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 10000,
        })
        status, body = _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "withdraw", "amount": 3000,
        })
        assert status == 200
        assert body["position"]["collateralQuote"] == 7000

    def test_withdraw_overdraw_rejected(self):
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 1000,
        })
        status, body = _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "withdraw", "amount": 2000,
        })
        assert status == 400
        assert body["error"] == "guard_rejected"

    def test_missing_marketId(self):
        status, body = _post("/api/perps/collateral", {
            "pubkey": "alice", "action": "deposit", "amount": 1000,
        })
        assert status == 400
        assert body["error"] == "missing_marketId"

    def test_invalid_action(self):
        status, body = _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "burn", "amount": 1000,
        })
        assert status == 400
        assert body["error"] == "invalid_action"

    def test_invalid_amount(self):
        status, body = _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 0,
        })
        assert status == 400
        assert body["error"] == "invalid_amount"

    def test_market_not_found(self):
        status, body = _post("/api/perps/collateral", {
            "marketId": "DOGE-USD", "pubkey": "alice", "action": "deposit", "amount": 1000,
        })
        assert status == 404
        assert body["error"] == "market_not_found"


# ---------------------------------------------------------------------------
# POST /api/perps/position
# ---------------------------------------------------------------------------

class TestPostPosition:
    def test_open_position_with_collateral(self):
        # Deposit collateral first (initial_margin_bps=1000 for BTC-USD)
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit",
            "amount": 500_000_000_000,
        })
        # Open a small position
        status, body = _post("/api/perps/position", {
            "marketId": "BTC-USD", "pubkey": "alice", "newPositionBase": 10,
        })
        assert status == 200
        assert body["ok"] is True
        assert body["position"]["positionBase"] == 10

    def test_close_position(self):
        # Deposit and open
        _post("/api/perps/collateral", {
            "marketId": "ETH-USD", "pubkey": "alice", "action": "deposit",
            "amount": 500_000_000_000,
        })
        _post("/api/perps/position", {
            "marketId": "ETH-USD", "pubkey": "alice", "newPositionBase": 100,
        })
        # Close
        status, body = _post("/api/perps/position", {
            "marketId": "ETH-USD", "pubkey": "alice", "newPositionBase": 0,
        })
        assert status == 200
        assert body["position"]["positionBase"] == 0

    def test_insufficient_margin_rejected(self):
        # No collateral deposited
        status, body = _post("/api/perps/position", {
            "marketId": "BTC-USD", "pubkey": "alice", "newPositionBase": 100,
        })
        assert status == 400
        assert body["error"] == "guard_rejected"

    def test_missing_fields(self):
        status, body = _post("/api/perps/position", {"marketId": "BTC-USD"})
        assert status == 400

    def test_position_computed_fields(self):
        # Deposit just enough collateral for ~10x leverage on ETH-USD
        # ETH at 320_000_000_000 e8 = $3200, position of 1000 base units
        # notional = 1000 * 320_000_000_000 / 1e8 = 3_200_000
        # 10% initial margin -> need 320_000 collateral minimum
        # Use 400_000 so leverage is ~8x (3_200_000 * 100 / 400_000 = 800)
        _post("/api/perps/collateral", {
            "marketId": "ETH-USD", "pubkey": "charlie", "action": "deposit",
            "amount": 400_000,
        })
        status, body = _post("/api/perps/position", {
            "marketId": "ETH-USD", "pubkey": "charlie", "newPositionBase": 1000,
        })
        assert status == 200
        pos = body["position"]
        assert pos["notionalQuote"] > 0
        assert pos["liquidationPriceE8"] is not None
        assert pos["leverageX100"] > 0


# ---------------------------------------------------------------------------
# GET /api/perps/history/{pubkey}
# ---------------------------------------------------------------------------

class TestGetHistory:
    def test_empty_history(self):
        status, body = handle_perps_request("GET", "/api/perps/history/alice", None)
        assert status == 200
        assert body["ok"] is True
        assert body["history"] == []

    def test_history_after_operations(self):
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 5000,
        })
        status, body = handle_perps_request("GET", "/api/perps/history/alice", None)
        assert status == 200
        assert len(body["history"]) == 1
        assert body["history"][0]["action"] == "deposit"
        assert body["history"][0]["marketId"] == "BTC-USD"

    def test_history_action_strings_for_all_operations(self):
        """History records correct action strings for deposit, set_position, deposit_insurance."""
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 500_000,
        })
        _post("/api/perps/position", {
            "marketId": "BTC-USD", "pubkey": "alice", "newPositionBase": 1,
        })
        _post("/api/perps/insurance", {
            "marketId": "BTC-USD", "pubkey": "alice", "amount": 1000,
        })
        status, body = handle_perps_request("GET", "/api/perps/history/alice", None)
        assert status == 200
        actions = [h["action"] for h in body["history"]]
        # Newest first: deposit_insurance, set_position, deposit
        assert actions == ["deposit_insurance", "set_position", "deposit"]

    def test_history_filtered_by_pubkey(self):
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 5000,
        })
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "bob", "action": "deposit", "amount": 3000,
        })
        status, body = handle_perps_request("GET", "/api/perps/history/bob", None)
        assert status == 200
        assert len(body["history"]) == 1
        assert body["history"][0]["pubkey"] == "bob"

    def test_history_newest_first(self):
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 100,
        })
        _post("/api/perps/collateral", {
            "marketId": "BTC-USD", "pubkey": "alice", "action": "deposit", "amount": 200,
        })
        status, body = handle_perps_request("GET", "/api/perps/history/alice", None)
        assert status == 200
        assert len(body["history"]) == 2
        # Newest entry first
        assert body["history"][0]["detail"]["amount"] == 200
        assert body["history"][1]["detail"]["amount"] == 100


# ---------------------------------------------------------------------------
# POST /api/perps/insurance
# ---------------------------------------------------------------------------

class TestPostInsurance:
    def test_deposit(self):
        status, body = _post("/api/perps/insurance", {
            "marketId": "BTC-USD", "pubkey": "alice", "amount": 1_000_000,
        })
        assert status == 200
        assert body["ok"] is True
        market = body["market"]
        # Initial insurance was 4_000_000_000, now +1_000_000
        assert market["initialInsurance"] == 4_000_000_000 + 1_000_000
        assert market["insuranceBalance"] == 5_000_000_000 + 1_000_000

    def test_missing_market(self):
        status, body = _post("/api/perps/insurance", {
            "marketId": "DOGE-USD", "pubkey": "alice", "amount": 1000,
        })
        assert status == 404

    def test_missing_pubkey(self):
        status, body = _post("/api/perps/insurance", {
            "marketId": "BTC-USD", "amount": 1000,
        })
        assert status == 400
        assert body["error"] == "missing_pubkey"

    def test_invalid_amount(self):
        status, body = _post("/api/perps/insurance", {
            "marketId": "BTC-USD", "pubkey": "alice", "amount": -1,
        })
        assert status == 400
        assert body["error"] == "invalid_amount"


# ---------------------------------------------------------------------------
# 404 for unknown routes
# ---------------------------------------------------------------------------

class TestRouting:
    def test_unknown_get(self):
        status, body = handle_perps_request("GET", "/api/perps/unknown", None)
        assert status == 404
        assert body["error"] == "not_found"

    def test_unknown_post(self):
        status, body = _post("/api/perps/unknown", {"foo": "bar"})
        assert status == 404

    def test_unknown_post_no_body(self):
        """Unknown POST route returns 404 even without a body."""
        status, body = handle_perps_request("POST", "/api/perps/unknown", None)
        assert status == 404
        assert body["error"] == "not_found"

    def test_wrong_prefix(self):
        status, body = handle_perps_request("GET", "/api/other/markets", None)
        assert status == 404

    def test_empty_post_body(self):
        status, body = handle_perps_request("POST", "/api/perps/collateral", None)
        assert status == 400
        assert body["error"] == "empty_body"

    def test_invalid_json_body(self):
        status, body = handle_perps_request("POST", "/api/perps/collateral", b"not json")
        assert status == 400
        assert body["error"] == "invalid_json"

    def test_method_not_allowed(self):
        status, body = handle_perps_request("DELETE", "/api/perps/markets", None)
        assert status == 405

    def test_internal_errors_are_fail_closed(self):
        """Unexpected internal exceptions must return a stable 500 response."""
        import src.integration.perps_api as perps_api

        # Corrupt demo state in-place to force an internal exception during response build.
        perps_api._demo_perps.markets["BTC-USD"].global_state["epoch_phase"] = "InvalidPhase"
        status, body = perps_api.handle_perps_request("GET", "/api/perps/markets", None)
        assert status == 500
        assert body["ok"] is False
        assert body["error"] == "internal_error"


# ---------------------------------------------------------------------------
# API server env gate
# ---------------------------------------------------------------------------

class TestApiServerPerpsGate:
    def test_perps_api_gated_off_returns_404(self):
        """When perps_api_enabled is False, GET /api/perps/markets returns 404."""
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = False

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/markets"
        h.headers = {}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 404, f"Expected 404 when gate off, got {captured['status']}"
        assert captured["obj"]["error"] == "not_found"

    def test_perps_api_gated_on_returns_200(self):
        """When perps_api_enabled is True, GET /api/perps/markets returns 200."""
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/markets"
        h.headers = {}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 200, f"Expected 200 when gate on, got {captured['status']}"
        assert captured["obj"]["ok"] is True
        assert "markets" in captured["obj"]

    def test_perps_api_gated_on_without_unsafe_demo_flag_returns_404(self):
        """When only PERPS_API_ENABLED is true, demo perps routes stay unserved."""
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = False
            api_host = "127.0.0.1"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/markets"
        h.headers = {}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 404, f"Expected 404 without unsafe demo gate, got {captured['status']}"
        assert captured["obj"]["error"] == "not_found"

    def test_perps_api_unsafe_demo_flag_rejects_non_loopback_client(self):
        """Unsafe demo perps routes still require loopback client and bind host."""
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("203.0.113.10", 12345)
        h.path = "/api/perps/markets"
        h.headers = {}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        h._write_json = types.MethodType(fake_write_json, h)

        h.do_GET()
        assert captured["status"] == 404, f"Expected 404 for non-loopback demo caller, got {captured['status']}"
        assert captured["obj"]["error"] == "not_found"

    def test_perps_post_gated_off_returns_404(self):
        """When perps_api_enabled is False, POST /api/perps/collateral returns 404."""
        import json as _json
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = False

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/collateral"
        h.headers = {"Content-Length": "2"}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return _json.dumps({
                "marketId": "BTC-USD", "pubkey": "a", "action": "deposit", "amount": 1,
            }).encode(), None
        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 404, f"Expected 404 when gate off, got {captured['status']}"

    def test_perps_post_gated_on_returns_200(self):
        """When perps_api_enabled is True, POST /api/perps/collateral returns 200."""
        import json as _json
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/collateral"
        h.headers = {"Content-Length": "2"}

        captured = {}
        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj
        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return _json.dumps({
                "marketId": "BTC-USD", "pubkey": "a", "action": "deposit", "amount": 1,
            }).encode(), None
        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 200, f"Expected 200 when gate on, got {captured['status']}"
        assert captured["obj"]["ok"] is True

    def test_perps_api_token_required_returns_401(self):
        """When demo_api_token is set, perps routes must require Authorization."""
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/markets"
        h.headers = {}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)
        h.do_GET()
        assert captured["status"] == 401
        assert captured["obj"]["error"] == "unauthorized"

    def test_perps_api_token_allows_valid_bearer(self):
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/markets"
        h.headers = {"Authorization": "Bearer sekret"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        h._write_json = types.MethodType(fake_write_json, h)
        h.do_GET()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True

    def test_perps_post_token_required_returns_401(self):
        import json as _json
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/collateral"
        h.headers = {"Content-Length": "2"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return _json.dumps({
                "marketId": "BTC-USD", "pubkey": "a", "action": "deposit", "amount": 1,
            }).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 401
        assert captured["obj"]["error"] == "unauthorized"

    def test_perps_post_token_allows_valid_bearer(self):
        import json as _json
        import types
        from src.integration.api_server import _Handler

        class _FakeLimiter:
            def allow(self, key):
                return True

        class _FakeServer:
            cors_origins = set()
            rate_limiter = _FakeLimiter()
            perps_api_enabled = True
            perps_demo_api_unsafe_enabled = True
            api_host = "127.0.0.1"
            demo_api_token = "sekret"

        h = object.__new__(_Handler)
        h.server = _FakeServer()
        h.client_address = ("127.0.0.1", 12345)
        h.path = "/api/perps/collateral"
        h.headers = {"Content-Length": "2", "Authorization": "Bearer sekret"}

        captured = {}

        def fake_write_json(self, status, obj, *, cors_origin):
            captured["status"] = status
            captured["obj"] = obj

        def fake_read_raw_body_with_error(self, max_bytes=65536):
            return _json.dumps({
                "marketId": "BTC-USD", "pubkey": "a", "action": "deposit", "amount": 1,
            }).encode(), None

        h._write_json = types.MethodType(fake_write_json, h)
        h._read_raw_body_with_error = types.MethodType(fake_read_raw_body_with_error, h)

        h.do_POST()
        assert captured["status"] == 200
        assert captured["obj"]["ok"] is True
