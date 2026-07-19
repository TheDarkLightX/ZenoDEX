"""Local lifecycle coverage for tools-only perps oracle evidence."""

from __future__ import annotations

from typing import Mapping

import pytest

from tools.zenoctl_testnet_local import lifecycle as lc
from tools.zenoctl_testnet_local.perps_oracle_bridge import (
    build_local_settle_epoch_bridge,
)
from tools.zenodex_oracle_aggregate_adapter import verify_aggregate_adapter_bridge


def _market_summary() -> dict[str, object]:
    return {
        "market_id": "perp:ch2p:localtest-zusd-perps-v1",
        "kind": "clearinghouse_2p_v1",
        "quote_asset": "0x" + ("ab" * 32),
        "account_a_pubkey": "0x" + ("11" * 48),
        "account_b_pubkey": "0x" + ("22" * 48),
        "now_epoch": 1,
        "clearing_price_epoch": 1,
        "clearing_price_e8": 100_000_000,
        "index_price_e8": 100_000_000,
        "oracle_last_update_epoch": 0,
    }


def test_local_perps_settle_bridge_binds_live_market_snapshot() -> None:
    market = _market_summary()
    bridge = build_local_settle_epoch_bridge(
        chain_id="zeno-ledger-localtest-v0",
        market=market,
    )
    changed_bridge = build_local_settle_epoch_bridge(
        chain_id="zeno-ledger-localtest-v0",
        market={**market, "clearing_price_e8": 100_000_001},
    )

    result = verify_aggregate_adapter_bridge(bridge)
    assert result.status == "accepted"
    assert result.consumer_module == "zenodex.perps"
    assert result.action_kind == "settle_epoch"
    assert bridge["action"]["action_id"] != changed_bridge["action"]["action_id"]


def test_perps_wallet_cycle_builds_oracle_bridge_without_fixture_http_route(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    market = {
        **_market_summary(),
        "quote_asset": "quote",
        "account_a_pubkey": "alice",
        "account_b_pubkey": "bob",
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
    }
    status_payload = {
        "ok": True,
        "status": {
            "chain_id": "zeno-ledger-localtest-v0",
            "markets": [market],
        },
    }
    posted_paths: list[str] = []
    bridge_inputs: list[tuple[str, Mapping[str, object]]] = []

    def fake_safe_get_json(url: str, *, timeout_s: float = 5.0) -> dict[str, object]:
        assert url.endswith("/api/perps/wallet/status")
        return status_payload

    def fake_build_bridge(*, chain_id: str, market: Mapping[str, object]) -> dict[str, object]:
        bridge_inputs.append((chain_id, market))
        return {"schema": "local-test-bridge", "bridge_id": "sha256:" + ("1" * 64)}

    def fake_post_json(
        url: str,
        payload: Mapping[str, object],
        *,
        timeout_s: float = 10.0,
    ) -> dict[str, object]:
        path = "/" + url.split("/", 3)[3]
        posted_paths.append(path)
        if path == "/api/perps/wallet/prepare":
            return {"status_code": 200, "ok": True}
        assert path == "/api/perps/wallet/submit"
        if payload.get("action") == "settle_epoch":
            assert payload.get("oracle_adapter_bridge") == {
                "schema": "local-test-bridge",
                "bridge_id": "sha256:" + ("1" * 64),
            }
        return {
            "status_code": 200,
            "ok": True,
            "submission": {"sendtx_response": "SUCCESS: tx accepted"},
            "report": {"action": payload.get("action"), "preflight": {"ok": True}},
        }

    monkeypatch.setattr(lc, "_safe_get_json", fake_safe_get_json)
    monkeypatch.setattr(lc, "_post_json", fake_post_json)
    monkeypatch.setattr(lc, "build_local_settle_epoch_bridge", fake_build_bridge)
    monkeypatch.setattr(
        lc,
        "_local_sign_prepared_perps_wallet_payload",
        lambda *, request, prepared, roles: {**request, "signed_tau_tx_payload": {"fixture": True}},
    )

    result = lc._run_perps_wallet_cycle_smoke(
        ui_base="http://127.0.0.1:19108",
        market_id=str(market["market_id"]),
        roles={
            "operator": {"privkey_int": 17, "public_key": "operator"},
            "oracle_authority": {"privkey_int": 19, "public_key": "oracle"},
        },
        deadline=123,
    )

    assert result["ok"] is True
    assert posted_paths == [
        "/api/perps/wallet/prepare",
        "/api/perps/wallet/submit",
        "/api/perps/wallet/prepare",
        "/api/perps/wallet/submit",
        "/api/perps/wallet/prepare",
        "/api/perps/wallet/submit",
    ]
    assert bridge_inputs == [("zeno-ledger-localtest-v0", market)]
