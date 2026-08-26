from __future__ import annotations

import json
import threading
from http.client import HTTPConnection


def _start_test_server(*, dex_enabled: bool = True):
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = bool(dex_enabled)  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]
    httpd.external_auth_enforced = True  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _locally_sign_settlement_price_packet(packet: dict[str, object]) -> dict[str, object]:
    from src.integration.settlement_price_attestation import (
        SettlementSpotPricePacket,
        build_settlement_spot_price_attestation,
    )

    return build_settlement_spot_price_attestation(
        packet=SettlementSpotPricePacket.from_dict(packet),
        signer_privkey=7,
    ).to_dict()


def _pool_dict(
    *,
    pid: str,
    a0: str,
    a1: str,
    r0: int,
    r1: int,
    fee_bps: int = 0,
    curve_tag: str = "CPMM",
    curve_params: object = "",
) -> dict:
    asset0 = min(a0, a1)
    asset1 = max(a0, a1)
    reserve0 = r0 if a0 < a1 else r1
    reserve1 = r1 if a0 < a1 else r0
    return {
        "pool_id": pid,
        "asset0": asset0,
        "asset1": asset1,
        "reserve0": int(reserve0),
        "reserve1": int(reserve1),
        "fee_bps": int(fee_bps),
        "lp_supply": 1,
        "status": "ACTIVE",
        "created_at": 0,
        "curve_tag": curve_tag,
        "curve_params": curve_params,
    }


def _spot_settlement_request() -> tuple[dict, dict[str, int]]:
    from src.core.batch_clearing import compute_settlement
    from src.core.liquidity import create_pool
    from src.integration.operations import create_settlement_operation
    from src.state import BalanceTable, LPTable
    from src.state.intents import Intent, IntentKind

    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + f"{2200:064x}",
        sender_pubkey=pk,
        deadline=9_999_999_999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    settlement_dict = create_settlement_operation(settlement)["3"]
    prices = {asset0: 100, asset1: 120}
    return settlement_dict, prices


def _spot_settlement_request_with_pool() -> tuple[dict, dict[str, int], dict]:
    from src.core.batch_clearing import compute_settlement
    from src.core.liquidity import create_pool
    from src.core.settlement import LPDelta
    from src.integration.operations import create_settlement_operation
    from src.state import BalanceTable, LPTable
    from src.state.intents import Intent, IntentKind

    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + f"{3300:064x}",
        sender_pubkey=pk,
        deadline=9_999_999_999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    settlement.lp_deltas.append(LPDelta(pubkey=pk, pool_id=pool_id, delta_add=3, delta_sub=0))
    settlement_dict = create_settlement_operation(settlement)["3"]
    prices = {asset0: 100, asset1: 120}
    pool_snapshot = {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": pool.reserve0,
        "reserve1": pool.reserve1,
        "fee_bps": pool.fee_bps,
        "lp_supply": pool.lp_supply,
        "status": pool.status.name,
        "created_at": pool.created_at,
        "curve_tag": pool.curve_tag,
        "curve_params": pool.curve_params,
    }
    return settlement_dict, prices, pool_snapshot


def _four_swap_settlement_request() -> tuple[dict, dict[str, int]]:
    from src.core.batch_clearing import compute_settlement
    from src.core.liquidity import create_pool
    from src.integration.operations import create_settlement_operation
    from src.state import BalanceTable, LPTable
    from src.state.intents import Intent, IntentKind

    pk = "0x" + "33" * 48
    asset0 = "0x" + "05" * 32
    asset1 = "0x" + "06" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 100_000)
    balances.set(pk, asset1, 0)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + f"{idx + 1:064x}",
            sender_pubkey=pk,
            deadline=9_999_999_999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        )
        for idx in range(4)
    ]
    settlement = compute_settlement(intents, {pool_id: pool}, balances, LPTable())
    settlement_dict = create_settlement_operation(settlement)["3"]
    prices = {asset0: 100, asset1: 120}
    return settlement_dict, prices


def _four_swap_settlement_request_with_pool() -> tuple[dict, dict[str, int], dict]:
    from src.core.batch_clearing import compute_settlement
    from src.core.liquidity import create_pool
    from src.core.settlement import LPDelta
    from src.integration.operations import create_settlement_operation
    from src.state import BalanceTable, LPTable
    from src.state.intents import Intent, IntentKind

    pk = "0x" + "44" * 48
    asset0 = "0x" + "07" * 32
    asset1 = "0x" + "08" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 100_000)
    balances.set(pk, asset1, 0)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + f"{idx + 1:064x}",
            sender_pubkey=pk,
            deadline=9_999_999_999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        )
        for idx in range(4)
    ]
    settlement = compute_settlement(intents, {pool_id: pool}, balances, LPTable())
    settlement.lp_deltas = [LPDelta(pubkey=pk, pool_id=pool_id, delta_add=2, delta_sub=0)]
    settlement_dict = create_settlement_operation(settlement)["3"]
    prices = {asset0: 100, asset1: 120}
    pool_snapshot = {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": pool.reserve0,
        "reserve1": pool.reserve1,
        "fee_bps": pool.fee_bps,
        "lp_supply": pool.lp_supply,
        "status": pool.status.name,
        "created_at": pool.created_at,
        "curve_tag": pool.curve_tag,
        "curve_params": str(pool.curve_params),
    }
    return settlement_dict, prices, pool_snapshot


def _feature_extension_inputs_payload() -> dict[str, int]:
    return {
        "trade_amount": 100,
        "fee_charged": 1,
        "buyback_amount": 1,
        "burned_amount": 1,
        "supply_before": 1000,
        "supply_after": 999,
        "supply_floor": 500,
        "unit_scale": 1,
        "rebate_rate_bps": 500,
        "rebate_amount": 1,
        "rebate_cap": 1,
        "lock_days": 60,
        "stake_amount": 50,
        "tier1_days": 30,
        "tier2_days": 90,
        "weight_t1": 1,
        "weight_t2": 2,
        "weight_t3": 3,
        "weight_claimed": 2,
        "weighted_stake": 100,
    }


def _settlement_witness_lifecycle_request(
    *,
    block_timestamp: int = 0,
    deadline: int = 9_999_999_999,
    price_history: list[int] | None = None,
) -> tuple[dict, str]:
    from src.core.batch_clearing import compute_settlement
    from src.core.liquidity import create_pool
    from src.integration.operations import create_intent_operation, create_settlement_operation
    from src.integration.settlement_price_provenance import (
        SettlementSpotPriceEntry,
        build_settlement_spot_price_packet,
    )
    from src.state import BalanceTable, LPTable
    from src.state.intents import Intent, IntentKind

    pk = "0x" + "22" * 48
    asset0 = "0x" + "03" * 32
    asset1 = "0x" + "04" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 100_000)
    balances.set(pk, asset1, 0)
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + f"{idx + 1:064x}",
            sender_pubkey=pk,
            deadline=deadline,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        )
        for idx in range(4)
    ]
    settlement = compute_settlement(intents, {pool_id: pool}, balances, LPTable())
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    request = {
        "intents": create_intent_operation(intents)["2"],
        "balances": [
            {"pubkey": pk, "asset": asset0, "amount": 100_000},
        ],
        "pools": [
            {
                "pool_id": pool.pool_id,
                "asset0": pool.asset0,
                "asset1": pool.asset1,
                "reserve0": pool.reserve0,
                "reserve1": pool.reserve1,
                "fee_bps": pool.fee_bps,
                "lp_supply": pool.lp_supply,
                "status": pool.status.name,
                "created_at": pool.created_at,
                "curve_tag": pool.curve_tag,
                "curve_params": str(pool.curve_params),
            }
        ],
        "lp_balances": [],
        "block_timestamp": int(block_timestamp),
        "settlement": create_settlement_operation(settlement)["3"],
        "proof_flags": {
            "cpmm_ok": 1,
            "balance_ok": 1,
            "token_ok": 1,
            "buyback_floor_ok": 1,
            "buyback_floor_fixedpoint_ok": 1,
            "rebate_ok": 1,
            "lock_weight_ok": 1,
            "proof_ok": 1,
            "binding_ok": 1,
        },
        "price_history": list(price_history or [100, 110, 120]),
        "feature_extension_inputs": _feature_extension_inputs_payload(),
        "price_packet": price_packet.to_dict(),
    }
    return request, intents[0].intent_id


def test_api_server_dex_quote_and_verify_receipt_roundtrip() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p1", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        req = {
            "kind": "exact_out",
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 600,
            "apply_two_hop_gate": False,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["kind"] == "exact_out"
        assert "receipt" in body
        receipt = body["receipt"]
        assert isinstance(receipt, dict)
        assert isinstance(receipt.get("receipt_hash"), str) and receipt["receipt_hash"]

        # Verify via API.
        req2 = {"receipt": receipt, "pools": pools}
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_quote_receipt",
            body=json.dumps(req2).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] == "ok"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_dex_quote_exact_out_fast_v1_roundtrip() -> None:
    import pytest

    pytest.importorskip("numpy")
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p1", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        req = {
            "kind": "exact_out",
            "routing_mode": "fast_v1",
            "fast_topk_max": 32,
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 600,
            "apply_two_hop_gate": False,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["kind"] == "exact_out"
        assert body["routing_mode"] == "fast_v1"
        assert "receipt" in body
        receipt = body["receipt"]
        assert isinstance(receipt, dict)
        assert isinstance(receipt.get("receipt_hash"), str) and receipt["receipt_hash"]

        # Verify via API.
        req2 = {"receipt": receipt, "pools": pools}
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_quote_receipt",
            body=json.dumps(req2).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] == "ok"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_in_route_oracle_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_in_route_oracle_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_schema"] == "zenodex/exact-in-route-oracle-contract/v1"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_in_route_oracle_contract"
        contract = body["contract"]
        assert contract["runtime_matches_canonical"] is True
        assert contract["runtime_quote"] == contract["canonical_winner_quote"]
        assert contract["candidate_count"] >= 1

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_in_route_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_in_route_oracle_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_in_route_oracle_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = dict(body["contract"])
        contract["runtime_matches_canonical"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_in_route_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "oracle contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_guard_exact_in_route_canonicality() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/guard_exact_in_route_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["error"] is None
        assert body["contract"]["runtime_matches_canonical"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_in_route_guarded() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_in_route_guarded",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["error"] is None
        assert body["quote"] == body["contract"]["runtime_quote"]
        assert body["contract"]["runtime_matches_canonical"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_in_route_guarded_quote_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_in_route_guarded_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == "zenodex/exact-in-route-guarded-quote-packet/v1"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_in_route_guarded_quote_packet"
        assert packet["guard_ok"] is True
        assert packet["quote"] == packet["contract"]["runtime_quote"]
        assert packet["error"] is None

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_in_route_guarded_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None

        packet["guard_ok"] = False
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_exact_in_route_guarded_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is False
        assert body3["error"] == "guarded quote packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_in_route_rank_projection_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_in_route_rank_projection_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["packet_schema"] == "zenodex/exact-in-route-rank-projection-packet/v1"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_in_route_rank_projection_packet"
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["ordered_unique_keys_sorted_unique"] is True
        assert packet["candidate_ranks_match_projection"] is True
        assert packet["rank_order_preserves_true_key_order"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_in_route_rank_projection_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None

        packet["rank_order_preserves_true_key_order"] = False
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_exact_in_route_rank_projection_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is False
        assert body3["error"] == "rank projection packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_in_route_true_key_interpretation_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p_ab", a0="A", a1="B", r0=1000, r1=1001, fee_bps=0),
            _pool_dict(pid="p_ac", a0="A", a1="C", r0=1000, r1=1000, fee_bps=0),
            _pool_dict(pid="p_cb", a0="C", a1="B", r0=1000, r1=1000, fee_bps=0),
        ]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_in_route_true_key_interpretation_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_in": 10,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["packet_schema"] == "zenodex/exact-in-route-true-key-interpretation-packet/v1"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_in_route_true_key_interpretation_packet"
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["winner_index_in_range"] is True
        assert packet["candidate_indices_match_stream"] is True
        assert packet["candidate_route_keys_match_quotes"] is True
        assert packet["winner_matches_certificate_candidate"] is True
        assert packet["winner_true_key_minimal"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None

        packet["winner_true_key_minimal"] = False
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_exact_in_route_true_key_interpretation_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is False
        assert body3["error"] == "true-key interpretation packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_spot_value_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, asset_prices = _spot_settlement_request()

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["schema"] == "zenodex/settlement-spot-value-contract/v1"
        assert contract["asset_conservation_ok"] is True
        assert contract["value_conservation_ok"] is True
        assert contract["net_value_sum"] == 0

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                    "contract": contract,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_settlement_spot_value_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, asset_prices = _spot_settlement_request()

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = dict(body["contract"])
        contract["net_value_sum"] = 1

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                    "contract": contract,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "settlement spot value contract mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_spot_price_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(
                {
                    "entries": [
                        {"asset": "A", "price": 100, "observed_epoch": 95, "age_epochs": 5, "source_id": "local:a"},
                        {"asset": "B", "price": 120, "observed_epoch": 97, "age_epochs": 3, "source_id": "local:b"},
                    ],
                    "now_epoch": 100,
                    "max_staleness_epochs": 10,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["provenance_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_spot_price_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_settlement_spot_value_contract_from_price_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices = _spot_settlement_request()
        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "local:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "local:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "price_packet": price_packet,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["schema"] == "zenodex/settlement-spot-value-contract/v1"
        assert contract["value_conservation_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_spot_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "price_packet": price_packet,
                    "contract": contract,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_spot_price_attestation() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "05" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "06" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }
        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        packet = body0["packet"]

        attestation = _locally_sign_settlement_price_packet(packet)

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_spot_price_attestation",
            body=json.dumps(
                {
                    "attestation": attestation,
                    "consumer_now_epoch": 103,
                    "max_attestation_age_epochs": 5,
                    "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_settlement_spot_value_contract_from_price_attestation() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices = _spot_settlement_request()
        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        packet = body0["packet"]

        attestation = _locally_sign_settlement_price_packet(packet)

        req = {
            "settlement": settlement,
            "price_attestation": attestation,
            "consumer_now_epoch": 103,
            "max_attestation_age_epochs": 5,
            "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
        }
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/build_settlement_spot_value_contract",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        contract = body2["contract"]
        assert contract["schema"] == "zenodex/settlement-spot-value-contract/v1"
        assert contract["value_conservation_ok"] is True

        verify_req = dict(req)
        verify_req["contract"] = contract
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_settlement_spot_value_contract",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is True
        assert body3["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_lp_value_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, asset_prices = _spot_settlement_request()
        settlement["lp_deltas"] = [
            {
                "pubkey": settlement["balance_deltas"][0]["pubkey"],
                "pool_id": settlement["reserve_deltas"][0]["pool_id"],
                "delta_add": 5,
                "delta_sub": 0,
            }
        ]
        lp_unit_values = {settlement["reserve_deltas"][0]["pool_id"]: 77}

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_lp_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                    "lp_unit_values": lp_unit_values,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["lp_user_value_sum"] == 5 * 77
        assert contract["lp_protocol_liability_value_sum"] == -(5 * 77)
        assert contract["value_conservation_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_lp_value_contract",
            body=json.dumps(
                {
                    "settlement": settlement,
                    "asset_prices": asset_prices,
                    "lp_unit_values": lp_unit_values,
                    "contract": contract,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_settlement_lp_value_contract_from_price_attestation() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices = _spot_settlement_request()
        settlement["lp_deltas"] = [
            {
                "pubkey": settlement["balance_deltas"][0]["pubkey"],
                "pool_id": settlement["reserve_deltas"][0]["pool_id"],
                "delta_add": 3,
                "delta_sub": 0,
            }
        ]
        pool_id = settlement["reserve_deltas"][0]["pool_id"]

        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        packet = body0["packet"]

        attestation = _locally_sign_settlement_price_packet(packet)

        req = {
            "settlement": settlement,
            "price_attestation": attestation,
            "consumer_now_epoch": 103,
            "max_attestation_age_epochs": 5,
            "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
            "lp_unit_values": {pool_id: 91},
        }
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/build_settlement_lp_value_contract",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        contract = body2["contract"]
        assert contract["lp_user_value_sum"] == 3 * 91
        assert contract["lp_protocol_liability_value_sum"] == -(3 * 91)
        assert contract["value_conservation_ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_value_packet_spot() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices = _spot_settlement_request()

        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_value_packet",
            body=json.dumps({"settlement": settlement, "price_packet": price_packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        assert body1["ok"] is True
        packet = body1["packet"]
        assert packet["mode"] == "spot_only"
        assert packet["packet_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_value_packet",
            body=json.dumps(
                {"settlement": settlement, "price_packet": price_packet, "packet": packet}
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_value_packet_lp_attested() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices = _spot_settlement_request()
        settlement["lp_deltas"] = [
            {
                "pubkey": settlement["balance_deltas"][0]["pubkey"],
                "pool_id": settlement["reserve_deltas"][0]["pool_id"],
                "delta_add": 3,
                "delta_sub": 0,
            }
        ]
        pool_id = settlement["reserve_deltas"][0]["pool_id"]

        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        attestation = _locally_sign_settlement_price_packet(price_packet)

        req = {
            "settlement": settlement,
            "price_attestation": attestation,
            "consumer_now_epoch": 103,
            "max_attestation_age_epochs": 5,
            "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
            "lp_unit_values": {pool_id: 91},
        }
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/build_settlement_value_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        packet = body2["packet"]
        assert packet["mode"] == "lp_aware"
        assert packet["packet_ok"] is True

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_settlement_value_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is True
        assert body3["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_endogenous_lp_value_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices, pool_snapshot = _spot_settlement_request_with_pool()
        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        req = {
            "settlement": settlement,
            "price_packet": price_packet,
            "pool_snapshots": [pool_snapshot],
        }
        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_endogenous_lp_value_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        assert body1["ok"] is True
        packet = body1["packet"]
        assert packet["price_input_kind"] == "packet"
        assert packet["packet_ok"] is True

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_endogenous_lp_value_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_endogenous_lp_value_packet_from_attestation() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, _asset_prices, pool_snapshot = _spot_settlement_request_with_pool()
        build_packet_req = {
            "entries": [
                {
                    "asset": "0x" + "01" * 32,
                    "price": 100,
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": "0x" + "02" * 32,
                    "price": 120,
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }
        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True

        attestation = _locally_sign_settlement_price_packet(body0["packet"])

        req = {
            "settlement": settlement,
            "price_attestation": attestation,
            "consumer_now_epoch": 103,
            "max_attestation_age_epochs": 5,
            "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
            "pool_snapshots": [pool_snapshot],
        }
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/build_settlement_endogenous_lp_value_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        packet = body2["packet"]
        assert packet["price_input_kind"] == "attestation"
        assert packet["packet_ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_end_to_end_certificate_packet_spot() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, asset_prices = _four_swap_settlement_request()
        assets = list(asset_prices.items())
        build_packet_req = {
            "entries": [
                {
                    "asset": assets[0][0],
                    "price": assets[0][1],
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": assets[1][0],
                    "price": assets[1][1],
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        req = {
            "settlement": settlement,
            "proof_flags": {
                "cpmm_ok": 1,
                "balance_ok": 1,
                "token_ok": 1,
                "buyback_floor_ok": 1,
                "buyback_floor_fixedpoint_ok": 1,
                "rebate_ok": 1,
                "lock_weight_ok": 1,
                "proof_ok": 1,
                "binding_ok": 1,
            },
            "price_history": [100, 110, 120],
            "feature_extension_inputs": _feature_extension_inputs_payload(),
            "price_packet": price_packet,
        }
        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_end_to_end_certificate_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        assert body1["ok"] is True
        packet = body1["packet"]
        assert packet["packet_ok"] is True
        assert packet["value_packet_kind"] == "declared_value"
        assert packet["full_price_rails_ok"] is True

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_end_to_end_certificate_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_end_to_end_certificate_packet_endogenous_attested() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        settlement, asset_prices, pool_snapshot = _four_swap_settlement_request_with_pool()
        assets = list(asset_prices.items())
        build_packet_req = {
            "entries": [
                {
                    "asset": assets[0][0],
                    "price": assets[0][1],
                    "observed_epoch": 95,
                    "age_epochs": 5,
                    "source_id": "oracle:a",
                },
                {
                    "asset": assets[1][0],
                    "price": assets[1][1],
                    "observed_epoch": 97,
                    "age_epochs": 3,
                    "source_id": "oracle:b",
                },
            ],
            "now_epoch": 100,
            "max_staleness_epochs": 10,
        }

        conn0 = HTTPConnection(host, port, timeout=2.0)
        conn0.request(
            "POST",
            "/api/dex/build_settlement_spot_price_packet",
            body=json.dumps(build_packet_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp0 = conn0.getresponse()
        body0 = json.loads(resp0.read().decode("utf-8"))
        assert resp0.status == 200
        assert body0["ok"] is True
        price_packet = body0["packet"]

        attestation = _locally_sign_settlement_price_packet(price_packet)

        req = {
            "settlement": settlement,
            "proof_flags": {
                "cpmm_ok": 1,
                "balance_ok": 1,
                "token_ok": 1,
                "buyback_floor_ok": 1,
                "buyback_floor_fixedpoint_ok": 1,
                "rebate_ok": 1,
                "lock_weight_ok": 1,
                "proof_ok": 1,
                "binding_ok": 1,
            },
            "price_history": [100, 110, 120],
            "feature_extension_inputs": _feature_extension_inputs_payload(),
            "price_attestation": attestation,
            "consumer_now_epoch": 103,
            "max_attestation_age_epochs": 5,
            "allowed_signers": {attestation["signer_pubkey"]: ["oracle:a", "oracle:b"]},
            "pool_snapshots": [pool_snapshot],
        }
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/build_settlement_end_to_end_certificate_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        packet = body2["packet"]
        assert packet["packet_ok"] is True
        assert packet["value_packet_kind"] == "endogenous_lp_value"
        assert packet["price_input_kind"] == "attestation"

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn3 = HTTPConnection(host, port, timeout=2.0)
        conn3.request(
            "POST",
            "/api/dex/verify_settlement_end_to_end_certificate_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp3 = conn3.getresponse()
        body3 = json.loads(resp3.read().decode("utf-8"))
        assert resp3.status == 200
        assert body3["ok"] is True
        assert body3["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_feature_extension_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req = {"feature_extension_inputs": _feature_extension_inputs_payload()}
        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_feature_extension_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        assert body1["ok"] is True
        packet = body1["packet"]
        assert packet["packet_ok"] is True
        assert packet["feature_extension_ok"] is True

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_feature_extension_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_settlement_witness_lifecycle_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req, _ = _settlement_witness_lifecycle_request()

        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_witness_lifecycle_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        assert body1["ok"] is True
        packet = body1["packet"]
        assert packet["packet_built"] is True
        assert packet["end_to_end_packet_ok"] is True
        assert packet["witness_present"] is True
        assert packet["witness_valid"] is True
        assert packet["settled"] is True
        assert packet["rejected_with_reason"] is False
        assert packet["lifecycle_ok"] is True

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_witness_lifecycle_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] is None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_settlement_witness_lifecycle_packet_rejected_with_reason() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req, _ = _settlement_witness_lifecycle_request(price_history=[0, 60, 70])

        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_settlement_witness_lifecycle_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["packet_built"] is True
        assert packet["end_to_end_packet_ok"] is False
        assert packet["witness_present"] is False
        assert packet["settled"] is False
        assert packet["rejected_with_reason"] is True
        assert packet["rejection_reason"] == "settlement end-to-end certificate full price rails rejected"
        assert packet["lifecycle_ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_verify_settlement_witness_lifecycle_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req, _ = _settlement_witness_lifecycle_request()

        conn1 = HTTPConnection(host, port, timeout=2.0)
        conn1.request(
            "POST",
            "/api/dex/build_settlement_witness_lifecycle_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp1 = conn1.getresponse()
        body1 = json.loads(resp1.read().decode("utf-8"))
        assert resp1.status == 200
        packet = body1["packet"]
        packet["settled"] = False

        verify_req = dict(req)
        verify_req["packet"] = packet
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_settlement_witness_lifecycle_packet",
            body=json.dumps(verify_req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "settlement witness lifecycle packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_dex_impact_preview() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        req = {
            "reserve_in": 1_000_000,
            "reserve_out": 1_000_000,
            "amount_in": 10_000,
            "fee_bps": 30,
            "pending_volume_same_direction": 50_000,
            "confidence_bps": 9500,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/impact_preview",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        preview = body["preview"]
        assert isinstance(preview, dict)
        assert int(preview["amount_out_best_case"]) >= int(preview["amount_out_worst_case"])
        assert int(preview["amount_out_isolated"]) == int(preview["amount_out_best_case"])
        assert int(preview["recommended_min_out"]) >= int(preview["amount_out_worst_case"])
        assert int(preview["recommended_min_out"]) <= int(preview["amount_out_best_case"])
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_certificate_build_and_verify_roundtrip() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        quotes = [
            {
                "amount_out_total": 10,
                "amount_in_total": 11,
                "legs": [
                    {"pool_id": "pool_b", "amount_out": 4, "amount_in": 4},
                    {"pool_id": "pool_c", "amount_out": 6, "amount_in": 7},
                ],
            },
            {
                "amount_out_total": 10,
                "amount_in_total": 11,
                "legs": [
                    {"pool_id": "pool_b", "amount_out": 10, "amount_in": 11},
                ],
            },
            {
                "amount_out_total": 10,
                "amount_in_total": 11,
                "legs": [
                    {"pool_id": "pool_a", "amount_out": 4, "amount_in": 4},
                    {"pool_id": "pool_c", "amount_out": 6, "amount_in": 7},
                ],
            },
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_route_certificate",
            body=json.dumps({"quotes": quotes}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        certificate = body["certificate"]
        assert isinstance(certificate, dict)
        assert certificate["winner_index"] == 1

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_route_certificate",
            body=json.dumps({"certificate": certificate}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["error"] == "ok"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_certificate_verify_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        quotes = [
            {
                "amount_out_total": 10,
                "amount_in_total": 11,
                "legs": [
                    {"pool_id": "pool_b", "amount_out": 10, "amount_in": 11},
                ],
            },
            {
                "amount_out_total": 10,
                "amount_in_total": 11,
                "legs": [
                    {"pool_id": "pool_a", "amount_out": 4, "amount_in": 4},
                    {"pool_id": "pool_c", "amount_out": 6, "amount_in": 7},
                ],
            },
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_route_certificate",
            body=json.dumps({"quotes": quotes}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        certificate = dict(body["certificate"])
        certificate["winner_index"] = int(certificate["winner_index"]) + 1

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_route_certificate",
            body=json.dumps({"certificate": certificate}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "certificate payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_two_pool_canonicality_audit_matches_on_asymmetric_case() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=25, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/audit_exact_out_two_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 5,
                    "pools": pools,
                    "brute_force_max": 5,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        audit = body["audit"]
        assert audit["runtime_matches_canonical"] is True
        assert audit["candidate_count"] >= 1
        assert audit["runtime_quote"] == audit["canonical_winner_quote"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_two_pool_canonicality_audit_matches_symmetric_plateau() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=15, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/audit_exact_out_two_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 1,
                    "pools": pools,
                    "brute_force_max": 1,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        audit = body["audit"]
        assert audit["runtime_matches_canonical"] is True
        assert audit["runtime_quote"] == audit["canonical_winner_quote"]
        assert audit["runtime_quote"]["legs"][0]["pool_id"] == "pool_a"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_canonicality_audit_matches_small_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/audit_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_full_domain_pools": 9,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        audit = body["audit"]
        assert audit["runtime_matches_canonical"] is True
        assert audit["runtime_quote"] == audit["canonical_winner_quote"]
        assert audit["audit_pool_ids"] == ["pool_c"]
        assert audit["candidate_count"] >= 1
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_canonicality_audit_shows_runtime_alignment_on_known_counterexample() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/audit_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        audit = body["audit"]
        assert audit["runtime_matches_canonical"] is True
        assert audit["runtime_quote"]["amount_in_total"] == 2
        assert audit["canonical_winner_quote"]["amount_in_total"] == 2
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_canonicality_audit_rejects_bad_budget() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/audit_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_enumerated_candidates": 0,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 400
        assert body["ok"] is False
        assert body["error"] == "bad_max_enumerated_candidates"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_oracle_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_oracle_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_full_domain_pools": 9,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert body["contract_ok"] is True
        assert contract["contract_ok"] is True
        assert contract["audit"]["runtime_matches_canonical"] is True
        assert contract["audit"]["runtime_quote"] == contract["audit"]["canonical_winner_quote"]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_candidate_domain_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_candidate_domain_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["contract_ok"] is True
        assert contract["candidate_domain_nonempty"] is True
        assert contract["all_candidates_complete"] is True
        assert contract["all_candidates_leg_bounded"] is True
        assert contract["all_candidates_leg_pool_ids_sorted_unique"] is True
        assert contract["all_candidates_within_audit_pool_ids"] is True
        assert contract["candidate_count_within_budget"] is True
        assert contract["audit_pool_ids"] == ["pool_c"]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_prefilter_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_prefilter_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["contract_ok"] is True
        assert contract["selected_pool_ids"] == ["pool_a", "pool_b", "pool_c"]
        assert contract["selected_is_prefix_of_feasible_ranking"] is True
        assert contract["selected_capacity_guard_feasible"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_prefilter_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_prefilter_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        contract["selected_is_prefix_of_feasible_ranking"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "prefilter contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_prefilter_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["current_selected_pool_ids"] == ["p0", "p2", "p3"]
        assert contract["repaired_selected_pool_ids"] == ["p0", "p1"]
        assert contract["repaired_selected_domain_matches_full_canonical"] is True
        assert contract["repaired_contraction_holds"] is True
        assert contract["contract_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_repaired_prefilter_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        contract["repaired_selected_domain_matches_full_canonical"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "repaired prefilter contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_selected_domain_oracle_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert body["contract_schema"] == contract["schema"]
        assert body["quote_endpoint"] == "/api/dex/quote_exact_out_many_pool_repaired_selected_domain"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract"
        assert contract["repaired_selected_pool_ids"] == ["p0", "p1"]
        assert contract["repaired_selected_domain_matches_full_canonical"] is True
        assert contract["audit_pool_ids_match_repaired_selected_pool_ids"] is True
        assert contract["replacement_quote_matches_full_canonical"] is True
        assert contract["contract_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "repaired_selected_domain_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_repaired_selected_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "repaired_selected_domain_v1"
        assert body["contract_schema"] == body["contract"]["schema"]
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract"
        assert body["repaired_selected_pool_ids"] == ["p0", "p1"]
        assert body["repaired_selected_domain_matches_full_canonical"] is True
        assert body["audit_pool_ids_match_repaired_selected_pool_ids"] is True
        assert body["repaired_selected_domain_runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["repaired_selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["repaired_selected_domain_runtime_matches_canonical"] is True
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["replacement_quote_matches_full_canonical"] is True
        assert body["quote"] == body["repaired_selected_domain_runtime_quote"]
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_replacement_shadow_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_replacement_shadow_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet"
        assert packet["packet_ok"] is True
        assert packet["replacement_available"] is True
        assert packet["effective_quote_matches_replacement_quote"] is True
        assert packet["replacement_quote_matches_selected_runtime_quote"] is True
        assert packet["replacement_quote_matches_full_canonical"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_replacement_shadow_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_repaired_advisory() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_repaired_advisory",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["packet_schema"] == body["packet"]["schema"]
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet"
        assert body["runtime_matches_advisory"] is True
        assert body["runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["repaired_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_projection_cover_side"] == "repaired"
        assert body["effective_projection_cover_holds"] is True
        assert body["effective_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_matches_canonical_projected_path"] is True
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["runtime_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["packet"]["repaired_contract"]["contract_ok"] is True
        assert body["packet"]["projection_cover_audit"] is not None
        assert body["packet"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert body["packet"]["projection_cover_audit"]["canonical_quote_projected_path"] == [
            ["p0", 2, 5],
            ["p1", 2, 5],
        ]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_repaired_full_domain_certified() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))

        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "repaired_full_domain_certified_v1"
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet"
        assert body["repaired_matches_full_canonical"] is True
        assert body["full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
        assert body["quote"] == body["full_domain_canonical_quote"]
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["runtime_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_advisory_quote_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet"
        assert packet["packet_ok"] is True
        assert packet["runtime_matches_advisory"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_full_domain_certified_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_full_domain_certified_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))

        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "repaired_full_domain_certified_v1"
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["repaired_matches_full_canonical"] is True
        assert packet["full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet"

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_full_domain_certified_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "repaired_full_domain_certified_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_key_cover_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_key_cover_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))

        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "repaired_key_cover_v1"
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["selected_keys_subset_full_keys"] is True
        assert packet["key_cover_holds"] is True
        assert packet["selected_domain_canonical_matches_full_domain_canonical"] is True
        assert packet["selected_domain_contract"]["contract_ok"] is True
        assert packet["repaired_full_domain_packet"]["packet_ok"] is True
        assert len(packet["domination_witnesses"]) == packet["full_candidate_count"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet"

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_key_cover_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "repaired_key_cover_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_repaired_key_cover_interpretation_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))

        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "repaired_key_cover_interpretation_v1"
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["selected_winner_index_in_range"] is True
        assert packet["selected_winner_matches_certificate"] is True
        assert packet["selected_winner_key_minimal"] is True
        assert packet["domination_witness_indices_in_range"] is True
        assert packet["domination_witnesses_cover_full_candidates"] is True
        assert packet["domination_witness_keys_match_candidates"] is True
        assert packet["domination_witnesses_dominate"] is True
        assert packet["key_cover_packet"]["packet_ok"] is True
        assert (
            body["verify_packet_endpoint"]
            == "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet"
        )

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_key_cover_interpretation_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "repaired_key_cover_interpretation_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_bounded_workaround_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_bounded_workaround_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet"
        assert packet["packet_ok"] is True
        assert packet["runtime_quotes_agree"] is True
        assert packet["runtime_matches_repaired_advisory"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_bounded_workaround_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_bounded_workaround_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]
        packet["runtime_quotes_agree"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_bounded_workaround_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "bounded workaround packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_bounded_advisory_prefers_repaired_quote() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_bounded_advisory",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["packet_schema"] == body["packet"]["schema"]
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet"
        assert body["quote_source"] == "selected_domain_runtime"
        assert body["repaired_advisory_available"] is True
        assert body["quote_matches_runtime"] is True
        assert body["quote_matches_repaired_advisory"] is True
        assert body["runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_domain_projection_cover_available"] is True
        assert body["selected_domain_projection_cover_holds"] is True
        assert body["packet"]["workaround_packet"]["repaired_full_domain_packet"]["packet_ok"] is True
        assert body["packet"]["workaround_packet"]["repaired_full_domain_packet"]["repaired_matches_full_canonical"] is True
        assert body["selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["repaired_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_matches_repaired_canonical_projected_path"] is True
        assert body["effective_projection_cover_side"] == "selected_domain"
        assert body["effective_projection_cover_holds"] is True
        assert body["effective_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_matches_canonical_projected_path"] is True
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["runtime_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"] is not None
        assert body["packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert body["packet"]["workaround_packet"]["runtime_matches_repaired_advisory"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_default_uses_certified_advisory_policy() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "certified_advisory_v1"
        assert body["packet_schema"] == body["packet"]["schema"]
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_default_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_default_packet"
        assert body["effective_quote"] == body["quote"]
        assert body["quote_source"] == "selected_domain_runtime"
        assert body["selected_runtime_quotes_agree"] is True
        assert body["quote_matches_runtime"] is True
        assert body["quote_matches_repaired_advisory"] is True
        assert body["repaired_full_domain_packet_ok"] is True
        assert body["repaired_quote_matches_full_domain_canonical"] is True
        assert body["repaired_full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
        assert body["repaired_full_domain_candidate_count"] == body["packet"]["advisory_packet"]["workaround_packet"][
            "repaired_full_domain_packet"
        ]["full_domain_candidate_count"]
        assert body["repaired_full_domain_canonical_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["effective_quote_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_packet_ok"] is True
        assert body["repaired_selected_keys_subset_full_keys"] is True
        assert body["repaired_key_cover_holds"] is True
        assert body["repaired_selected_domain_canonical_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_witness_count"] == body["packet"]["repaired_key_cover_packet"]["full_candidate_count"]
        assert body["repaired_key_cover_interpretation_packet_ok"] is True
        assert body["repaired_key_cover_selected_winner_index_in_range"] is True
        assert body["repaired_key_cover_selected_winner_matches_certificate"] is True
        assert body["repaired_key_cover_selected_winner_key_minimal"] is True
        assert body["repaired_key_cover_witness_indices_in_range"] is True
        assert body["repaired_key_cover_witness_coverage_complete"] is True
        assert body["repaired_key_cover_witness_keys_match_candidates"] is True
        assert body["repaired_key_cover_witness_domination_holds"] is True
        assert body["selected_domain_runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_domain_projection_cover_available"] is True
        assert body["selected_domain_projection_cover_holds"] is True
        assert body["packet"]["advisory_packet"]["workaround_packet"]["repaired_full_domain_packet"]["packet_ok"] is True
        assert (
            body["packet"]["advisory_packet"]["workaround_packet"]["repaired_full_domain_packet"][
                "repaired_matches_full_canonical"
            ]
            is True
        )
        assert body["selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["repaired_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_matches_repaired_canonical_projected_path"] is True
        assert body["effective_projection_cover_side"] == "selected_domain"
        assert body["effective_projection_cover_holds"] is True
        assert body["effective_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_matches_canonical_projected_path"] is True
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["runtime_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["packet"]["certified_packet"]["packet_ok"] is True
        assert body["packet"]["advisory_packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"] is not None
        assert (
            body["packet"]["advisory_packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"][
                "projection_cover_holds"
            ]
            is True
        )
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_default_falls_back_on_aligned_case() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 8_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "certified_advisory_v1"
        assert body["packet_schema"] == body["packet"]["schema"]
        assert body["effective_quote"] == body["quote"]
        assert body["quote_source"] == "selected_domain_runtime"
        assert body["selected_runtime_quotes_agree"] is True
        assert body["quote_matches_runtime"] is True
        assert body["quote_matches_repaired_advisory"] is True
        assert body["repaired_full_domain_packet_ok"] is True
        assert body["repaired_quote_matches_full_domain_canonical"] is True
        assert body["repaired_full_domain_feasible_pool_ids"] == ["pool_a", "pool_b", "pool_c"]
        assert body["repaired_full_domain_candidate_count"] == body["packet"]["advisory_packet"]["workaround_packet"][
            "repaired_full_domain_packet"
        ]["full_domain_candidate_count"]
        assert body["repaired_full_domain_canonical_quote"]["legs"] == [
            {"pool_id": "pool_b", "amount_out": 3, "amount_in": 2}
        ]
        assert body["effective_quote_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_packet_ok"] is True
        assert body["repaired_selected_keys_subset_full_keys"] is True
        assert body["repaired_key_cover_holds"] is True
        assert body["repaired_selected_domain_canonical_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_witness_count"] == body["packet"]["repaired_key_cover_packet"]["full_candidate_count"]
        assert body["repaired_key_cover_interpretation_packet_ok"] is True
        assert body["repaired_key_cover_selected_winner_index_in_range"] is True
        assert body["repaired_key_cover_selected_winner_matches_certificate"] is True
        assert body["repaired_key_cover_selected_winner_key_minimal"] is True
        assert body["repaired_key_cover_witness_indices_in_range"] is True
        assert body["repaired_key_cover_witness_coverage_complete"] is True
        assert body["repaired_key_cover_witness_keys_match_candidates"] is True
        assert body["repaired_key_cover_witness_domination_holds"] is True
        assert body["selected_domain_runtime_projected_path"] == [["pool_b", 3, 2]]
        assert body["advisory_projected_path"] == [["pool_b", 3, 2]]
        assert body["selected_domain_projection_cover_available"] is True
        assert body["selected_domain_projection_cover_holds"] is True
        assert body["selected_domain_canonical_projected_path"] == [["pool_b", 3, 2]]
        assert body["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["repaired_canonical_projected_path"] == [["pool_b", 3, 2]]
        assert body["advisory_matches_repaired_canonical_projected_path"] is True
        assert body["effective_projection_cover_side"] == "selected_domain"
        assert body["effective_projection_cover_holds"] is True
        assert body["effective_canonical_projected_path"] == [["pool_b", 3, 2]]
        assert body["effective_quote_projected_path"] == [["pool_b", 3, 2]]
        assert body["effective_quote_matches_canonical_projected_path"] is True
        assert body["quote"] == body["runtime_quote"]
        assert body["quote"]["amount_in_total"] == 2
    finally:
        _stop_test_server(httpd, t)


def test_api_server_default_quote_packet_matches_default_build_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            body["build_packet_endpoint"],
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body["packet"] == body2["packet"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_certified_advisory_prefers_repaired_quote() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_certified_advisory",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "certified_advisory_v1"
        assert body["packet_schema"] == body["packet"]["schema"]
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_certified_advisory_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_certified_advisory_packet"
        assert body["effective_quote"] == body["quote"]
        assert body["quote_source"] == "selected_domain_runtime"
        assert body["repaired_advisory_available"] is True
        assert body["selected_runtime_quotes_agree"] is True
        assert body["quote_matches_runtime"] is True
        assert body["quote_matches_repaired_advisory"] is True
        assert body["repaired_full_domain_packet_ok"] is True
        assert body["repaired_quote_matches_full_domain_canonical"] is True
        assert body["repaired_full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
        assert body["repaired_full_domain_candidate_count"] == body["packet"]["advisory_packet"]["workaround_packet"][
            "repaired_full_domain_packet"
        ]["full_domain_candidate_count"]
        assert body["repaired_full_domain_canonical_quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["effective_quote_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_packet_ok"] is True
        assert body["repaired_selected_keys_subset_full_keys"] is True
        assert body["repaired_key_cover_holds"] is True
        assert body["repaired_selected_domain_canonical_matches_full_domain_canonical"] is True
        assert body["repaired_key_cover_witness_count"] == body["packet"]["repaired_key_cover_packet"]["full_candidate_count"]
        assert body["repaired_key_cover_interpretation_packet_ok"] is True
        assert body["repaired_key_cover_selected_winner_index_in_range"] is True
        assert body["repaired_key_cover_selected_winner_matches_certificate"] is True
        assert body["repaired_key_cover_selected_winner_key_minimal"] is True
        assert body["repaired_key_cover_witness_indices_in_range"] is True
        assert body["repaired_key_cover_witness_coverage_complete"] is True
        assert body["repaired_key_cover_witness_keys_match_candidates"] is True
        assert body["repaired_key_cover_witness_domination_holds"] is True
        assert body["selected_domain_runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_domain_projection_cover_available"] is True
        assert body["selected_domain_projection_cover_holds"] is True
        assert body["selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert body["repaired_projection_cover_available"] is True
        assert body["repaired_projection_cover_holds"] is True
        assert body["repaired_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["advisory_matches_repaired_canonical_projected_path"] is True
        assert body["effective_projection_cover_side"] == "selected_domain"
        assert body["effective_projection_cover_holds"] is True
        assert body["effective_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
        assert body["effective_quote_matches_canonical_projected_path"] is True
        assert body["quote"]["legs"] == [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ]
        assert body["packet"]["certified_packet"]["packet_ok"] is True
        assert body["packet"]["advisory_packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"] is not None
    finally:
        _stop_test_server(httpd, t)


def test_api_server_certified_advisory_quote_packet_matches_build_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        req = {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 4,
            "max_legs": 3,
            "max_candidate_pools": 3,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 64,
            "brute_force_max": 512,
            "max_full_domain_pools": 6,
            "max_enumerated_candidates": 50_000,
            "pools": pools,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_certified_advisory",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            body["build_packet_endpoint"],
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body["packet"] == body2["packet"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_default_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_default_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "certified_advisory_v1"
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_default_packet"
        assert packet["packet_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_default_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "certified_advisory_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_default_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_default_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]
        packet["selected_runtime_quotes_agree"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_default_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "certified advisory packet payload mismatch"
        assert body2["quote_policy"] == "certified_advisory_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_certified_advisory_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_certified_advisory_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_certified_advisory_packet"
        assert packet["packet_ok"] is True

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_certified_advisory_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_certified_advisory_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]
        packet["selected_runtime_quotes_agree"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_certified_advisory_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "certified advisory packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_bounded_advisory_quote_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet"
        assert packet["packet_ok"] is True
        assert packet["quote_source"] == "selected_domain_runtime"

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_bounded_advisory_quote_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_bounded_advisory_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]
        packet["quote_source"] = "repaired_bounded_advisory"

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_bounded_advisory_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "bounded advisory quote packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_repaired_advisory_quote_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_repaired_advisory_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50_000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]
        packet["runtime_matches_advisory"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_repaired_advisory_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "repaired advisory quote packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_candidate_domain_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_candidate_domain_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        contract["contract_ok"] = False

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "candidate domain contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_oracle_contract_shows_runtime_alignment_on_known_counterexample() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_oracle_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["audit"]["runtime_matches_canonical"] is True
        assert contract["audit"]["runtime_quote"]["amount_in_total"] == 2
        assert contract["audit"]["canonical_winner_quote"]["amount_in_total"] == 2
        assert contract["audit"]["runtime_projected_path"] == [["pool_b", 3, 2]]
        assert contract["audit"]["canonical_winner_projected_path"] == [["pool_b", 3, 2]]
        assert contract["audit"]["runtime_matches_canonical_projected_path"] is True
        assert contract["audit"]["projection_cover_available"] is True
        assert contract["audit"]["projection_cover_holds"] is True
        assert contract["audit"]["projection_cover_audit"] is not None
        assert contract["audit"]["projection_cover_audit"]["projection_cover_holds"] is True

        contract["audit"]["projection_cover_audit"]["projection_cover_holds"] = False
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "oracle contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_oracle_contract_carries_projection_cover_on_mixed_curve_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=20, fee_bps=0, curve_tag="SUM_BOOST_V1", curve_params={"mu_num": 200, "mu_den": 10000}),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_oracle_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 2,
                    "max_candidate_pools": 2,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert contract["audit"]["runtime_matches_canonical"] is True
        assert contract["audit"]["runtime_projected_path"] == [["pool_b", 3, 5]]
        assert contract["audit"]["canonical_winner_projected_path"] == [["pool_b", 3, 5]]
        assert contract["audit"]["runtime_matches_canonical_projected_path"] is True
        assert contract["audit"]["projection_cover_available"] is True
        assert contract["audit"]["projection_cover_holds"] is True
        assert contract["audit"]["projection_cover_audit"] is not None
        assert contract["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert contract["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_oracle_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_guard_exact_out_many_pool_canonicality_accepts_match() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/guard_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["quote"] == body["contract"]["audit"]["runtime_quote"]
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == body["canonical_winner_projected_path"]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_guard_exact_out_many_pool_canonicality_accepts_known_counterexample_after_alignment() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/guard_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["quote"]["amount_in_total"] == 2
        assert body["contract"]["audit"]["canonical_winner_quote"]["amount_in_total"] == 2
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == [["pool_b", 3, 2]]
        assert body["canonical_winner_projected_path"] == [["pool_b", 3, 2]]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_guard_exact_out_many_pool_canonicality_accepts_mixed_curve_selected_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=20, fee_bps=0, curve_tag="SUM_BOOST_V1", curve_params={"mu_num": 200, "mu_den": 10000}),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/guard_exact_out_many_pool_canonicality",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 2,
                    "max_candidate_pools": 2,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["quote"] == body["contract"]["audit"]["runtime_quote"]
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == [["pool_b", 3, 5]]
        assert body["canonical_winner_projected_path"] == [["pool_b", 3, 5]]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
        assert body["contract"]["audit"]["projection_cover_audit"] is not None
        assert body["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert body["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_guarded_accepts_match() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_guarded",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["packet_schema"] == "zenodex/exact-out-many-pool-guarded-quote-packet/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_guarded_quote_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_guarded_quote_packet"
        assert body["quote"] == body["contract"]["audit"]["runtime_quote"]
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == body["canonical_winner_projected_path"]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_guarded_accepts_known_counterexample_after_alignment() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_guarded",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["packet_schema"] == "zenodex/exact-out-many-pool-guarded-quote-packet/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_guarded_quote_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_guarded_quote_packet"
        assert body["quote"]["amount_in_total"] == 2
        assert body["contract"]["audit"]["canonical_winner_quote"]["amount_in_total"] == 2
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == [["pool_b", 3, 2]]
        assert body["canonical_winner_projected_path"] == [["pool_b", 3, 2]]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_guarded_accepts_mixed_curve_selected_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=20, fee_bps=0, curve_tag="SUM_BOOST_V1", curve_params={"mu_num": 200, "mu_den": 10000}),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_guarded",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 2,
                    "max_candidate_pools": 2,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["contract_ok"] is True
        assert body["contract"]["contract_ok"] is True
        assert body["contract_schema"] == "zenodex/exact-out-many-pool-oracle-contract/v1"
        assert body["packet_schema"] == "zenodex/exact-out-many-pool-guarded-quote-packet/v1"
        assert body["build_contract_endpoint"] == "/api/dex/build_exact_out_many_pool_oracle_contract"
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_oracle_contract"
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_guarded_quote_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_guarded_quote_packet"
        assert body["quote"] == body["contract"]["audit"]["runtime_quote"]
        assert body["contract"]["audit"]["runtime_matches_canonical"] is True
        assert body["runtime_projected_path"] == [["pool_b", 3, 5]]
        assert body["canonical_winner_projected_path"] == [["pool_b", 3, 5]]
        assert body["runtime_matches_canonical_projected_path"] is True
        assert body["projection_cover_available"] is True
        assert body["projection_cover_holds"] is True
        assert body["contract"]["audit"]["projection_cover_audit"] is not None
        assert body["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert body["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_guarded_quote_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_guarded_quote_packet"
        assert packet["guard_ok"] is True
        assert packet["contract"]["contract_ok"] is True
        assert packet["quote"] == packet["contract"]["audit"]["runtime_quote"]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_guarded_quote_packet_builds_on_known_counterexample_after_alignment() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["guard_ok"] is True
        assert packet["error"] is None
        assert packet["quote"] == packet["contract"]["audit"]["runtime_quote"]
        assert packet["contract"]["audit"]["runtime_matches_canonical"] is True

        packet["guard_ok"] = False
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "guarded quote packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_guarded_quote_packet_carries_projection_cover_on_mixed_curve_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=20, fee_bps=0, curve_tag="SUM_BOOST_V1", curve_params={"mu_num": 200, "mu_den": 10000}),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 2,
                    "max_candidate_pools": 2,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["guard_ok"] is True
        assert packet["selected_domain_projection_cover_available"] is True
        assert packet["selected_domain_projection_cover_holds"] is True
        assert packet["selected_domain_canonical_projected_path"] == [["pool_b", 3, 5]]
        assert packet["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert packet["guarded_quote"] == packet["contract"]["audit"]["runtime_quote"]
        assert packet["guarded_quote_projected_path"] == [["pool_b", 3, 5]]
        assert packet["guarded_quote_matches_runtime_quote"] is True
        assert packet["guarded_quote_matches_canonical_projected_path"] is True
        assert packet["contract"]["audit"]["projection_cover_audit"] is not None
        assert packet["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert packet["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_guarded_quote_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_certified_winner_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_certified_winner_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_full_domain_pools": 9,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_certified_winner_packet"
        assert packet["packet_ok"] is True
        assert packet["domain_contract"]["contract_ok"] is True
        assert packet["guarded_packet"]["guard_ok"] is True
        assert packet["guarded_packet"]["contract"]["max_full_domain_pools"] == 9

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_audited_bounds_contract() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_audited_bounds_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_full_domain_pools": 9,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        contract = body["contract"]
        assert body["contract_schema"] == contract["schema"]
        assert body["verify_contract_endpoint"] == "/api/dex/verify_exact_out_many_pool_audited_bounds_contract"
        assert contract["contract_ok"] is True
        assert contract["max_full_domain_pools"] == 9
        assert contract["certified_advisory_packet"]["certified_packet"]["guarded_packet"]["contract"]["max_full_domain_pools"] == 9

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)


def test_api_server_verify_exact_out_many_pool_audited_bounds_contract_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=100, r1=34, fee_bps=0),
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=120, r1=40, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=160, r1=60, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_audited_bounds_contract",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 6,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 12,
                    "max_full_domain_pools": 9,
                    "max_enumerated_candidates": 2000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        contract = body["contract"]

        contract["budget_parameters_bound"] = False
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_audited_bounds_contract",
            body=json.dumps({"contract": contract}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "audited bounds contract payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_quote_exact_out_many_pool_adaptive() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/quote_exact_out_many_pool_adaptive",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "adaptive_liveness_v1"
        assert body["build_packet_endpoint"] == "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet"
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet"
        assert body["cheap_path_success"] is True
        assert body["fallback_success"] is False
        assert body["liveness_ok"] is True
        assert body["quote_source"] == "default_certified_advisory"
        assert body["quote"] == body["packet"]["effective_quote"]
    finally:
        _stop_test_server(httpd, t)


def test_api_server_build_and_verify_exact_out_many_pool_adaptive_liveness_packet() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 1,
                    "max_candidates": 2,
                    "max_iters": 1,
                    "window": 0,
                    "brute_force_max": 0,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        assert body["quote_policy"] == "adaptive_liveness_v1"
        assert body["liveness_ok"] is True
        packet = body["packet"]
        assert body["packet_schema"] == packet["schema"]
        assert body["verify_packet_endpoint"] == "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet"
        assert packet["explicit_failure"] is True
        assert packet["failure_reason"] == "default_packet_not_ok"

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
        assert body2["quote_policy"] == "adaptive_liveness_v1"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_verify_exact_out_many_pool_adaptive_liveness_packet_rejects_tampering() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="p0", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p1", a0="A", a1="B", r0=20, r1=10, fee_bps=0),
            _pool_dict(pid="p2", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
            _pool_dict(pid="p3", a0="A", a1="B", r0=30, r1=15, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_adaptive_liveness_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 4,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 12,
                    "max_iters": 4096,
                    "window": 64,
                    "brute_force_max": 512,
                    "max_full_domain_pools": 6,
                    "max_enumerated_candidates": 50000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        packet = body["packet"]

        packet["fallback_attempted"] = True
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_adaptive_liveness_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "adaptive liveness packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_certified_winner_packet_builds_on_known_counterexample_after_alignment() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=63, fee_bps=0),
            _pool_dict(pid="pool_c", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_certified_winner_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 3,
                    "max_candidate_pools": 3,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["guarded_packet"]["guard_ok"] is True
        assert packet["guarded_packet"]["error"] is None

        packet["packet_ok"] = False
        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is False
        assert body2["error"] == "certified winner packet payload mismatch"
    finally:
        _stop_test_server(httpd, t)


def test_api_server_exact_out_many_pool_certified_winner_packet_carries_projection_cover_on_mixed_curve_domain() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        pools = [
            _pool_dict(pid="pool_a", a0="A", a1="B", r0=40, r1=20, fee_bps=0),
            _pool_dict(pid="pool_b", a0="A", a1="B", r0=40, r1=20, fee_bps=0, curve_tag="SUM_BOOST_V1", curve_params={"mu_num": 200, "mu_den": 10000}),
        ]
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/build_exact_out_many_pool_certified_winner_packet",
            body=json.dumps(
                {
                    "asset_in": "A",
                    "asset_out": "B",
                    "amount_out_total": 3,
                    "max_legs": 2,
                    "max_candidate_pools": 2,
                    "max_candidates": 6,
                    "max_iters": 512,
                    "window": 8,
                    "brute_force_max": 16,
                    "max_enumerated_candidates": 8000,
                    "pools": pools,
                }
            ).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        packet = body["packet"]
        assert packet["packet_ok"] is True
        assert packet["selected_domain_projection_cover_available"] is True
        assert packet["selected_domain_projection_cover_holds"] is True
        assert packet["selected_domain_canonical_projected_path"] == [["pool_b", 3, 5]]
        assert packet["selected_runtime_matches_selected_canonical_projected_path"] is True
        assert packet["certified_quote"] == packet["guarded_packet"]["quote"]
        assert packet["certified_quote_projected_path"] == [["pool_b", 3, 5]]
        assert packet["certified_quote_matches_runtime_quote"] is True
        assert packet["certified_quote_matches_canonical_projected_path"] is True
        assert packet["guarded_packet"]["contract"]["audit"]["projection_cover_audit"] is not None
        assert packet["guarded_packet"]["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
        assert packet["guarded_packet"]["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

        conn2 = HTTPConnection(host, port, timeout=2.0)
        conn2.request(
            "POST",
            "/api/dex/verify_exact_out_many_pool_certified_winner_packet",
            body=json.dumps({"packet": packet}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp2 = conn2.getresponse()
        body2 = json.loads(resp2.read().decode("utf-8"))
        assert resp2.status == 200
        assert body2["ok"] is True
    finally:
        _stop_test_server(httpd, t)
