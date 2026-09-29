"""Owned pool snapshots preserve ordinary plan, receipt and advisory readers."""

from src.agents.route_economic_sanity import build_route_economic_sanity_snapshot
from src.core.quote_receipts import pool_state_fingerprint, receipt_hash, verify_route_quote_receipt
from src.core.spot_swap_plan_v2 import SpotSwapContextV2, SpotSwapPlanV2, plan_spot_swap_v2
from src.state.intents import IntentKind, SwapIntent
from src.state.pools import PoolState, PoolStatus, snapshot_pool, snapshot_pool_table


def _pool() -> PoolState:
    return PoolState(
        pool_id="pool", asset0="A", asset1="B", reserve0=1_000, reserve1=1_000,
        fee_bps=30, lp_supply=1_000, status=PoolStatus.ACTIVE, created_at=0,
    )


def test_spot_planner_accepts_committed_pool_without_changing_economic_result() -> None:
    pool = _pool()
    context = SpotSwapContextV2(
        subject_id="alice", block_timestamp=100,
        sender_input_atoms=100, recipient_output_atoms=5,
    )
    intent = SwapIntent(
        "TauSwap", "0.1", IntentKind.SWAP_EXACT_OUT, "0x" + "11" * 32,
        "alice", 100,
        fields={"pool_id": "pool", "asset_in": "A", "asset_out": "B",
                "nonce": 1, "amount_out": 7, "max_amount_in": 10},
    )
    expected = plan_spot_swap_v2(context, pool, intent)
    actual = plan_spot_swap_v2(context, snapshot_pool(pool), intent)
    assert isinstance(actual, SpotSwapPlanV2)
    assert actual == expected
    assert (actual.amount_in_atoms, actual.amount_out_atoms, actual.fee_atoms) == (9, 7, 1)


def test_quote_and_route_metrics_accept_committed_pool_mapping() -> None:
    pool = _pool()
    # Independent integer vector: fee=ceil(100*30/10000)=1;
    # output=floor(99*1000/(1000+99))=90.
    hop = {"pool_id": "pool", "asset_in": "A", "asset_out": "B",
           "amount_in": 100, "amount_out": 90}
    body = {
        "schema": "zenodex/route_quote_receipt/v1", "kind": "exact_in",
        "asset_in": "A", "asset_out": "B", "amount_in": 100, "amount_out": 90,
        "legs": [{"amount_in": 100, "amount_out": 90, "hops": [hop]}],
        "pools": {"pool": pool_state_fingerprint(pool)},
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}
    builders = {"pool": pool}
    committed = snapshot_pool_table(builders)
    assert verify_route_quote_receipt(receipt, pools_by_id=builders) == (True, "ok")
    assert verify_route_quote_receipt(receipt, pools_by_id=committed) == (True, "ok")
    expected = build_route_economic_sanity_snapshot(quote_receipt=receipt, pools_by_id=builders)
    actual = build_route_economic_sanity_snapshot(quote_receipt=receipt, pools_by_id=committed)
    assert actual is not None and actual == expected
    assert committed["pool"].reserve0 == 1_000
    assert committed["pool"].reserve1 == 1_000
