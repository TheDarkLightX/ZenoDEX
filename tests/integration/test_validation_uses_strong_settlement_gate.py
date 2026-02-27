from __future__ import annotations

from src.core.settlement import BalanceDelta, Fill, FillAction, ReserveDelta, Settlement
from src.integration.validation import validate_operations
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_validate_operations_rejects_k_decrease_settlement() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )

    # Malicious settlement: drains too much output from the pool (k decreases),
    # but keeps reserves non-negative.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=200,  # impossible under CPMM reserves=(1000,1000) with fee_bps=30
                fee_paid=1,
                reserve_in_before=1_000,
                reserve_out_before=1_000,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[
            ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=100, delta_sub=0),
            ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=0, delta_sub=200),
        ],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_operations(
        intents=[intent],
        settlement=settlement,
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        block_timestamp=0,
    )
    assert ok is False
    assert err is not None

