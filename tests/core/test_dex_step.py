# [TESTER] v1

from __future__ import annotations

import pytest

from src.core import (
    DexConfig,
    DexEffects,
    DexState,
    DexStepResult,
    FeeSplitParams,
    dex_step,
)
from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_dex_step_end_to_end_create_swap_lp() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    # Pool id is deterministic from (asset0, asset1, fee_bps).
    pool_id, _, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()

    state = DexState(balances=balances, pools={}, lp_balances=lp_balances)
    config = DexConfig(fee_split_params=FeeSplitParams(buyback_bps=3000, treasury_bps=3000, rewards_bps=4000))

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "amount0": 2_000_000,
                "amount1": 2_000_000,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_OUT,
            intent_id=_iid(5),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset1,
                "asset_out": asset0,
                "amount_out": 500,
                "max_amount_in": 10_000_000,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.ADD_LIQUIDITY,
            intent_id=_iid(3),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "amount0_desired": 100_000,
                "amount1_desired": 100_000,
                "amount0_min": 0,
                "amount1_min": 0,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.REMOVE_LIQUIDITY,
            intent_id=_iid(4),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "lp_amount": 1000,
                "amount0_min": 0,
                "amount1_min": 0,
            },
        ),
    ]

    res = dex_step(config, state, intents)
    assert res.ok, res.error
    assert res.state is not None
    assert type(res.effects) is DexEffects

    next_state = res.state
    settlement = res.effects["settlement"]
    assert settlement.module == "TauSwap"
    assert pool_id in next_state.pools

    # LP balances exist for the user and the lock address after pool creation.
    assert next_state.lp_balances.get(pk, pool_id) > 0
    assert next_state.lp_balances.get("0x" + "00" * 48, pool_id) > 0

    # Fee split is computed when configured.
    assert int(res.effects["total_swap_fees"]) >= 0
    assert res.effects["fee_split"] is not None

    # Accepted effects retain their historical mapping reads but cannot mutate.
    with pytest.raises(TypeError):
        res.effects["total_swap_fees"] = 0  # type: ignore[index]


def test_dex_step_result_shape_is_fail_closed() -> None:
    empty = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
    )

    with pytest.raises(ValueError, match="accepted result requires exact DexEffects"):
        DexStepResult(ok=True, state=empty, effects=None)
    with pytest.raises(ValueError, match="rejected result cannot carry state"):
        DexStepResult(ok=False, state=empty, error="rejected")
    with pytest.raises(ValueError, match="non-empty error"):
        DexStepResult(ok=False, error="")
