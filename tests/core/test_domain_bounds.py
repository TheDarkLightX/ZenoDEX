from __future__ import annotations

import pytest

from src.core.batch_clearing import compute_settlement, validate_settlement
from src.core.cpmm import swap_exact_in, swap_exact_in_with_protocol_fee, swap_exact_out
from src.core.domain_limits import (
    DEX_LP_AMOUNT_MAX,
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    require_int_range,
)
from src.core.liquidity import add_liquidity, create_pool, remove_liquidity
from src.core.settlement import FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_swap_exact_in_rejects_post_update_reserve_overflow() -> None:
    with pytest.raises(ValueError, match="swap would exceed reserve_in domain max"):
        swap_exact_in(
            reserve_in=DEX_POOL_RESERVE_MAX,
            reserve_out=DEX_POOL_RESERVE_MAX,
            amount_in=2,
            fee_bps=0,
        )


def test_swap_exact_in_protocol_fee_uses_actual_post_reserve_domain() -> None:
    quote = swap_exact_in_with_protocol_fee(
        reserve_in=DEX_POOL_RESERVE_MAX - 1,
        reserve_out=DEX_POOL_RESERVE_MAX,
        amount_in=2,
        fee_bps=5_000,
        protocol_fee_share_bps=10_000,
    )

    assert quote.fee_total == 1
    assert quote.protocol_fee == 1
    assert quote.amount_out == 1
    assert quote.new_reserve_in == DEX_POOL_RESERVE_MAX


def test_swap_exact_out_rejects_post_update_reserve_overflow() -> None:
    with pytest.raises(ValueError, match="swap would exceed reserve_in domain max"):
        swap_exact_out(
            reserve_in=DEX_POOL_RESERVE_MAX,
            reserve_out=DEX_POOL_RESERVE_MAX,
            amount_out=1,
            fee_bps=0,
        )


def test_swap_exact_out_rejects_computed_amount_in_overflow() -> None:
    with pytest.raises(ValueError, match=f"amount_in exceeds kernel domain max {DEX_SWAP_AMOUNT_MAX}"):
        swap_exact_out(
            reserve_in=DEX_POOL_RESERVE_MAX,
            reserve_out=2,
            amount_out=1,
            fee_bps=30,
        )


class _ExecutableInt(int):
    def __mul__(self, _other: object) -> int:
        return 0


def test_consensus_domain_rejects_executable_int_subclasses() -> None:
    value = _ExecutableInt(100)

    with pytest.raises(TypeError, match="value must be an int"):
        require_int_range("value", value, minimum=0)
    with pytest.raises(TypeError, match="amount_in must be an int"):
        swap_exact_in(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_in=value,
            fee_bps=30,
        )


def test_add_liquidity_rejects_negative_direct_min_bounds() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _lp = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=100_000,
        amount1=100_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    with pytest.raises(ValueError, match="amount0_min must be >= 0"):
        add_liquidity(
            pool_state=pool,
            amount0_desired=1_000,
            amount1_desired=1_000,
            amount0_min=-1,
            amount1_min=0,
        )


def test_remove_liquidity_rejects_negative_direct_min_bounds() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _lp = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=100_000,
        amount1=100_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    with pytest.raises(ValueError, match="amount0_min must be >= 0"):
        remove_liquidity(
            pool_state=pool,
            lp_amount=1,
            amount0_min=-1,
            amount1_min=0,
        )


def test_compute_settlement_rejects_non_integer_create_pool_params_without_crashing() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 1_000_000)
    balances.set(pk, asset1, 1_000_000)

    settlement = compute_settlement(
        [
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
                    "amount0": "1000",
                    "amount1": 1000,
                },
            )
        ],
        {},
        balances,
        LPTable(),
    )

    assert len(settlement.fills) == 1
    assert settlement.fills[0].action == FillAction.REJECT
    assert settlement.fills[0].reason == "INVALID_PARAMS"
    ok, err = validate_settlement(settlement, balances, {}, LPTable())
    assert ok, err


def test_compute_settlement_rejects_oversized_create_pool_params() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, DEX_LP_AMOUNT_MAX + 10)
    balances.set(pk, asset1, DEX_LP_AMOUNT_MAX + 10)

    settlement = compute_settlement(
        [
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.CREATE_POOL,
                intent_id=_iid(2),
                sender_pubkey=pk,
                deadline=9999999999,
                fields={
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": 30,
                    "amount0": DEX_LP_AMOUNT_MAX + 1,
                    "amount1": 1000,
                },
            )
        ],
        {},
        balances,
        LPTable(),
    )

    assert len(settlement.fills) == 1
    assert settlement.fills[0].action == FillAction.REJECT
    assert settlement.fills[0].reason == "INVALID_PARAMS"
