from __future__ import annotations

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDState,
    ZUSDVault,
    check_invariants,
    check_multi_invariants,
    step,
    step_multi,
)


def _multi_state(*, total_e8: int, free_e8: int, max_supply_e8: int) -> ZUSDMultiState:
    debt_a = 700 * E8
    debt_b = total_e8 - debt_a
    assert debt_b >= 0
    return ZUSDMultiState(
        now_epoch=0,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=E8,
        price_pending_e8=E8,
        vault_a=ZUSDVault(collateral_e8=10_000 * E8, debt_e8=debt_a),
        vault_b=ZUSDVault(collateral_e8=10_000 * E8, debt_e8=debt_b),
        free_debt_e8=free_e8,
        sp_debt_e8=total_e8 - free_e8,
        max_debt_e8=1_000 * E8,
        max_debt_supply_e8=max_supply_e8,
    )


def test_multi_mint_counts_stability_pool_debt_against_global_cap() -> None:
    state = _multi_state(
        total_e8=1_400 * E8,
        free_e8=100 * E8,
        max_supply_e8=1_500 * E8,
    )

    result = step_multi(
        state,
        ZUSDMultiCommand(
            tag="mint_zusd",
            args={"vault": "b", "amount_e8": 200 * E8},
        ),
    )

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "mint exceeds max_debt_supply_e8"
    assert state.vault_b.debt_e8 == 700 * E8
    assert state.free_debt_e8 == 100 * E8
    assert state.sp_debt_e8 == 1_300 * E8


def test_multi_mint_accepts_exact_global_cap_boundary() -> None:
    state = _multi_state(
        total_e8=1_400 * E8,
        free_e8=100 * E8,
        max_supply_e8=1_500 * E8,
    )

    result = step_multi(
        state,
        ZUSDMultiCommand(
            tag="mint_zusd",
            args={"vault": "b", "amount_e8": 100 * E8},
        ),
    )

    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.vault_b.debt_e8 == 800 * E8
    assert result.state.free_debt_e8 == 200 * E8
    assert result.state.sp_debt_e8 == 1_300 * E8
    assert result.state.free_debt_e8 + result.state.sp_debt_e8 == 1_500 * E8
    assert check_multi_invariants(result.state) == []


def test_multi_invariant_detects_forged_total_debt_above_cap() -> None:
    state = _multi_state(
        total_e8=1_600 * E8,
        free_e8=300 * E8,
        max_supply_e8=1_500 * E8,
    )

    assert "inv_total_debt_cap" in check_multi_invariants(state)


def test_single_invariant_uses_total_debt_value_for_cap() -> None:
    state = ZUSDState(
        debt_e8=1_501 * E8,
        free_debt_e8=1 * E8,
        sp_debt_e8=1_500 * E8,
        max_debt_e8=1_500 * E8,
        max_debt_supply_e8=1_500 * E8,
        min_debt_open_e8=100 * E8,
    )

    assert "inv_total_debt_cap" in check_invariants(state)


def test_stability_pool_transfer_at_cap_preserves_total_debt() -> None:
    state = ZUSDState(
        now_epoch=0,
        oracle_seen=True,
        oracle_last_update_epoch=0,
        price_e8=2 * E8,
        price_pending_e8=2 * E8,
        collateral_e8=10_000 * E8,
        debt_e8=1_500 * E8,
        free_debt_e8=200 * E8,
        sp_debt_e8=1_300 * E8,
        max_debt_e8=1_500 * E8,
        max_debt_supply_e8=1_500 * E8,
    )

    result = step(
        state,
        ZUSDCommand(tag="deposit_sp", args={"amount_e8": 100 * E8}),
    )

    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.debt_e8 == 1_500 * E8
    assert result.state.free_debt_e8 == 100 * E8
    assert result.state.sp_debt_e8 == 1_400 * E8
    assert check_invariants(result.state) == []
