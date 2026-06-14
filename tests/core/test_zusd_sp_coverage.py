"""Unit tests for the zUSD stability-pool absorption-coverage monitor.

These pin the read-only advisory monitor (``src/core/zusd_sp_coverage.py``,
recommendation R7c) to the kernel: the monitor's ``coverage_ok`` prediction must
equal the real ``zusd`` Python-reference liquidation-refusal decision.
"""

from __future__ import annotations

from src.core.zusd import (
    E8,
    ZUSDCommand,
    ZUSDState,
    _step_python,
    check_invariants,
)
from src.core.zusd_sp_coverage import (
    SP_ABSORPTION_COVERAGE_SCHEMA,
    liquidation_blocked_by_sp,
    sp_absorption_coverage,
    sp_absorption_coverage_clear,
)

SP_REFUSAL = "stability pool cannot absorb debt"


def _seen_vault(
    *,
    collateral_e8: int,
    debt_e8: int,
    free_debt_e8: int,
    sp_debt_e8: int,
    price_e8: int = E8,
) -> ZUSDState:
    state = ZUSDState(
        oracle_seen=True,
        price_e8=price_e8,
        price_pending_e8=price_e8,
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        free_debt_e8=free_debt_e8,
        sp_debt_e8=sp_debt_e8,
    )
    # Every constructed scenario must be a legal, reachable state.
    assert check_invariants(state) == []
    return state


def _liquidate(state: ZUSDState):
    return _step_python(state, ZUSDCommand(tag="liquidate", args={}))


def test_covered_under_mcr_vault_liquidates_cleanly() -> None:
    state = _seen_vault(
        collateral_e8=1_000 * E8,
        debt_e8=1_000 * E8,
        free_debt_e8=0,
        sp_debt_e8=1_000 * E8,
    )
    cov = sp_absorption_coverage(state)
    assert cov.schema == SP_ABSORPTION_COVERAGE_SCHEMA
    assert cov.vault_under_mcr is True
    assert cov.coverage_ok is True
    assert cov.liquidation_blocked_by_sp is False
    assert cov.classification == "covered"
    assert cov.absorption_shortfall_e8 == 0
    # Faithful to the kernel: the liquidation actually succeeds.
    assert _liquidate(state).ok is True


def test_under_mcr_uninsured_vault_is_the_blocked_disaster_precursor() -> None:
    state = _seen_vault(
        collateral_e8=1_000 * E8,
        debt_e8=1_000 * E8,
        free_debt_e8=400 * E8,
        sp_debt_e8=600 * E8,
    )
    cov = sp_absorption_coverage(state)
    assert cov.vault_under_mcr is True
    assert cov.coverage_ok is False
    assert cov.liquidation_blocked_by_sp is True
    assert cov.classification == "liquidation_blocked"
    assert cov.severity == 3
    # The shortfall is exactly the uninsured (free) debt.
    assert cov.absorption_shortfall_e8 == 400 * E8
    # Faithful to the kernel: the monitor predicts the exact refusal.
    result = _liquidate(state)
    assert result.ok is False
    assert result.error == SP_REFUSAL
    assert sp_absorption_coverage_clear(state) is False
    assert liquidation_blocked_by_sp(state) is True


def test_above_mcr_partially_backed_vault_is_uninsurable_region_not_blocked() -> None:
    state = _seen_vault(
        collateral_e8=2_000 * E8,
        debt_e8=1_000 * E8,
        free_debt_e8=400 * E8,
        sp_debt_e8=600 * E8,
    )
    cov = sp_absorption_coverage(state)
    assert cov.vault_under_mcr is False
    assert cov.coverage_ok is False
    assert cov.liquidation_blocked_by_sp is False
    assert cov.classification == "uninsurable_region"
    assert cov.severity == 2
    # Not yet a disaster: the kernel refuses for the MCR reason, not absorption.
    result = _liquidate(state)
    assert result.ok is False
    assert result.error != SP_REFUSAL
    assert sp_absorption_coverage_clear(state) is True


def test_no_debt_and_indeterminate_oracle_are_not_blocked() -> None:
    no_debt = _seen_vault(collateral_e8=0, debt_e8=0, free_debt_e8=0, sp_debt_e8=0)
    cov_no_debt = sp_absorption_coverage(no_debt)
    assert cov_no_debt.classification == "no_debt"
    assert cov_no_debt.liquidation_blocked_by_sp is False
    assert cov_no_debt.absorption_shortfall_e8 == 0

    unseen = ZUSDState(
        oracle_seen=False,
        collateral_e8=1_000 * E8,
        debt_e8=1_000 * E8,
        free_debt_e8=1_000 * E8,
        sp_debt_e8=0,
    )
    assert check_invariants(unseen) == []
    cov_unseen = sp_absorption_coverage(unseen)
    assert cov_unseen.oracle_evaluable is False
    assert cov_unseen.classification == "indeterminate_oracle"
    assert cov_unseen.liquidation_blocked_by_sp is False


def test_coverage_ok_equals_kernel_refusal_across_the_split_sweep() -> None:
    """For under-MCR vaults, coverage_ok must equal the kernel's liquidate ok.

    Sweep the free/sp debt split at fixed total debt while the vault is under
    MCR (collateral == debt at price 1.0). The monitor's coverage prediction is
    checked against the actual kernel decision at every split.
    """
    debt = 1_000 * E8
    for free_debt in range(0, debt + 1, 50 * E8):
        sp_debt = debt - free_debt
        state = _seen_vault(
            collateral_e8=debt,  # collateral == debt => under MCR (110%)
            debt_e8=debt,
            free_debt_e8=free_debt,
            sp_debt_e8=sp_debt,
        )
        cov = sp_absorption_coverage(state)
        assert cov.vault_under_mcr is True
        result = _liquidate(state)
        # The binding: coverage_ok iff the kernel liquidates.
        assert cov.coverage_ok is result.ok
        if not result.ok:
            assert result.error == SP_REFUSAL
            assert cov.liquidation_blocked_by_sp is True
        # Shortfall tracks uninsured debt exactly.
        assert cov.absorption_shortfall_e8 == free_debt


def test_full_sp_backing_is_the_only_covered_split() -> None:
    """coverage_ok holds iff free (uninsured) debt is zero, by conservation."""
    debt = 500 * E8
    covered = _seen_vault(
        collateral_e8=2_000 * E8,
        debt_e8=debt,
        free_debt_e8=0,
        sp_debt_e8=debt,
    )
    assert sp_absorption_coverage(covered).coverage_ok is True

    one_unit_uninsured = _seen_vault(
        collateral_e8=2_000 * E8,
        debt_e8=debt,
        free_debt_e8=1,
        sp_debt_e8=debt - 1,
    )
    assert sp_absorption_coverage(one_unit_uninsured).coverage_ok is False
