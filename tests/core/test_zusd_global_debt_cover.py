import pytest

from src.core.zusd_global_debt_cover import (
    ZUSDGlobalDebtCoverDecision,
    ZUSDGlobalDebtCoverViolation,
    evaluate_zusd_global_debt_cover,
)
from src.core.zusd_liability_cover import ZUSDFreeDebtLiabilityBreakdown


def _free_breakdown() -> ZUSDFreeDebtLiabilityBreakdown:
    return ZUSDFreeDebtLiabilityBreakdown(
        wallet_e8=11,
        dex_pool_e8=13,
        perps_e8=17,
        protocol_fee_reserve_e8=19,
        staking_fee_pool_e8=23,
        host_fee_pool_e8=29,
        gas_pool_reserve_e8=31,
    )


def test_global_cover_accepts_all_component_equalities() -> None:
    free = _free_breakdown()
    sp = 37
    decision = evaluate_zusd_global_debt_cover(
        free_breakdown=free,
        stability_pool_escrow_e8=sp,
        core_free_debt_e8=free.total_e8,
        core_sp_debt_e8=sp,
        core_total_debt_e8=free.total_e8 + sp,
    )

    assert decision.covered is True
    assert decision.violations == ()
    assert decision.external_global_liabilities_e8 == free.total_e8 + sp


def test_global_cover_retains_every_independent_violation() -> None:
    decision = evaluate_zusd_global_debt_cover(
        free_breakdown=_free_breakdown(),
        stability_pool_escrow_e8=37,
        core_free_debt_e8=1,
        core_sp_debt_e8=2,
        core_total_debt_e8=4,
    )

    assert decision.violations == (
        ZUSDGlobalDebtCoverViolation.FREE_DEBT_LIABILITY_MISMATCH,
        ZUSDGlobalDebtCoverViolation.STABILITY_POOL_CUSTODY_MISMATCH,
        ZUSDGlobalDebtCoverViolation.CORE_DEBT_SPLIT_MISMATCH,
        ZUSDGlobalDebtCoverViolation.GLOBAL_DEBT_LIABILITY_MISMATCH,
    )


def test_global_cover_distinguishes_core_split_from_external_cover() -> None:
    free = _free_breakdown()
    decision = evaluate_zusd_global_debt_cover(
        free_breakdown=free,
        stability_pool_escrow_e8=7,
        core_free_debt_e8=free.total_e8,
        core_sp_debt_e8=7,
        core_total_debt_e8=free.total_e8 + 8,
    )

    assert decision.violations == (
        ZUSDGlobalDebtCoverViolation.CORE_DEBT_SPLIT_MISMATCH,
        ZUSDGlobalDebtCoverViolation.GLOBAL_DEBT_LIABILITY_MISMATCH,
    )


def test_forged_decision_with_missing_violation_is_unrepresentable() -> None:
    free = _free_breakdown()
    with pytest.raises(ValueError, match="global debt-cover decision is inconsistent"):
        ZUSDGlobalDebtCoverDecision(
            violations=(),
            external_free_liabilities_e8=free.total_e8,
            external_sp_custody_e8=7,
            core_free_debt_e8=free.total_e8 + 1,
            core_sp_debt_e8=7,
            core_total_debt_e8=free.total_e8 + 8,
        )


def test_violation_vector_must_be_canonical_and_unique() -> None:
    with pytest.raises(ValueError, match="canonically ordered"):
        ZUSDGlobalDebtCoverDecision(
            violations=(
                ZUSDGlobalDebtCoverViolation.GLOBAL_DEBT_LIABILITY_MISMATCH,
                ZUSDGlobalDebtCoverViolation.FREE_DEBT_LIABILITY_MISMATCH,
            ),
            external_free_liabilities_e8=0,
            external_sp_custody_e8=0,
            core_free_debt_e8=1,
            core_sp_debt_e8=0,
            core_total_debt_e8=0,
        )
