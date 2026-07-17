import pytest

from src.core.zusd_liability_cover import (
    ZUSDFreeDebtLiabilityBreakdown,
    ZUSDLiabilityCoverCode,
    evaluate_zusd_free_debt_liability_cover,
)


def _breakdown(*, wallet_e8: int = 11, dex_pool_e8: int = 13) -> ZUSDFreeDebtLiabilityBreakdown:
    return ZUSDFreeDebtLiabilityBreakdown(
        wallet_e8=wallet_e8,
        dex_pool_e8=dex_pool_e8,
        perps_e8=17,
        protocol_fee_reserve_e8=19,
        staking_fee_pool_e8=23,
        host_fee_pool_e8=29,
    )


def test_liability_cover_accepts_exact_sum() -> None:
    breakdown = _breakdown()

    decision = evaluate_zusd_free_debt_liability_cover(
        breakdown=breakdown,
        actual_free_debt_e8=breakdown.total_e8,
    )

    assert decision.covered is True
    assert decision.code is ZUSDLiabilityCoverCode.COVERED


def test_liability_cover_rejects_mismatch_with_bound_amounts() -> None:
    breakdown = _breakdown()

    decision = evaluate_zusd_free_debt_liability_cover(
        breakdown=breakdown,
        actual_free_debt_e8=breakdown.total_e8 + 1,
    )

    assert decision.covered is False
    assert decision.code is ZUSDLiabilityCoverCode.FREE_DEBT_MISMATCH
    assert decision.expected_free_debt_e8 == breakdown.total_e8
    assert decision.actual_free_debt_e8 == breakdown.total_e8 + 1


@pytest.mark.parametrize("amount", range(12))
def test_wallet_to_pool_transfer_preserves_total(amount: int) -> None:
    before = _breakdown(wallet_e8=11, dex_pool_e8=13)
    after = _breakdown(
        wallet_e8=before.wallet_e8 - amount,
        dex_pool_e8=before.dex_pool_e8 + amount,
    )

    assert after.total_e8 == before.total_e8


@pytest.mark.parametrize("invalid", [True, 1.0, "1", None])
def test_breakdown_rejects_non_exact_integers(invalid: object) -> None:
    with pytest.raises(TypeError):
        ZUSDFreeDebtLiabilityBreakdown(
            wallet_e8=invalid,  # type: ignore[arg-type]
            dex_pool_e8=0,
            perps_e8=0,
            protocol_fee_reserve_e8=0,
            staking_fee_pool_e8=0,
            host_fee_pool_e8=0,
        )


def test_breakdown_rejects_negative_domain_amount() -> None:
    with pytest.raises(ValueError, match="dex_pool_e8 must be non-negative"):
        _breakdown(dex_pool_e8=-1)
