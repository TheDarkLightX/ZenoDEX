import pytest

from src.core.zusd_liquity_v1_risk_mode import (
    BPS_TO_E18,
    DECIMAL_PRECISION_E18,
    LIQUITY_V1_CCR_E18,
    MAX_U256,
    CollateralSourceAtoms,
    LiquityV1RiskDecision,
    LiquityV1RiskMode,
    LiquityV1SystemPools,
    PriceSourceE18,
    ZusdSourceAtoms,
    derive_liquity_v1_risk_mode,
)


def _pools(
    *,
    active_collateral: int,
    active_debt: int,
    default_collateral: int = 0,
    default_debt: int = 0,
) -> LiquityV1SystemPools:
    return LiquityV1SystemPools(
        active_collateral=CollateralSourceAtoms(active_collateral),
        active_debt=ZusdSourceAtoms(active_debt),
        default_collateral=CollateralSourceAtoms(default_collateral),
        default_debt=ZusdSourceAtoms(default_debt),
    )


@pytest.mark.parametrize(
    ("collateral", "debt", "expected_mode"),
    (
        (0, 0, LiquityV1RiskMode.NORMAL),
        (14_999, 10_000, LiquityV1RiskMode.RECOVERY),
        (15_000, 10_000, LiquityV1RiskMode.NORMAL),
        (15_001, 10_000, LiquityV1RiskMode.NORMAL),
    ),
)
def test_risk_mode_is_total_at_the_ccr_boundary(
    collateral: int,
    debt: int,
    expected_mode: LiquityV1RiskMode,
) -> None:
    decision = derive_liquity_v1_risk_mode(
        pools=_pools(active_collateral=collateral, active_debt=debt),
        price=PriceSourceE18(DECIMAL_PRECISION_E18),
    )

    assert decision.mode is expected_mode
    if debt == 0:
        assert decision.tcr_e18 == MAX_U256
    else:
        assert decision.tcr_e18 == collateral * DECIMAL_PRECISION_E18 // debt


def test_risk_mode_aggregates_only_active_and_default_pools() -> None:
    decision = derive_liquity_v1_risk_mode(
        pools=_pools(
            active_collateral=100,
            active_debt=100,
            default_collateral=50,
            default_debt=0,
        ),
        price=PriceSourceE18(DECIMAL_PRECISION_E18),
    )

    assert decision.total_collateral_source == CollateralSourceAtoms(150)
    assert decision.total_debt_source == ZusdSourceAtoms(100)
    assert decision.tcr_e18 == LIQUITY_V1_CCR_E18
    assert decision.mode is LiquityV1RiskMode.NORMAL


def test_non_risk_custody_cannot_enter_the_input_type() -> None:
    with pytest.raises(TypeError, match="unexpected keyword argument"):
        LiquityV1SystemPools(
            active_collateral=CollateralSourceAtoms(100),
            active_debt=ZusdSourceAtoms(100),
            default_collateral=CollateralSourceAtoms(0),
            default_debt=ZusdSourceAtoms(0),
            stability_pool_collateral=CollateralSourceAtoms(10_000),  # type: ignore[call-arg]
        )


def test_exact_source_ratio_is_not_first_floored_to_basis_points() -> None:
    collateral = 1_000_000_010_000_000_000
    debt = 1_000_000_000_000_000_000
    decision = derive_liquity_v1_risk_mode(
        pools=_pools(active_collateral=collateral, active_debt=debt),
        price=PriceSourceE18(DECIMAL_PRECISION_E18),
    )

    assert decision.tcr_e18 == 1_000_000_010_000_000_000
    assert decision.tcr_e18 > 10_000 * BPS_TO_E18


def test_nominal_source_types_are_not_interchangeable() -> None:
    with pytest.raises(TypeError, match="active_collateral must be CollateralSourceAtoms"):
        LiquityV1SystemPools(
            active_collateral=ZusdSourceAtoms(1),  # type: ignore[arg-type]
            active_debt=ZusdSourceAtoms(1),
            default_collateral=CollateralSourceAtoms(0),
            default_debt=ZusdSourceAtoms(0),
        )


def test_aggregate_u256_overflow_rejects() -> None:
    pools = _pools(
        active_collateral=MAX_U256,
        active_debt=0,
        default_collateral=1,
        default_debt=0,
    )
    with pytest.raises(ValueError, match="total_system_collateral_source exceeds U256"):
        derive_liquity_v1_risk_mode(
            pools=pools,
            price=PriceSourceE18(DECIMAL_PRECISION_E18),
        )


def test_forged_decision_mode_is_unrepresentable() -> None:
    with pytest.raises(ValueError, match="risk mode is inconsistent"):
        LiquityV1RiskDecision(
            total_collateral_source=CollateralSourceAtoms(15_000),
            total_debt_source=ZusdSourceAtoms(10_000),
            price_source_e18=PriceSourceE18(DECIMAL_PRECISION_E18),
            collateral_value_source=15_000,
            tcr_e18=LIQUITY_V1_CCR_E18,
            mode=LiquityV1RiskMode.RECOVERY,
        )
