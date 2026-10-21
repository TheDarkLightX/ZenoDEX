import pytest

from src.core.zusd_owner_close_xqr import (
    COLLATERAL_E18_TO_CUSTODY_E8_FACTOR,
    MAX_U256,
    CollateralE18Atoms,
    CustodyE8Atoms,
    NoPhysicalTransfer,
    OwnerClaimE18Atoms,
    OwnerCloseCustodyMode,
    OwnerCloseProjectionCandidate,
    OwnerCloseProjectionInput,
    OwnerCloseProjectionReject,
    OwnerCloseProjectionViolation,
    PhysicalTransferE8,
    project_owner_close_xqr,
)

K = COLLATERAL_E18_TO_CUSTODY_E8_FACTOR


def _projection_input(
    *,
    x: int,
    active_shadow: int = 100 * K,
    accounted: int = 100,
    observed: int = 100,
    external: int = 7,
    claim: int = 11,
    quarantine: int = 13,
    mode: OwnerCloseCustodyMode = OwnerCloseCustodyMode.BALANCED,
) -> OwnerCloseProjectionInput:
    return OwnerCloseProjectionInput(
        closed_collateral_e18=CollateralE18Atoms(x),
        active_pool_shadow_e18=CollateralE18Atoms(active_shadow),
        accounted_custody_e8=CustodyE8Atoms(accounted),
        observed_custody_e8=CustodyE8Atoms(observed),
        owner_external_e8=CustodyE8Atoms(external),
        owner_claim_e18=OwnerClaimE18Atoms(claim),
        quarantine_e8=CustodyE8Atoms(quarantine),
        custody_mode=mode,
    )


def test_exactly_divisible_close_has_zero_residue() -> None:
    outcome = project_owner_close_xqr(_projection_input(x=3 * K))

    assert isinstance(outcome, OwnerCloseProjectionCandidate)
    assert outcome.physical_quotient_e8 == CustodyE8Atoms(3)
    assert outcome.exact_residue_e18 == OwnerClaimE18Atoms(0)
    assert outcome.active_pool_shadow_after_e18 == CollateralE18Atoms(97 * K)
    assert outcome.accounted_custody_after_e8 == CustodyE8Atoms(97)
    assert outcome.observed_custody_after_e8 == CustodyE8Atoms(97)
    assert outcome.owner_external_after_e8 == CustodyE8Atoms(10)
    assert outcome.owner_claim_after_e18 == OwnerClaimE18Atoms(11)
    assert outcome.quarantine_after_e8 == CustodyE8Atoms(13)
    assert outcome.physical_directive == PhysicalTransferE8(CustodyE8Atoms(3))
    assert outcome.is_commit_receipt is False


def test_close_pays_quotient_and_preserves_residue() -> None:
    residue = K - 1
    outcome = project_owner_close_xqr(_projection_input(x=3 * K + residue))

    assert isinstance(outcome, OwnerCloseProjectionCandidate)
    assert outcome.physical_quotient_e8 == CustodyE8Atoms(3)
    assert outcome.exact_residue_e18 == OwnerClaimE18Atoms(residue)
    assert outcome.owner_external_after_e8 == CustodyE8Atoms(10)
    assert outcome.owner_claim_after_e18 == OwnerClaimE18Atoms(11 + residue)
    assert outcome.closed_collateral_e18.value == (
        K * outcome.physical_quotient_e8.value + outcome.exact_residue_e18.value
    )


@pytest.mark.parametrize("x", [1, 7, K - 1])
def test_sub_e8_close_creates_claim_without_adapter_transfer(x: int) -> None:
    before = _projection_input(x=x)
    outcome = project_owner_close_xqr(before)

    assert isinstance(outcome, OwnerCloseProjectionCandidate)
    assert outcome.physical_quotient_e8 == CustodyE8Atoms(0)
    assert outcome.exact_residue_e18 == OwnerClaimE18Atoms(x)
    assert type(outcome.physical_directive) is NoPhysicalTransfer
    assert outcome.accounted_custody_after_e8 == before.accounted_custody_e8
    assert outcome.observed_custody_after_e8 == before.observed_custody_e8
    assert outcome.owner_external_after_e8 == before.owner_external_e8
    assert outcome.owner_claim_after_e18 == OwnerClaimE18Atoms(11 + x)


def test_zero_collateral_is_a_total_no_transfer_projection() -> None:
    before = _projection_input(x=0)
    outcome = project_owner_close_xqr(before)

    assert isinstance(outcome, OwnerCloseProjectionCandidate)
    assert type(outcome.physical_directive) is NoPhysicalTransfer
    assert outcome.physical_quotient_e8 == CustodyE8Atoms(0)
    assert outcome.exact_residue_e18 == OwnerClaimE18Atoms(0)
    assert outcome.active_pool_shadow_after_e18 == before.active_pool_shadow_e18
    assert outcome.owner_claim_after_e18 == before.owner_claim_e18


def test_deficit_frozen_blocks_successor_arithmetic() -> None:
    outcome = project_owner_close_xqr(
        _projection_input(
            x=3 * K + 1,
            active_shadow=0,
            accounted=0,
            observed=0,
            external=MAX_U256,
            claim=MAX_U256,
            mode=OwnerCloseCustodyMode.DEFICIT_FROZEN,
        )
    )

    assert isinstance(outcome, OwnerCloseProjectionReject)
    assert outcome.violations == (OwnerCloseProjectionViolation.DEFICIT_FROZEN,)


def test_all_independent_arithmetic_failures_survive() -> None:
    outcome = project_owner_close_xqr(
        _projection_input(
            x=K + 1,
            active_shadow=0,
            accounted=0,
            observed=0,
            external=MAX_U256,
            claim=MAX_U256,
        )
    )

    assert isinstance(outcome, OwnerCloseProjectionReject)
    assert outcome.violations == (
        OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW,
        OwnerCloseProjectionViolation.ACCOUNTED_CUSTODY_UNDERFLOW,
        OwnerCloseProjectionViolation.OBSERVED_CUSTODY_UNDERFLOW,
        OwnerCloseProjectionViolation.OWNER_EXTERNAL_OVERFLOW,
        OwnerCloseProjectionViolation.OWNER_CLAIM_OVERFLOW,
    )
    assert outcome.primary_violation is OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW


@pytest.mark.parametrize(
    ("field", "kwargs", "violation"),
    (
        (
            "active shadow",
            {"x": K, "active_shadow": K - 1},
            OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW,
        ),
        (
            "accounted custody",
            {"x": K, "accounted": 0},
            OwnerCloseProjectionViolation.ACCOUNTED_CUSTODY_UNDERFLOW,
        ),
        (
            "observed custody",
            {"x": K, "observed": 0},
            OwnerCloseProjectionViolation.OBSERVED_CUSTODY_UNDERFLOW,
        ),
        (
            "owner external",
            {"x": K, "external": MAX_U256},
            OwnerCloseProjectionViolation.OWNER_EXTERNAL_OVERFLOW,
        ),
        (
            "owner claim",
            {"x": 1, "claim": MAX_U256},
            OwnerCloseProjectionViolation.OWNER_CLAIM_OVERFLOW,
        ),
    ),
)
def test_each_arithmetic_failure_is_typed(
    field: str,
    kwargs: dict[str, int],
    violation: OwnerCloseProjectionViolation,
) -> None:
    del field
    outcome = project_owner_close_xqr(_projection_input(**kwargs))

    assert isinstance(outcome, OwnerCloseProjectionReject)
    assert violation in outcome.violations


def test_surplus_quarantine_is_preserved_exactly() -> None:
    outcome = project_owner_close_xqr(
        _projection_input(
            x=2 * K + 3,
            quarantine=99,
            mode=OwnerCloseCustodyMode.SURPLUS_QUARANTINED,
        )
    )

    assert isinstance(outcome, OwnerCloseProjectionCandidate)
    assert outcome.quarantine_before_e8 == CustodyE8Atoms(99)
    assert outcome.quarantine_after_e8 == CustodyE8Atoms(99)


def test_nominal_units_are_not_interchangeable() -> None:
    with pytest.raises(TypeError, match="closed_collateral_e18 must be CollateralE18Atoms"):
        OwnerCloseProjectionInput(
            closed_collateral_e18=CustodyE8Atoms(1),  # type: ignore[arg-type]
            active_pool_shadow_e18=CollateralE18Atoms(K),
            accounted_custody_e8=CustodyE8Atoms(1),
            observed_custody_e8=CustodyE8Atoms(1),
            owner_external_e8=CustodyE8Atoms(0),
            owner_claim_e18=OwnerClaimE18Atoms(0),
            quarantine_e8=CustodyE8Atoms(0),
            custody_mode=OwnerCloseCustodyMode.BALANCED,
        )


def test_forged_candidate_successor_is_unrepresentable() -> None:
    with pytest.raises(ValueError, match="owner-claim successor is inconsistent"):
        OwnerCloseProjectionCandidate(
            closed_collateral_e18=CollateralE18Atoms(K + 1),
            physical_quotient_e8=CustodyE8Atoms(1),
            exact_residue_e18=OwnerClaimE18Atoms(1),
            active_pool_shadow_before_e18=CollateralE18Atoms(10 * K),
            active_pool_shadow_after_e18=CollateralE18Atoms(9 * K - 1),
            accounted_custody_before_e8=CustodyE8Atoms(10),
            accounted_custody_after_e8=CustodyE8Atoms(9),
            observed_custody_before_e8=CustodyE8Atoms(10),
            observed_custody_after_e8=CustodyE8Atoms(9),
            owner_external_before_e8=CustodyE8Atoms(0),
            owner_external_after_e8=CustodyE8Atoms(1),
            owner_claim_before_e18=OwnerClaimE18Atoms(0),
            owner_claim_after_e18=OwnerClaimE18Atoms(0),
            quarantine_before_e8=CustodyE8Atoms(0),
            quarantine_after_e8=CustodyE8Atoms(0),
            physical_directive=PhysicalTransferE8(CustodyE8Atoms(1)),
        )


def test_rejection_violation_vector_must_be_canonical() -> None:
    with pytest.raises(ValueError, match="canonically ordered"):
        OwnerCloseProjectionReject(
            violations=(
                OwnerCloseProjectionViolation.OWNER_CLAIM_OVERFLOW,
                OwnerCloseProjectionViolation.ACTIVE_POOL_SHADOW_UNDERFLOW,
            ),
            closed_collateral_e18=CollateralE18Atoms(K + 1),
            physical_quotient_e8=CustodyE8Atoms(1),
            exact_residue_e18=OwnerClaimE18Atoms(1),
        )
