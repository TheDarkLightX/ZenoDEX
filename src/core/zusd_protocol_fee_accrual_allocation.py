"""Allocate one exact zUSD borrowing-fee occurrence when it accrues.

The candidate composes the current scalar fee claim with exactly one SRGD-v1
transition and a configuration-qualified role-claim update.  It intentionally
accepts only a self-consistent configuration claim.  Exact-state activation,
authenticated borrow lineage, publication, and value transfer remain later
authority boundaries.
"""

from __future__ import annotations

from typing import NamedTuple, cast

from .fcis_fee_apportionment_allocator import apply_fee_apportionment_v2
from .fcis_fee_apportionment_codec import canonical_sha256_fcis_fee_apportionment_v2
from .fcis_fee_apportionment_values import (
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeApportionmentTransitionRejectV2,
)
from .fcis_fee_distribution_configuration_values import (
    ValidatedFeeDistributionConfigurationClaimV2,
)
from .fcis_fee_distribution_configuration_verification import (
    revalidate_fee_distribution_configuration_claim_v2,
)
from .zusd_protocol_fee_accrual_allocation_values import (
    ZUSDProtocolFeeAccrualAllocationCandidateV1,
    ZUSDProtocolFeeAccrualAllocationRejectCodeV1,
    ZUSDProtocolFeeAccrualAllocationRejectV1,
    ZUSDProtocolFeeAccrualAllocationResultV1,
    ZUSDProtocolFeeAccrualAllocationSourceV1,
    _zusd_protocol_fee_accrual_allocation_candidate_v1,
)
from .zusd_protocol_fee_claim import (
    ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
    ZUSDProtocolFeeClaimRejectV1,
    ZUSDProtocolFeeClaimTransitionV1,
    ZUSDProtocolFeeClaimV1,
    accrue_zusd_protocol_fee_claim_v1,
    decode_zusd_protocol_fee_claim_v1,
    verify_zusd_protocol_fee_claim_transition_v1,
)
from .zusd_protocol_fee_role_claims import (
    ZUSDProtocolFeeRoleClaimStateV1,
    accrue_zusd_protocol_fee_role_claim_state_v1,
    revalidate_zusd_protocol_fee_role_claim_state_v1,
)


def _reject_v1(
    code: ZUSDProtocolFeeAccrualAllocationRejectCodeV1,
    *path: str,
) -> ZUSDProtocolFeeAccrualAllocationRejectV1:
    return ZUSDProtocolFeeAccrualAllocationRejectV1(code, tuple(path))


def _scalar_claim_is_valid_v1(value: object) -> bool:
    if type(value) is not ZUSDProtocolFeeClaimV1:
        return False
    claim = cast(ZUSDProtocolFeeClaimV1, value)
    try:
        rebuilt = decode_zusd_protocol_fee_claim_v1(
            {
                "schema": ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
                "version": 1,
                "asset_id": claim.asset_id,
                "custody_pubkey": claim.custody_pubkey,
                "outstanding_e8": claim.outstanding_e8,
                "accrued_cumulative_e8": claim.accrued_cumulative_e8,
            }
        )
    except (TypeError, ValueError, OverflowError, ArithmeticError):
        return False
    return rebuilt == claim


def _apportionment_state_is_valid_v1(value: object) -> bool:
    if type(value) is not CommittedFeeApportionmentStateV2:
        return False
    state = cast(CommittedFeeApportionmentStateV2, value)
    try:
        state.__post_init__()
    except (TypeError, ValueError, OverflowError, ArithmeticError):
        return False
    return True


def _apportionment_state_digest_v1(
    value: CommittedFeeApportionmentStateV2,
) -> str:
    return canonical_sha256_fcis_fee_apportionment_v2(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        value,
    )


class _ValidatedAccrualSourceV1(NamedTuple):
    scalar_claim: ZUSDProtocolFeeClaimV1
    role_claims: ZUSDProtocolFeeRoleClaimStateV1
    apportionment_state: CommittedFeeApportionmentStateV2
    configuration: ValidatedFeeDistributionConfigurationClaimV2
    amount_e8: int


class _AccrualArithmeticV1(NamedTuple):
    scalar_transition: ZUSDProtocolFeeClaimTransitionV1
    contribution: FeeAmountCandidateV2
    apportionment_transition: FeeApportionmentTransitionOkV2


def _validate_candidate_components_v1(
    candidate: ZUSDProtocolFeeAccrualAllocationCandidateV1,
) -> None:
    if not revalidate_fee_distribution_configuration_claim_v2(candidate.validated_configuration):
        raise ValueError("candidate configuration is invalid")
    if not _scalar_claim_is_valid_v1(candidate.scalar_claim_transition.pre_state):
        raise ValueError("candidate scalar pre-claim is invalid")
    scalar_verified = verify_zusd_protocol_fee_claim_transition_v1(
        expected_kind="accrue",
        expected_asset_id=candidate.scalar_claim_transition.pre_state.asset_id,
        expected_custody_pubkey=candidate.scalar_claim_transition.pre_state.custody_pubkey,
        expected_pre_state=candidate.scalar_claim_transition.pre_state,
        expected_amount_e8=candidate.scalar_claim_transition.amount_e8,
        transition=candidate.scalar_claim_transition,
    )
    if scalar_verified is not candidate.scalar_claim_transition:
        raise ValueError("candidate scalar transition is invalid")
    if type(candidate.fee_contribution) is not FeeAmountCandidateV2:
        raise TypeError("candidate fee contribution must be exact")
    candidate.fee_contribution.__post_init__()
    if not revalidate_zusd_protocol_fee_role_claim_state_v1(candidate.pre_role_claims):
        raise ValueError("candidate pre-role claims are invalid")
    if not revalidate_zusd_protocol_fee_role_claim_state_v1(candidate.post_role_claims):
        raise ValueError("candidate post-role claims are invalid")
    if not _apportionment_state_is_valid_v1(candidate.pre_apportionment_state):
        raise ValueError("candidate pre-apportionment state is invalid")
    if type(candidate.apportionment_transition) is not FeeApportionmentTransitionOkV2:
        raise TypeError("candidate apportionment transition must be exact")
    candidate.apportionment_transition._revalidate()


def _validate_candidate_identity_and_partition_v1(
    candidate: ZUSDProtocolFeeAccrualAllocationCandidateV1,
) -> None:
    configuration = candidate.validated_configuration
    scalar_transition = candidate.scalar_claim_transition
    pre_roles = candidate.pre_role_claims
    post_roles = candidate.post_role_claims
    if (
        pre_roles.fee_distribution_domain_id != configuration.body.fee_distribution_domain_id
        or pre_roles.asset_id != scalar_transition.pre_state.asset_id
        or pre_roles.scalar_claim_custody_pubkey != scalar_transition.pre_state.custody_pubkey
        or post_roles.fee_distribution_domain_id != configuration.body.fee_distribution_domain_id
        or post_roles.asset_id != scalar_transition.post_state.asset_id
        or post_roles.scalar_claim_custody_pubkey != scalar_transition.post_state.custody_pubkey
    ):
        raise ValueError("candidate role-claim identity mismatch")
    if pre_roles.apportionment_state_digest != _apportionment_state_digest_v1(
        candidate.pre_apportionment_state
    ) or post_roles.apportionment_state_digest != _apportionment_state_digest_v1(
        candidate.apportionment_transition.state
    ):
        raise ValueError("candidate apportionment-state lineage mismatch")
    if (
        pre_roles.outstanding_total_e8 != scalar_transition.pre_state.outstanding_e8
        or pre_roles.accrued_cumulative_total_e8
        != scalar_transition.pre_state.accrued_cumulative_e8
        or post_roles.outstanding_total_e8 != scalar_transition.post_state.outstanding_e8
        or post_roles.accrued_cumulative_total_e8
        != scalar_transition.post_state.accrued_cumulative_e8
    ):
        raise ValueError("candidate scalar and role claims do not partition equally")


def _validate_candidate_relations_v1(
    candidate: ZUSDProtocolFeeAccrualAllocationCandidateV1,
) -> None:
    _validate_candidate_components_v1(candidate)
    _validate_candidate_identity_and_partition_v1(candidate)

    configuration = candidate.validated_configuration
    scalar_transition = candidate.scalar_claim_transition
    contribution = candidate.fee_contribution
    pre_roles = candidate.pre_role_claims
    post_roles = candidate.post_role_claims
    expected_key = FeeApportionmentKeyV2(
        configuration.body.fee_distribution_domain_id,
        scalar_transition.pre_state.asset_id,
    )
    if contribution != FeeAmountCandidateV2(expected_key, scalar_transition.amount_e8):
        raise ValueError("candidate contribution is not the scalar occurrence")
    if len(candidate.apportionment_transition.allocations) != 1:
        raise ValueError("candidate must contain exactly one allocation")
    allocation = candidate.allocation
    if allocation.key != expected_key or allocation.amount != scalar_transition.amount_e8:
        raise ValueError("candidate allocation does not match the occurrence")
    if allocation.destinations != configuration.body.policy.destinations:
        raise ValueError("candidate allocation destinations do not match the configuration")
    expected_roles = accrue_zusd_protocol_fee_role_claim_state_v1(
        expected_pre_state=pre_roles,
        configuration_root=configuration.configuration_root,
        destinations=allocation.destinations,
        amounts_e8=allocation.amounts,
        post_apportionment_state=candidate.apportionment_transition.state,
    )
    if expected_roles != post_roles:
        raise ValueError("candidate role-claim successor is invalid")
    expected_apportionment = apply_fee_apportionment_v2(
        contributions=(contribution,),
        policy=configuration.body.policy,
        state=candidate.pre_apportionment_state,
    )
    if expected_apportionment != candidate.apportionment_transition:
        raise ValueError("candidate apportionment transition is invalid")


def _candidate_is_valid_v1(value: object) -> bool:
    if type(value) is not ZUSDProtocolFeeAccrualAllocationCandidateV1:
        return False
    try:
        _validate_candidate_relations_v1(value)
    except (TypeError, ValueError, OverflowError, ArithmeticError, IndexError):
        return False
    return True


def _validate_amount_v1(
    value: object,
) -> int | ZUSDProtocolFeeAccrualAllocationRejectV1:
    if type(value) is not int:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.WRONG_EXACT_TYPE,
            "amount_e8",
        )
    if value < 0:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.NEGATIVE_AMOUNT,
            "amount_e8",
        )
    if value == 0:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.ZERO_AMOUNT,
            "amount_e8",
        )
    if value > MAX_FEE_AMOUNT_V2:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.VALUE_EXCEEDS_U256,
            "amount_e8",
        )
    return value


def _source_component_reject_v1(
    source: ZUSDProtocolFeeAccrualAllocationSourceV1,
) -> ZUSDProtocolFeeAccrualAllocationRejectV1 | None:
    validators = (
        (
            _scalar_claim_is_valid_v1(source.pre_scalar_claim),
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_SCALAR_CLAIM,
            "pre_scalar_claim",
        ),
        (
            revalidate_zusd_protocol_fee_role_claim_state_v1(source.pre_role_claims),
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_ROLE_CLAIMS,
            "pre_role_claims",
        ),
        (
            _apportionment_state_is_valid_v1(source.pre_apportionment_state),
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_APPORTIONMENT_STATE,
            "pre_apportionment_state",
        ),
        (
            revalidate_fee_distribution_configuration_claim_v2(source.validated_configuration),
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CONFIGURATION,
            "validated_configuration",
        ),
    )
    for accepted, code, path in validators:
        if not accepted:
            return _reject_v1(code, path)
    return None


def _validate_source_v1(
    source: object,
) -> _ValidatedAccrualSourceV1 | ZUSDProtocolFeeAccrualAllocationRejectV1:
    if type(source) is not ZUSDProtocolFeeAccrualAllocationSourceV1:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.WRONG_EXACT_TYPE,
            "source",
        )
    amount_e8 = _validate_amount_v1(source.amount_e8)
    if type(amount_e8) is ZUSDProtocolFeeAccrualAllocationRejectV1:
        return amount_e8
    component_reject = _source_component_reject_v1(source)
    if component_reject is not None:
        return component_reject
    validated = _ValidatedAccrualSourceV1(
        cast(ZUSDProtocolFeeClaimV1, source.pre_scalar_claim),
        cast(ZUSDProtocolFeeRoleClaimStateV1, source.pre_role_claims),
        cast(CommittedFeeApportionmentStateV2, source.pre_apportionment_state),
        cast(
            ValidatedFeeDistributionConfigurationClaimV2,
            source.validated_configuration,
        ),
        amount_e8,
    )
    if (
        validated.role_claims.fee_distribution_domain_id
        != validated.configuration.body.fee_distribution_domain_id
        or validated.role_claims.asset_id != validated.scalar_claim.asset_id
    ):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "role_claim_identity",
        )
    if validated.role_claims.scalar_claim_custody_pubkey != validated.scalar_claim.custody_pubkey:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "role_claim_custody",
        )
    if validated.role_claims.apportionment_state_digest != _apportionment_state_digest_v1(
        validated.apportionment_state
    ):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "apportionment_state_lineage",
        )
    if (
        validated.role_claims.outstanding_total_e8 != validated.scalar_claim.outstanding_e8
        or validated.role_claims.accrued_cumulative_total_e8
        != validated.scalar_claim.accrued_cumulative_e8
    ):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_PRESTATE_PARTITION,
            "claim_partition",
        )
    return validated


def _derive_arithmetic_v1(
    source: _ValidatedAccrualSourceV1,
) -> _AccrualArithmeticV1 | ZUSDProtocolFeeAccrualAllocationRejectV1:
    scalar_transition = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=source.scalar_claim.asset_id,
        expected_custody_pubkey=source.scalar_claim.custody_pubkey,
        expected_pre_state=source.scalar_claim,
        amount_e8=source.amount_e8,
    )
    if type(scalar_transition) is ZUSDProtocolFeeClaimRejectV1:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.SCALAR_CLAIM_TRANSITION,
            "scalar_claim_transition",
            scalar_transition.code.value,
            *scalar_transition.path,
        )
    contribution = FeeAmountCandidateV2(
        FeeApportionmentKeyV2(
            source.configuration.body.fee_distribution_domain_id,
            source.scalar_claim.asset_id,
        ),
        source.amount_e8,
    )
    apportioned = apply_fee_apportionment_v2(
        contributions=(contribution,),
        policy=source.configuration.body.policy,
        state=source.apportionment_state,
    )
    if type(apportioned) is FeeApportionmentTransitionRejectV2:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.APPORTIONMENT,
            "apportionment_transition",
            apportioned.code.value,
            *apportioned.path,
        )
    if len(apportioned.allocations) != 1:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.ALLOCATION_CARDINALITY,
            "apportionment_transition",
            "allocations",
        )
    return _AccrualArithmeticV1(scalar_transition, contribution, apportioned)


def _derive_role_successor_v1(
    source: _ValidatedAccrualSourceV1,
    arithmetic: _AccrualArithmeticV1,
) -> ZUSDProtocolFeeRoleClaimStateV1 | ZUSDProtocolFeeAccrualAllocationRejectV1:
    allocation = arithmetic.apportionment_transition.allocations[0]
    try:
        post = accrue_zusd_protocol_fee_role_claim_state_v1(
            expected_pre_state=source.role_claims,
            configuration_root=source.configuration.configuration_root,
            destinations=allocation.destinations,
            amounts_e8=allocation.amounts,
            post_apportionment_state=arithmetic.apportionment_transition.state,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.ROLE_CLAIM_TRANSITION,
            "post_role_claims",
        )
    if (
        post.outstanding_total_e8 != arithmetic.scalar_transition.post_state.outstanding_e8
        or post.accrued_cumulative_total_e8
        != arithmetic.scalar_transition.post_state.accrued_cumulative_e8
    ):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CANDIDATE,
            "post_partition",
        )
    return post


def derive_zusd_protocol_fee_accrual_allocation_v1(
    source: object,
) -> ZUSDProtocolFeeAccrualAllocationResultV1:
    """Derive one configuration-relative allocation candidate from exact inputs."""

    validated = _validate_source_v1(source)
    if type(validated) is ZUSDProtocolFeeAccrualAllocationRejectV1:
        return validated
    arithmetic = _derive_arithmetic_v1(validated)
    if type(arithmetic) is ZUSDProtocolFeeAccrualAllocationRejectV1:
        return arithmetic
    post_role_claims = _derive_role_successor_v1(validated, arithmetic)
    if type(post_role_claims) is ZUSDProtocolFeeAccrualAllocationRejectV1:
        return post_role_claims
    try:
        candidate = _zusd_protocol_fee_accrual_allocation_candidate_v1(
            validated_configuration=validated.configuration,
            scalar_claim_transition=arithmetic.scalar_transition,
            fee_contribution=arithmetic.contribution,
            pre_role_claims=validated.role_claims,
            post_role_claims=post_role_claims,
            pre_apportionment_state=validated.apportionment_state,
            apportionment_transition=arithmetic.apportionment_transition,
        )
        _validate_candidate_relations_v1(candidate)
        return candidate
    except (TypeError, ValueError, ArithmeticError, IndexError):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CANDIDATE,
            "candidate",
        )


def verify_zusd_protocol_fee_accrual_allocation_v1(
    *,
    source: object,
    candidate: object,
) -> ZUSDProtocolFeeAccrualAllocationResultV1:
    """Rebuild all derived fields from the externally supplied exact source."""

    if not _candidate_is_valid_v1(candidate):
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.INVALID_CANDIDATE,
            "candidate",
        )
    rebuilt = derive_zusd_protocol_fee_accrual_allocation_v1(source)
    if type(rebuilt) is not ZUSDProtocolFeeAccrualAllocationCandidateV1:
        return rebuilt
    exact_candidate = cast(ZUSDProtocolFeeAccrualAllocationCandidateV1, candidate)
    if rebuilt != exact_candidate:
        return _reject_v1(
            ZUSDProtocolFeeAccrualAllocationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "instance",
        )
    return exact_candidate


__all__ = (
    "ZUSDProtocolFeeAccrualAllocationCandidateV1",
    "ZUSDProtocolFeeAccrualAllocationRejectCodeV1",
    "ZUSDProtocolFeeAccrualAllocationRejectV1",
    "ZUSDProtocolFeeAccrualAllocationResultV1",
    "ZUSDProtocolFeeAccrualAllocationSourceV1",
    "derive_zusd_protocol_fee_accrual_allocation_v1",
    "verify_zusd_protocol_fee_accrual_allocation_v1",
)
