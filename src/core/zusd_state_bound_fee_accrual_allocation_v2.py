"""Compose one authenticated zUSD fee occurrence with exact-state allocation.

This research relation consumes a state-bound fee configuration, an E01-bound
borrowing-fee occurrence, and the exact pre-claim/apportionment components
named by one state projection.  The fee amount and active configuration are
derived from those controlled values; callers cannot supply either again.

The exact-state projection remains candidate data.  This module does not prove
that a runtime projection was reconstructed from store-current global state,
and it creates no balance patch, publication capability, receipt, or effect.
"""

from __future__ import annotations

from typing import NamedTuple, cast
from weakref import WeakValueDictionary

from .fcis_fee_apportionment_values import (
    CommittedFeeApportionmentStateV2,
)
from .fcis_fee_configuration_state_binding_v2 import (
    StateBoundActiveFeeConfigurationV2,
    revalidate_state_bound_active_fee_configuration_v2,
)
from .zusd_authenticated_borrow_fee_occurrence_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    canonical_zusd_state_root_v1,
    revalidate_zusd_authenticated_borrow_fee_occurrence_v1,
)
from .zusd_protocol_fee_accrual_allocation import (
    derive_zusd_protocol_fee_accrual_allocation_v1,
    verify_zusd_protocol_fee_accrual_allocation_v1,
)
from .zusd_protocol_fee_accrual_allocation_values import (
    ZUSDProtocolFeeAccrualAllocationCandidateV1,
    ZUSDProtocolFeeAccrualAllocationRejectV1,
    ZUSDProtocolFeeAccrualAllocationSourceV1,
)
from .zusd_protocol_fee_claim import ZUSDProtocolFeeClaimV1
from .zusd_protocol_fee_role_claims import ZUSDProtocolFeeRoleClaimStateV1
from .zusd_state_bound_fee_accrual_allocation_roots_v2 import (
    _apportionment_state_root_v2,
    _composition_root_v2,
)
from .zusd_state_bound_fee_accrual_allocation_values_v2 import (
    ZUSD_PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V2,
    ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2,
    ZUSDStateBoundFeeAccrualAllocationRejectCodeV2,
    ZUSDStateBoundFeeAccrualAllocationRejectV2,
    ZUSDStateBoundFeeAccrualAllocationResultV2,
    ZUSDStateBoundFeeAccrualAllocationSourceV2,
    ZUSDStateBoundFeeAccrualAllocationV2,
    _zusd_state_bound_fee_accrual_allocation_v2,
)


class _AlignedSourceV2(NamedTuple):
    state_bound_configuration: StateBoundActiveFeeConfigurationV2
    authenticated_occurrence: ZUSDAuthenticatedBorrowFeeOccurrenceV1
    scalar_claim: ZUSDProtocolFeeClaimV1
    role_claims: ZUSDProtocolFeeRoleClaimStateV1
    apportionment_state: CommittedFeeApportionmentStateV2


def _reject_v2(
    code: ZUSDStateBoundFeeAccrualAllocationRejectCodeV2,
    *path: str,
) -> ZUSDStateBoundFeeAccrualAllocationRejectV2:
    return ZUSDStateBoundFeeAccrualAllocationRejectV2(code, tuple(path))


def _request_context_reject_v2(
    source: _AlignedSourceV2,
) -> ZUSDStateBoundFeeAccrualAllocationRejectV2 | None:
    projection = source.state_bound_configuration.exact_state_projection
    identity = source.authenticated_occurrence.request_identity
    if identity.expected_sequence != projection.authority_header.sequence:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.REQUEST_SEQUENCE_MISMATCH,
            "authenticated_occurrence",
            "request_identity",
            "expected_sequence",
        )
    if identity.deployment_config_root != projection.deployment_config_root:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.DEPLOYMENT_CONFIG_ROOT_MISMATCH,
            "authenticated_occurrence",
            "request_identity",
            "deployment_config_root",
        )
    if identity.authority_epoch_index != projection.authority_epoch_index:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.AUTHORITY_EPOCH_MISMATCH,
            "authenticated_occurrence",
            "request_identity",
            "authority_epoch_index",
        )
    if canonical_zusd_state_root_v1(source.authenticated_occurrence.pre_state) != (
        projection.zusd_state_root
    ):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.ZUSD_STATE_ROOT_MISMATCH,
            "authenticated_occurrence",
            "pre_state",
        )
    return None


def _exact_components_v2(
    source: ZUSDStateBoundFeeAccrualAllocationSourceV2,
) -> _AlignedSourceV2 | ZUSDStateBoundFeeAccrualAllocationRejectV2:
    if type(source.pre_scalar_claim) is not ZUSDProtocolFeeClaimV1:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.WRONG_EXACT_TYPE,
            "pre_scalar_claim",
        )
    if type(source.pre_role_claims) is not ZUSDProtocolFeeRoleClaimStateV1:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.WRONG_EXACT_TYPE,
            "pre_role_claims",
        )
    if type(source.pre_apportionment_state) is not CommittedFeeApportionmentStateV2:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.WRONG_EXACT_TYPE,
            "pre_apportionment_state",
        )
    return _AlignedSourceV2(
        cast(StateBoundActiveFeeConfigurationV2, source.state_bound_configuration),
        cast(ZUSDAuthenticatedBorrowFeeOccurrenceV1, source.authenticated_occurrence),
        cast(ZUSDProtocolFeeClaimV1, source.pre_scalar_claim),
        cast(ZUSDProtocolFeeRoleClaimStateV1, source.pre_role_claims),
        cast(CommittedFeeApportionmentStateV2, source.pre_apportionment_state),
    )


def _state_component_reject_v2(
    source: _AlignedSourceV2,
) -> ZUSDStateBoundFeeAccrualAllocationRejectV2 | None:
    projection = source.state_bound_configuration.exact_state_projection
    if source.scalar_claim.asset_id != projection.zusd_asset_id:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.MANAGED_ASSET_MISMATCH,
            "pre_scalar_claim",
            "asset_id",
        )
    if source.scalar_claim.custody_pubkey != projection.protocol_fee_claim_custody_pubkey:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CLAIM_CUSTODY_MISMATCH,
            "pre_scalar_claim",
            "custody_pubkey",
        )
    try:
        component_roots = (
            source.scalar_claim.state_root,
            source.role_claims.state_root,
            _apportionment_state_root_v2(source.apportionment_state),
        )
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.WRONG_EXACT_TYPE,
            "state_components",
        )
    expected_roots = (
        projection.protocol_fee_claim_state_root,
        projection.protocol_fee_role_claim_state_root,
        projection.fee_apportionment_state_root,
    )
    if component_roots != expected_roots:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.STATE_COMPONENT_ROOT_MISMATCH,
            "state_components",
        )
    if (
        source.state_bound_configuration.validated_configuration.body.fee_distribution_domain_id
        != ZUSD_PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V2
    ):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.FEE_DISTRIBUTION_DOMAIN_MISMATCH,
            "state_bound_configuration",
            "fee_distribution_domain_id",
        )
    if (
        source.scalar_claim.accrued_cumulative_e8
        != source.authenticated_occurrence.pre_state.protocol_revenue_zusd_cum_e8
    ):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CUMULATIVE_FEE_HISTORY_MISMATCH,
            "pre_scalar_claim",
            "accrued_cumulative_e8",
        )
    return None


def _validated_source_v2(
    source: object,
) -> _AlignedSourceV2 | ZUSDStateBoundFeeAccrualAllocationRejectV2:
    if type(source) is not ZUSDStateBoundFeeAccrualAllocationSourceV2:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.WRONG_EXACT_TYPE,
            "source",
        )
    if not revalidate_state_bound_active_fee_configuration_v2(source.state_bound_configuration):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_STATE_BOUND_CONFIGURATION,
            "state_bound_configuration",
        )
    if not revalidate_zusd_authenticated_borrow_fee_occurrence_v1(source.authenticated_occurrence):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_AUTHENTICATED_OCCURRENCE,
            "authenticated_occurrence",
        )
    aligned = _exact_components_v2(source)
    if type(aligned) is ZUSDStateBoundFeeAccrualAllocationRejectV2:
        return aligned
    for reject in (
        _request_context_reject_v2(aligned),
        _state_component_reject_v2(aligned),
    ):
        if reject is not None:
            return reject
    return aligned


def _allocation_source_v2(
    source: _AlignedSourceV2,
) -> ZUSDProtocolFeeAccrualAllocationSourceV1:
    return ZUSDProtocolFeeAccrualAllocationSourceV1(
        pre_scalar_claim=source.scalar_claim,
        pre_role_claims=source.role_claims,
        pre_apportionment_state=source.apportionment_state,
        validated_configuration=source.state_bound_configuration.validated_configuration,
        amount_e8=source.authenticated_occurrence.fee_e8,
    )


def _validate_composite_v2(value: ZUSDStateBoundFeeAccrualAllocationV2) -> None:
    allocation = value.accrual_allocation
    if type(allocation) is not ZUSDProtocolFeeAccrualAllocationCandidateV1:
        raise TypeError("accrual allocation must be exact")
    aligned = _validated_source_v2(
        ZUSDStateBoundFeeAccrualAllocationSourceV2(
            state_bound_configuration=value.state_bound_configuration,
            authenticated_occurrence=value.authenticated_occurrence,
            pre_scalar_claim=allocation.scalar_claim_transition.pre_state,
            pre_role_claims=allocation.pre_role_claims,
            pre_apportionment_state=allocation.pre_apportionment_state,
        )
    )
    if type(aligned) is ZUSDStateBoundFeeAccrualAllocationRejectV2:
        raise ValueError("state and occurrence components are not aligned")
    source = _allocation_source_v2(aligned)
    if (
        verify_zusd_protocol_fee_accrual_allocation_v1(
            source=source,
            candidate=allocation,
        )
        is not allocation
    ):
        raise ValueError("accrual allocation is invalid")
    if (
        allocation.scalar_claim_transition.post_state.accrued_cumulative_e8
        != value.authenticated_occurrence.post_state.protocol_revenue_zusd_cum_e8
    ):
        raise ValueError("post-state cumulative fee histories diverge")
    expected_root = _composition_root_v2(
        state_bound_configuration=value.state_bound_configuration,
        authenticated_occurrence=value.authenticated_occurrence,
        accrual_allocation=allocation,
    )
    if value.composition_root != expected_root:
        raise ValueError("composition root is not canonical")


_COMPOSITES_V2: WeakValueDictionary[int, ZUSDStateBoundFeeAccrualAllocationV2] = (
    WeakValueDictionary()
)
_COMPOSITE_SNAPSHOTS_V2: dict[int, tuple[object, ...]] = {}


def _composite_snapshot_v2(
    value: ZUSDStateBoundFeeAccrualAllocationV2,
) -> tuple[object, ...]:
    return (
        value.state_projection_root,
        value.state_bound_configuration.binding_root,
        value.authenticated_occurrence_root,
        value.scalar_occurrence_root,
        value.composition_root,
    )


def _register_composite_v2(
    value: ZUSDStateBoundFeeAccrualAllocationV2,
) -> ZUSDStateBoundFeeAccrualAllocationV2:
    identity = id(value)
    _COMPOSITES_V2[identity] = value
    _COMPOSITE_SNAPSHOTS_V2[identity] = _composite_snapshot_v2(value)
    return value


def derive_zusd_state_bound_fee_accrual_allocation_v2(
    source: object,
) -> ZUSDStateBoundFeeAccrualAllocationResultV2:
    """Derive one complete local composition with deterministic rejection precedence."""

    aligned = _validated_source_v2(source)
    if type(aligned) is ZUSDStateBoundFeeAccrualAllocationRejectV2:
        return aligned
    allocation_source = _allocation_source_v2(aligned)
    allocation = derive_zusd_protocol_fee_accrual_allocation_v1(allocation_source)
    if type(allocation) is ZUSDProtocolFeeAccrualAllocationRejectV1:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.ALLOCATION_REJECTED,
            "accrual_allocation",
            allocation.code.value,
            *allocation.path,
        )
    if type(allocation) is not ZUSDProtocolFeeAccrualAllocationCandidateV1:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_CANDIDATE,
            "accrual_allocation",
        )
    try:
        value = _zusd_state_bound_fee_accrual_allocation_v2(
            state_bound_configuration=aligned.state_bound_configuration,
            authenticated_occurrence=aligned.authenticated_occurrence,
            accrual_allocation=allocation,
            composition_root=_composition_root_v2(
                state_bound_configuration=aligned.state_bound_configuration,
                authenticated_occurrence=aligned.authenticated_occurrence,
                accrual_allocation=allocation,
            ),
        )
        _validate_composite_v2(value)
        return _register_composite_v2(value)
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError, IndexError):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_CANDIDATE,
            "candidate",
        )


def revalidate_zusd_state_bound_fee_accrual_allocation_v2(value: object) -> bool:
    """Recheck registry provenance, exact relations, inner allocation, and root."""

    if type(value) is not ZUSDStateBoundFeeAccrualAllocationV2:
        return False
    if _COMPOSITES_V2.get(id(value)) is not value:
        return False
    try:
        _validate_composite_v2(value)
        return _COMPOSITE_SNAPSHOTS_V2.get(id(value)) == _composite_snapshot_v2(value)
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError, IndexError):
        return False


def verify_zusd_state_bound_fee_accrual_allocation_v2(
    *,
    source: object,
    candidate: object,
) -> ZUSDStateBoundFeeAccrualAllocationResultV2:
    """Freshly rebuild one candidate from its complete externally supplied source."""

    if not revalidate_zusd_state_bound_fee_accrual_allocation_v2(candidate):
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.INVALID_CANDIDATE,
            "candidate",
        )
    rebuilt = derive_zusd_state_bound_fee_accrual_allocation_v2(source)
    if type(rebuilt) is not ZUSDStateBoundFeeAccrualAllocationV2:
        return rebuilt
    exact_candidate = cast(ZUSDStateBoundFeeAccrualAllocationV2, candidate)
    if rebuilt != exact_candidate:
        return _reject_v2(
            ZUSDStateBoundFeeAccrualAllocationRejectCodeV2.CANDIDATE_MISMATCH,
            "candidate",
        )
    return exact_candidate


__all__ = (
    "ZUSD_PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V2",
    "ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2",
    "ZUSDStateBoundFeeAccrualAllocationRejectCodeV2",
    "ZUSDStateBoundFeeAccrualAllocationRejectV2",
    "ZUSDStateBoundFeeAccrualAllocationResultV2",
    "ZUSDStateBoundFeeAccrualAllocationSourceV2",
    "ZUSDStateBoundFeeAccrualAllocationV2",
    "derive_zusd_state_bound_fee_accrual_allocation_v2",
    "revalidate_zusd_state_bound_fee_accrual_allocation_v2",
    "verify_zusd_state_bound_fee_accrual_allocation_v2",
)
