"""Canonical roots for state-bound authenticated zUSD fee allocation."""

from __future__ import annotations

from typing import cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_fee_apportionment_codec import canonical_sha256_fcis_fee_apportionment_v2
from .fcis_fee_apportionment_values import (
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    CommittedFeeApportionmentStateV2,
)
from .fcis_fee_configuration_state_binding_v2 import StateBoundActiveFeeConfigurationV2
from .zusd_authenticated_borrow_fee_occurrence_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    canonical_zusd_state_root_v1,
)
from .zusd_protocol_fee_accrual_allocation_values import (
    ZUSDProtocolFeeAccrualAllocationCandidateV1,
)
from .zusd_state_bound_fee_accrual_allocation_values_v2 import (
    ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2,
)


def _apportionment_state_root_v2(value: CommittedFeeApportionmentStateV2) -> str:
    value.__post_init__()
    return cast(
        str,
        canonical_sha256_fcis_fee_apportionment_v2(
            COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
            value,
        ),
    )


def _composition_root_v2(
    *,
    state_bound_configuration: StateBoundActiveFeeConfigurationV2,
    authenticated_occurrence: ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    accrual_allocation: ZUSDProtocolFeeAccrualAllocationCandidateV1,
) -> str:
    projection = state_bound_configuration.exact_state_projection
    body = {
        "schema": ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2,
        "global_state_root": projection.global_state_root,
        "state_projection_root": state_bound_configuration.state_projection_root,
        "state_binding_root": state_bound_configuration.binding_root,
        "configuration_root": state_bound_configuration.configuration_root,
        "deployment_config_root": projection.deployment_config_root,
        "authority_epoch_index": projection.authority_epoch_index,
        "request_identity_root": authenticated_occurrence.request_identity.request_identity_root,
        "authenticated_occurrence_root": authenticated_occurrence.occurrence_root,
        "scalar_occurrence_root": accrual_allocation.occurrence_root,
        "pre_zusd_state_root": projection.zusd_state_root,
        "post_zusd_state_root": canonical_zusd_state_root_v1(authenticated_occurrence.post_state),
        "pre_scalar_claim_root": accrual_allocation.scalar_claim_transition.pre_state.state_root,
        "post_scalar_claim_root": accrual_allocation.scalar_claim_transition.post_state.state_root,
        "pre_role_claim_root": accrual_allocation.pre_role_claims.state_root,
        "post_role_claim_root": accrual_allocation.post_role_claims.state_root,
        "pre_apportionment_state_root": _apportionment_state_root_v2(
            accrual_allocation.pre_apportionment_state
        ),
        "post_apportionment_state_root": _apportionment_state_root_v2(
            accrual_allocation.apportionment_transition.state
        ),
    }
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zusd_state_bound_fee_accrual_allocation", version=2)
            + canonical_json_bytes(body)
        ),
    )


__all__ = ()
