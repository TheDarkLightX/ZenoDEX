"""Closed values for state-bound authenticated zUSD fee allocation."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast, final

from .fcis_fee_configuration_state_binding_v2 import StateBoundActiveFeeConfigurationV2
from .zusd_authenticated_borrow_fee_occurrence_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
)
from .zusd_protocol_fee_accrual_allocation_values import (
    ZUSDProtocolFeeAccrualAllocationCandidateV1,
)

ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2: Final = (
    "zenodex/zusd/state-bound-fee-accrual-allocation/v2"
)
ZUSD_PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V2: Final = "protocol-fees:zusd"

_COMPOSITE_TOKEN_V2 = object()


class ZUSDStateBoundFeeAccrualAllocationRejectCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_STATE_BOUND_CONFIGURATION = "invalid_state_bound_configuration"
    INVALID_AUTHENTICATED_OCCURRENCE = "invalid_authenticated_occurrence"
    REQUEST_SEQUENCE_MISMATCH = "request_sequence_mismatch"
    DEPLOYMENT_CONFIG_ROOT_MISMATCH = "deployment_config_root_mismatch"
    AUTHORITY_EPOCH_MISMATCH = "authority_epoch_mismatch"
    ZUSD_STATE_ROOT_MISMATCH = "zusd_state_root_mismatch"
    MANAGED_ASSET_MISMATCH = "managed_asset_mismatch"
    CLAIM_CUSTODY_MISMATCH = "claim_custody_mismatch"
    STATE_COMPONENT_ROOT_MISMATCH = "state_component_root_mismatch"
    FEE_DISTRIBUTION_DOMAIN_MISMATCH = "fee_distribution_domain_mismatch"
    CUMULATIVE_FEE_HISTORY_MISMATCH = "cumulative_fee_history_mismatch"
    ALLOCATION_REJECTED = "allocation_rejected"
    INVALID_CANDIDATE = "invalid_candidate"
    CANDIDATE_MISMATCH = "candidate_mismatch"


@final
@dataclass(frozen=True, slots=True)
class ZUSDStateBoundFeeAccrualAllocationSourceV2:
    """Independent exact inputs; this public carrier has no authority."""

    state_bound_configuration: object
    authenticated_occurrence: object
    pre_scalar_claim: object
    pre_role_claims: object
    pre_apportionment_state: object


@final
@dataclass(frozen=True, slots=True)
class ZUSDStateBoundFeeAccrualAllocationRejectV2:
    code: ZUSDStateBoundFeeAccrualAllocationRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDStateBoundFeeAccrualAllocationRejectCodeV2:
            raise TypeError("state-bound fee allocation reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("state-bound fee allocation reject path must be nonempty")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("state-bound fee allocation reject path parts must be exact")


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class ZUSDStateBoundFeeAccrualAllocationV2:
    """Controlled composition evidence; never a publication or effect plan."""

    state_bound_configuration: StateBoundActiveFeeConfigurationV2
    authenticated_occurrence: ZUSDAuthenticatedBorrowFeeOccurrenceV1
    accrual_allocation: ZUSDProtocolFeeAccrualAllocationCandidateV1
    composition_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _COMPOSITE_TOKEN_V2:
            raise TypeError("state-bound fee allocation requires controlled composition")
        if type(self.state_bound_configuration) is not StateBoundActiveFeeConfigurationV2:
            raise TypeError("state-bound configuration must be exact")
        if type(self.authenticated_occurrence) is not ZUSDAuthenticatedBorrowFeeOccurrenceV1:
            raise TypeError("authenticated occurrence must be exact")
        if type(self.accrual_allocation) is not ZUSDProtocolFeeAccrualAllocationCandidateV1:
            raise TypeError("accrual allocation must be exact")
        if type(self.composition_root) is not str:
            raise TypeError("composition root must be an exact string")

    @property
    def state_projection_root(self) -> str:
        return self.state_bound_configuration.state_projection_root

    @property
    def authenticated_occurrence_root(self) -> str:
        return self.authenticated_occurrence.occurrence_root

    @property
    def scalar_occurrence_root(self) -> str:
        return cast(str, self.accrual_allocation.occurrence_root)


ZUSDStateBoundFeeAccrualAllocationResultV2: TypeAlias = (
    ZUSDStateBoundFeeAccrualAllocationV2 | ZUSDStateBoundFeeAccrualAllocationRejectV2
)


def _zusd_state_bound_fee_accrual_allocation_v2(
    *,
    state_bound_configuration: StateBoundActiveFeeConfigurationV2,
    authenticated_occurrence: ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    accrual_allocation: ZUSDProtocolFeeAccrualAllocationCandidateV1,
    composition_root: str,
) -> ZUSDStateBoundFeeAccrualAllocationV2:
    return ZUSDStateBoundFeeAccrualAllocationV2(
        state_bound_configuration=state_bound_configuration,
        authenticated_occurrence=authenticated_occurrence,
        accrual_allocation=accrual_allocation,
        composition_root=composition_root,
        _construction_token=_COMPOSITE_TOKEN_V2,
    )


__all__ = (
    "ZUSD_PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V2",
    "ZUSD_STATE_BOUND_FEE_ACCRUAL_ALLOCATION_SCHEMA_V2",
    "ZUSDStateBoundFeeAccrualAllocationRejectCodeV2",
    "ZUSDStateBoundFeeAccrualAllocationRejectV2",
    "ZUSDStateBoundFeeAccrualAllocationResultV2",
    "ZUSDStateBoundFeeAccrualAllocationSourceV2",
    "ZUSDStateBoundFeeAccrualAllocationV2",
)
