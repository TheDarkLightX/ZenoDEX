"""Closed values for configuration-relative zUSD fee accrual allocation."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, final

from .fcis_fee_apportionment_values import (
    AssetFeeAllocationV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentTransitionOkV2,
)
from .fcis_fee_distribution_configuration_values import (
    ValidatedFeeDistributionConfigurationClaimV2,
)
from .zusd_protocol_fee_claim import ZUSDProtocolFeeClaimTransitionV1
from .zusd_protocol_fee_role_claims import ZUSDProtocolFeeRoleClaimStateV1

_CANDIDATE_CONSTRUCTION_TOKEN_V1 = object()


class ZUSDProtocolFeeAccrualAllocationRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    NEGATIVE_AMOUNT = "negative_amount"
    ZERO_AMOUNT = "zero_amount"
    VALUE_EXCEEDS_U256 = "value_exceeds_u256"
    INVALID_SCALAR_CLAIM = "invalid_scalar_claim"
    INVALID_ROLE_CLAIMS = "invalid_role_claims"
    INVALID_CONFIGURATION = "invalid_configuration"
    INVALID_APPORTIONMENT_STATE = "invalid_apportionment_state"
    EXTERNAL_INSTANCE_MISMATCH = "external_instance_mismatch"
    INVALID_PRESTATE_PARTITION = "invalid_prestate_partition"
    SCALAR_CLAIM_TRANSITION = "scalar_claim_transition"
    APPORTIONMENT = "apportionment"
    ALLOCATION_CARDINALITY = "allocation_cardinality"
    ROLE_CLAIM_TRANSITION = "role_claim_transition"
    INVALID_CANDIDATE = "invalid_candidate"


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeAccrualAllocationRejectV1:
    code: ZUSDProtocolFeeAccrualAllocationRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDProtocolFeeAccrualAllocationRejectCodeV1:
            raise TypeError("accrual allocation reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("accrual allocation reject path must be nonempty")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("accrual allocation reject path parts must be exact")


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeAccrualAllocationSourceV1:
    """Externally supplied candidate inputs carrying no authority by themselves."""

    pre_scalar_claim: object
    pre_role_claims: object
    pre_apportionment_state: object
    validated_configuration: object
    amount_e8: object


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeAccrualAllocationCandidateV1:
    """Controlled configuration-relative evidence for one fee occurrence."""

    validated_configuration: ValidatedFeeDistributionConfigurationClaimV2
    scalar_claim_transition: ZUSDProtocolFeeClaimTransitionV1
    fee_contribution: FeeAmountCandidateV2
    pre_role_claims: ZUSDProtocolFeeRoleClaimStateV1
    post_role_claims: ZUSDProtocolFeeRoleClaimStateV1
    pre_apportionment_state: CommittedFeeApportionmentStateV2
    apportionment_transition: FeeApportionmentTransitionOkV2
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _CANDIDATE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("accrual allocation candidates require controlled derivation")
        exact_fields = (
            (self.validated_configuration, ValidatedFeeDistributionConfigurationClaimV2),
            (self.scalar_claim_transition, ZUSDProtocolFeeClaimTransitionV1),
            (self.fee_contribution, FeeAmountCandidateV2),
            (self.pre_role_claims, ZUSDProtocolFeeRoleClaimStateV1),
            (self.post_role_claims, ZUSDProtocolFeeRoleClaimStateV1),
            (self.pre_apportionment_state, CommittedFeeApportionmentStateV2),
            (self.apportionment_transition, FeeApportionmentTransitionOkV2),
        )
        if any(type(value) is not expected for value, expected in exact_fields):
            raise TypeError("accrual allocation candidate fields must be exact")
        if len(self.apportionment_transition.allocations) != 1:
            raise ValueError("accrual allocation candidate must contain one allocation")

    @property
    def allocation(self) -> AssetFeeAllocationV2:
        return self.apportionment_transition.allocations[0]

    @property
    def occurrence_root(self) -> str:
        """Exact scalar-claim transition identity; it is not a publication receipt."""

        return self.scalar_claim_transition.transition_root


ZUSDProtocolFeeAccrualAllocationResultV1: TypeAlias = (
    ZUSDProtocolFeeAccrualAllocationCandidateV1 | ZUSDProtocolFeeAccrualAllocationRejectV1
)


def _zusd_protocol_fee_accrual_allocation_candidate_v1(
    *,
    validated_configuration: ValidatedFeeDistributionConfigurationClaimV2,
    scalar_claim_transition: ZUSDProtocolFeeClaimTransitionV1,
    fee_contribution: FeeAmountCandidateV2,
    pre_role_claims: ZUSDProtocolFeeRoleClaimStateV1,
    post_role_claims: ZUSDProtocolFeeRoleClaimStateV1,
    pre_apportionment_state: CommittedFeeApportionmentStateV2,
    apportionment_transition: FeeApportionmentTransitionOkV2,
) -> ZUSDProtocolFeeAccrualAllocationCandidateV1:
    return ZUSDProtocolFeeAccrualAllocationCandidateV1(
        validated_configuration=validated_configuration,
        scalar_claim_transition=scalar_claim_transition,
        fee_contribution=fee_contribution,
        pre_role_claims=pre_role_claims,
        post_role_claims=post_role_claims,
        pre_apportionment_state=pre_apportionment_state,
        apportionment_transition=apportionment_transition,
        _construction_token=_CANDIDATE_CONSTRUCTION_TOKEN_V1,
    )


__all__ = (
    "ZUSDProtocolFeeAccrualAllocationCandidateV1",
    "ZUSDProtocolFeeAccrualAllocationRejectCodeV1",
    "ZUSDProtocolFeeAccrualAllocationRejectV1",
    "ZUSDProtocolFeeAccrualAllocationResultV1",
    "ZUSDProtocolFeeAccrualAllocationSourceV1",
)
