"""Bind the buyback spend core to one authenticated Spot safety receipt.

This unmounted SHADOW adapter removes consensus height and the route-safe spend
limit from caller control.  It does not compose the Spot and tokenomics lane
receipts or authorize publication.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, replace
from typing import Any, Final, TypeVar, cast

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
)
from .zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendAcceptedV1,
    ZDEXBuybackSpendContextV1,
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
    ZDEXBuybackSpendStateV1,
    transition_zdex_buyback_spend_v1,
)
from .zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV1,
)
from .zdex_fee_allocation_receipt_verification_v1 import (
    _snapshot_fee_policy_v1,
    _snapshot_fee_state_v1,
)
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeStateV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
)

VERIFIED_ZDEX_BUYBACK_SPEND_SCHEMA_V1: Final = "zenodex/verified-zdex-buyback-spend/v1"
_VERIFIED_ZDEX_BUYBACK_SPEND_TOKEN_V1 = object()
ValueT = TypeVar("ValueT")


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackSpendFieldsV1:
    accepted: ZDEXBuybackSpendAcceptedV1
    safety_receipt_binding_root: str
    global_pre_state_root: str


class VerifiedZDEXBuybackSpendV1:
    """Opaque process-local witness for receipt-bound spend selection."""

    _fields: _VerifiedZDEXBuybackSpendFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXBuybackSpendFieldsV1,
    ) -> None:
        if token is not _VERIFIED_ZDEX_BUYBACK_SPEND_TOKEN_V1:
            raise TypeError("VerifiedZDEXBuybackSpendV1 is adapter-constructed")
        if type(fields) is not _VerifiedZDEXBuybackSpendFieldsV1:
            raise TypeError("verified ZDEX buyback spend fields must be exact typed data")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXBuybackSpendV1 is immutable")

    @property
    def accepted(self) -> ZDEXBuybackSpendAcceptedV1:
        return deepcopy(self._fields.accepted)

    @property
    def safety_receipt_binding_root(self) -> str:
        return self._fields.safety_receipt_binding_root

    @property
    def global_pre_state_root(self) -> str:
        return self._fields.global_pre_state_root


VerifiedZDEXBuybackSpendResultV1 = VerifiedZDEXBuybackSpendV1 | ZDEXBuybackSpendRejectedV1


def _snapshot_scalar_dataclass_v1(
    value: object,
    expected_type: type[ValueT],
    *,
    name: str,
) -> ValueT:
    if type(value) is not expected_type:
        raise TypeError(f"{name} must be exact typed data")
    _require_exact_dataclass_scalars_v1(value, name=name)
    return cast(ValueT, replace(cast(Any, value)))


def _snapshot_cadence_v1(
    cadence: ZDEXBuybackSpendStateV1,
) -> ZDEXBuybackSpendStateV1:
    if type(cadence) is not ZDEXBuybackSpendStateV1:
        raise TypeError("ZDEX buyback cadence state must be exact typed data")
    if type(cadence.quote_asset_id) is not str or type(cadence.policy_root) is not str:
        raise TypeError("ZDEX buyback cadence roots must be exact str")
    if cadence.last_execution_height is not None and type(cadence.last_execution_height) is not int:
        raise TypeError("ZDEX buyback cadence height must be exact int or None")
    cadence.validate()
    return replace(cadence)


def _reject_safety_mismatch_v1(
    cadence: ZDEXBuybackSpendStateV1,
    fee_state: ZDEXFeeStateV1,
) -> ZDEXBuybackSpendRejectedV1:
    return ZDEXBuybackSpendRejectedV1(
        ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH,
        None,
        cadence,
        cadence,
        fee_state,
        fee_state,
    )


def transition_verified_zdex_buyback_spend_shadow_v1(
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_policy: ZDEXFeeAllocationPolicyV1,
    fee_pre_state: ZDEXFeeStateV1,
    fee_context: ZDEXFeeAllocationContextV1,
    fee_command: ZDEXFeeAllocationCommandV1,
    occurrence: EconomicCommandOccurrenceV1,
    safety_purchase: VerifiedZDEXBuybackSpotSafetyPurchaseV1,
) -> VerifiedZDEXBuybackSpendResultV1:
    """Derive ``q`` only from owned state and an authenticated Spot journal."""

    owned_policy = _snapshot_scalar_dataclass_v1(
        spend_policy,
        ZDEXBuybackSpendPolicyV1,
        name="ZDEX buyback spend policy",
    )
    owned_cadence = _snapshot_cadence_v1(cadence)
    owned_fee_policy = _snapshot_fee_policy_v1(fee_policy)
    owned_fee_state = _snapshot_fee_state_v1(fee_pre_state)
    owned_fee_context = _snapshot_scalar_dataclass_v1(
        fee_context,
        ZDEXFeeAllocationContextV1,
        name="ZDEX buyback fee context",
    )
    owned_fee_command = _snapshot_scalar_dataclass_v1(
        fee_command,
        ZDEXFeeAllocationCommandV1,
        name="ZDEX buyback fee command",
    )
    owned_occurrence = _snapshot_occurrence_v1(occurrence)
    if type(safety_purchase) is not VerifiedZDEXBuybackSpotSafetyPurchaseV1:
        raise TypeError("ZDEX buyback safety purchase must be verifier-constructed")
    journal = safety_purchase.journal
    same_occurrence = (
        owned_occurrence.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        and journal.chain_id == owned_occurrence.chain_id
        and journal.deployment_root == owned_occurrence.deployment_root
        and journal.profile_root == owned_occurrence.profile_root
        and journal.route_release_id == owned_occurrence.route_release_id
        and journal.command_occurrence_id == owned_occurrence.occurrence_id
        and journal.global_pre_state_root == owned_occurrence.pre_state_root
        and journal.consensus_height == owned_occurrence.height
        and journal.quote_asset_id == owned_policy.quote_asset_id
        and owned_fee_context.chain_id == owned_occurrence.chain_id
        and owned_fee_context.deployment_root == owned_occurrence.deployment_root
        and owned_fee_context.writer_epoch == journal.writer_epoch
    )
    if not same_occurrence:
        return _reject_safety_mismatch_v1(owned_cadence, owned_fee_state)
    context = ZDEXBuybackSpendContextV1(
        profile_root=owned_occurrence.profile_root,
        route_release_id=owned_occurrence.route_release_id,
        command_occurrence_id=owned_occurrence.occurrence_id,
        expected_fee_pre_state_root=owned_fee_state.state_root,
        expected_cadence_pre_state_root=owned_cadence.state_root,
        safety_limit_binding_root=safety_purchase.binding_root,
        quote_asset_id=journal.quote_asset_id,
        current_height=owned_occurrence.height,
        route_safe_quote_limit_atoms=journal.route_safe_quote_limit_atoms,
    )
    result = transition_zdex_buyback_spend_v1(
        owned_policy,
        owned_cadence,
        owned_fee_policy,
        owned_fee_state,
        owned_fee_context,
        owned_fee_command,
        context,
    )
    if type(result) is ZDEXBuybackSpendRejectedV1:
        return result
    if (
        type(result) is not ZDEXBuybackSpendAcceptedV1
        or result.intent.quote_spend_atoms != journal.quote_amount_in_atoms
        or result.intent.safety_limit_binding_root != safety_purchase.binding_root
    ):
        return _reject_safety_mismatch_v1(owned_cadence, owned_fee_state)
    return VerifiedZDEXBuybackSpendV1(
        _VERIFIED_ZDEX_BUYBACK_SPEND_TOKEN_V1,
        _VerifiedZDEXBuybackSpendFieldsV1(
            result,
            safety_purchase.binding_root,
            journal.global_pre_state_root,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_BUYBACK_SPEND_SCHEMA_V1",
    "VerifiedZDEXBuybackSpendResultV1",
    "VerifiedZDEXBuybackSpendV1",
    "transition_verified_zdex_buyback_spend_shadow_v1",
]
