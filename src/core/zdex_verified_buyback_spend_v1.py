"""Bind the buyback spend core to one authenticated Spot safety receipt.

This unmounted SHADOW adapter removes consensus height and the route-safe spend
limit from caller control.  It does not compose the Spot and tokenomics lane
receipts or authorize publication.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from typing import Final, TypeAlias

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import _snapshot_occurrence_v1
from .zdex_atomic_buyback_state_v1 import ZDEXAtomicBuybackTokenomicsStateV1
from .zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendAcceptedV1,
    ZDEXBuybackSpendContextV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
    transition_zdex_buyback_spend_v1,
)
from .zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
)

VERIFIED_ZDEX_BUYBACK_SPEND_SCHEMA_V1: Final = "zenodex/verified-zdex-buyback-spend/v1"
_VERIFIED_ZDEX_BUYBACK_SPEND_TOKEN_V1 = object()


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackSpendFieldsV1:
    accepted: ZDEXBuybackSpendAcceptedV1
    safety_receipt_binding_root: str
    global_pre_state_root: str
    tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    tokenomics_post_state: ZDEXAtomicBuybackTokenomicsStateV1


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

    @property
    def tokenomics_pre_state(self) -> ZDEXAtomicBuybackTokenomicsStateV1:
        return deepcopy(self._fields.tokenomics_pre_state)

    @property
    def tokenomics_post_state(self) -> ZDEXAtomicBuybackTokenomicsStateV1:
        return deepcopy(self._fields.tokenomics_post_state)


VerifiedZDEXBuybackSpendResultV1: TypeAlias = (
    VerifiedZDEXBuybackSpendV1 | ZDEXBuybackSpendRejectedV1
)


def _reject_safety_mismatch_v1(
    state: ZDEXAtomicBuybackTokenomicsStateV1,
    quote_asset_id: str,
) -> ZDEXBuybackSpendRejectedV1:
    cadence = state.cadence_state_for(quote_asset_id)
    fee_state = state.fee_state_for(quote_asset_id)
    return ZDEXBuybackSpendRejectedV1(
        ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH,
        None,
        cadence,
        cadence,
        fee_state,
        fee_state,
    )


def transition_verified_zdex_buyback_spend_shadow_v1(
    occurrence: EconomicCommandOccurrenceV1,
    safety_purchase: VerifiedZDEXBuybackSpotSafetyPurchaseV1,
) -> VerifiedZDEXBuybackSpendResultV1:
    """Derive ``q`` only from receipt-owned policy, state, and command data."""

    owned_occurrence = _snapshot_occurrence_v1(occurrence)
    if type(safety_purchase) is not VerifiedZDEXBuybackSpotSafetyPurchaseV1:
        raise TypeError("ZDEX buyback safety purchase must be verifier-constructed")
    journal = safety_purchase.journal
    state = safety_purchase.tokenomics_pre_state
    owned_policy = safety_purchase.spend_policy
    owned_fee_policy = safety_purchase.fee_policy
    owned_fee_context = safety_purchase.fee_context
    owned_fee_command = safety_purchase.fee_command
    fee_ingress = safety_purchase.fee_ingress
    owned_cadence = state.cadence_state_for(journal.quote_asset_id)
    owned_fee_state = state.fee_state_for(journal.quote_asset_id)
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
        and fee_ingress.command_occurrence_id == owned_occurrence.occurrence_id
        and fee_ingress.global_pre_state_root == owned_occurrence.pre_state_root
        and fee_ingress.profile_root == owned_occurrence.profile_root
        and fee_ingress.fee_state_root == owned_fee_state.state_root
        and fee_ingress.fee_asset_id == journal.quote_asset_id
        and fee_ingress.fee_ingress_atoms == owned_fee_state.fee_ingress_atoms
        and owned_fee_command.fee_charged_atoms == fee_ingress.fee_ingress_atoms
        and fee_ingress.authority_head_root == safety_purchase.authority_head_root
        and fee_ingress.verifier_binding_root == safety_purchase.verifier_binding_root
    )
    if not same_occurrence:
        return _reject_safety_mismatch_v1(state, journal.quote_asset_id)
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
        return _reject_safety_mismatch_v1(state, journal.quote_asset_id)
    post_state = state.with_buyback_result(
        fee_state=result.fee_post_state,
        cadence_state=result.cadence_post_state,
    )
    return VerifiedZDEXBuybackSpendV1(
        _VERIFIED_ZDEX_BUYBACK_SPEND_TOKEN_V1,
        _VerifiedZDEXBuybackSpendFieldsV1(
            result,
            safety_purchase.binding_root,
            journal.global_pre_state_root,
            state,
            post_state,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_BUYBACK_SPEND_SCHEMA_V1",
    "VerifiedZDEXBuybackSpendResultV1",
    "VerifiedZDEXBuybackSpendV1",
    "transition_verified_zdex_buyback_spend_shadow_v1",
]
