"""Closed candidate, acceptance, and V3 journal values for ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TypeAlias

from .global_economic_profile_snapshot_v1 import _snapshot_route_release_v1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    RouteReleaseV1,
    _require_nonnegative_int,
    _require_root,
    hash_global_v1,
)
from .zdex_fee_allocation_receipt_verification_v1 import (
    VerifiedZDEXFeeAllocationV1,
    _snapshot_fee_journal_v1,
    _snapshot_fee_policy_v1,
    _snapshot_fee_state_v1,
    _VerifiedZDEXFeeAllocationFieldsV1,
)
from .zdex_fee_allocation_v1 import (
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeStateV1,
)
from .zdex_purchase_burn_profile_v2 import (
    GovernedZDEXPurchaseBurnRouteV2,
    _snapshot_governed_route_v2,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
    _GovernedVerifiedZDEXAMMPurchaseFieldsV2,
    _snapshot_burn_journal_v1,
    _snapshot_purchase_journal_v2,
    _VerifiedZDEXLaneFieldsV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
)
from .zdex_purchase_burn_route_v1 import ZDEXPurchaseBurnRouteRejectedV1

ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3 = (
    "zenodex/zdex-purchase-burn-route-composition/v3"
)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCandidateV2:
    governed_profile: GovernedZDEXPurchaseBurnRouteV2
    route_release: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    buyback_budget_occurrence: ZDEXFeeAllocationOccurrenceV1
    verified_buyback_budget: VerifiedZDEXFeeAllocationV1
    buyback_budget_policy: ZDEXFeeAllocationPolicyV1
    buyback_budget_pre_state: ZDEXFeeStateV1
    purchase_journal: ZDEXAMMPurchaseJournalV2
    purchase_effects: GlobalEconomicEffectPlanV1
    verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2
    burn_journal: ZDEXBurnJournalV1
    burn_effects: GlobalEconomicEffectPlanV1
    verified_burn: VerifiedZDEXBurnV1

    def __post_init__(self) -> None:
        expected = (
            (self.governed_profile, GovernedZDEXPurchaseBurnRouteV2),
            (self.route_release, RouteReleaseV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.buyback_budget_occurrence, ZDEXFeeAllocationOccurrenceV1),
            (self.verified_buyback_budget, VerifiedZDEXFeeAllocationV1),
            (self.buyback_budget_policy, ZDEXFeeAllocationPolicyV1),
            (self.buyback_budget_pre_state, ZDEXFeeStateV1),
            (self.purchase_journal, ZDEXAMMPurchaseJournalV2),
            (self.purchase_effects, GlobalEconomicEffectPlanV1),
            (self.verified_purchase, GovernedVerifiedZDEXAMMPurchaseV2),
            (self.burn_journal, ZDEXBurnJournalV1),
            (self.burn_effects, GlobalEconomicEffectPlanV1),
            (self.verified_burn, VerifiedZDEXBurnV1),
        )
        if any(type(value) is not expected_type for value, expected_type in expected):
            raise TypeError("ZDEX purchase-burn V2 candidate requires exact typed data")


def _require_exact_witnesses_v2(candidate: ZDEXPurchaseBurnRouteCandidateV2) -> None:
    purchase_fields = candidate.verified_purchase._fields
    if type(purchase_fields) is not _GovernedVerifiedZDEXAMMPurchaseFieldsV2:
        raise TypeError("ZDEX purchase-burn V2 governed purchase fields are not closed")
    leaf = purchase_fields.verified_leaf
    if type(leaf) is not VerifiedZDEXAMMPurchaseV2:
        raise TypeError("ZDEX purchase-burn V2 purchase leaf is not closed")
    witnesses = (
        (leaf._fields, _VerifiedZDEXLaneFieldsV1, "purchase leaf"),
        (candidate.verified_burn._fields, _VerifiedZDEXLaneFieldsV1, "burn"),
        (
            candidate.verified_buyback_budget._fields,
            _VerifiedZDEXFeeAllocationFieldsV1,
            "budget",
        ),
    )
    for fields, expected_type, name in witnesses:
        if type(fields) is not expected_type:
            raise TypeError(f"ZDEX purchase-burn V2 {name} witness fields are not closed")
        _require_exact_dataclass_scalars_v1(fields, name=f"ZDEX purchase-burn V2 {name}")


def _snapshot_route_candidate_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> ZDEXPurchaseBurnRouteCandidateV2:
    if type(candidate) is not ZDEXPurchaseBurnRouteCandidateV2:
        raise TypeError("ZDEX purchase-burn V2 candidate must be exact typed data")
    candidate.__post_init__()
    _require_exact_witnesses_v2(candidate)
    return replace(
        candidate,
        governed_profile=_snapshot_governed_route_v2(candidate.governed_profile),
        route_release=_snapshot_route_release_v1(candidate.route_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        buyback_budget_occurrence=_snapshot_fee_journal_v1(
            candidate.buyback_budget_occurrence
        ),
        buyback_budget_policy=_snapshot_fee_policy_v1(candidate.buyback_budget_policy),
        buyback_budget_pre_state=_snapshot_fee_state_v1(
            candidate.buyback_budget_pre_state
        ),
        purchase_journal=_snapshot_purchase_journal_v2(candidate.purchase_journal),
        purchase_effects=_snapshot_effect_plan_v1(candidate.purchase_effects),
        burn_journal=_snapshot_burn_journal_v1(candidate.burn_journal),
        burn_effects=_snapshot_effect_plan_v1(candidate.burn_effects),
    )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCompositionJournalV3:
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    verified_budget_binding_root: str
    buyback_execution_policy_root: str
    price_safety_policy_root: str
    price_authority_root: str
    effect_plan_root: str
    terminal_obligations_root: str
    schema: str = ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3

    def __post_init__(self) -> None:
        if type(self.schema) is not str or self.schema != (
            ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3
        ):
            raise ValueError("ZDEX route composition V3 schema mismatch")
        _require_nonnegative_int(self.writer_epoch, name="ZDEX route V3 writer epoch")
        for field_name in (
            "route_release_id",
            "command_occurrence_id",
            "profile_root",
            "verified_budget_binding_root",
            "buyback_execution_policy_root",
            "price_safety_policy_root",
            "price_authority_root",
            "effect_plan_root",
        ):
            value = getattr(self, field_name)
            if type(value) is not str:
                raise TypeError(f"ZDEX route V3 {field_name} must be exact str")
            _require_root(value, name=f"ZDEX route V3 {field_name}")
        if type(self.terminal_obligations_root) is not str:
            raise TypeError("ZDEX route V3 terminal obligations root must be exact str")
        _require_root(
            self.terminal_obligations_root,
            name="ZDEX route V3 terminal obligations root",
            allow_zero=True,
        )
        for field_name in (
            "ordered_lane_journal_roots",
            "ordered_verified_binding_roots",
        ):
            roots = getattr(self, field_name)
            if type(roots) is not tuple or len(roots) != 2:
                raise ValueError(f"ZDEX route V3 {field_name} must contain two roots")
            for root in roots:
                if type(root) is not str:
                    raise TypeError(f"ZDEX route V3 {field_name} requires exact str roots")
                _require_root(root, name=f"ZDEX route V3 {field_name}")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "ordered_lane_journal_roots": self.ordered_lane_journal_roots,
            "ordered_verified_binding_roots": self.ordered_verified_binding_roots,
            "verified_budget_binding_root": self.verified_budget_binding_root,
            "buyback_execution_policy_root": self.buyback_execution_policy_root,
            "price_safety_policy_root": self.price_safety_policy_root,
            "price_authority_root": self.price_authority_root,
            "effect_plan_root": self.effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }

    @property
    def journal_root(self) -> str:
        return hash_global_v1(
            "zdex-purchase-burn-route-composition-v3",
            self.to_canonical(),
        )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteAcceptedV2:
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    verified_budget_binding_root: str
    buyback_execution_policy_root: str
    price_safety_policy_root: str
    price_authority_root: str
    effects: GlobalEconomicEffectPlanV1
    terminal_obligations_root: str

    @property
    def composition_journal_v3(self) -> ZDEXPurchaseBurnRouteCompositionJournalV3:
        return ZDEXPurchaseBurnRouteCompositionJournalV3(
            route_release_id=self.route_release_id,
            command_occurrence_id=self.command_occurrence_id,
            profile_root=self.profile_root,
            writer_epoch=self.writer_epoch,
            ordered_lane_journal_roots=self.ordered_lane_journal_roots,
            ordered_verified_binding_roots=self.ordered_verified_binding_roots,
            verified_budget_binding_root=self.verified_budget_binding_root,
            buyback_execution_policy_root=self.buyback_execution_policy_root,
            price_safety_policy_root=self.price_safety_policy_root,
            price_authority_root=self.price_authority_root,
            effect_plan_root=self.effects.effect_plan_root,
            terminal_obligations_root=self.terminal_obligations_root,
        )


ZDEXPurchaseBurnRouteResultV2: TypeAlias = (
    ZDEXPurchaseBurnRouteAcceptedV2 | ZDEXPurchaseBurnRouteRejectedV1
)


__all__ = [
    "ZDEXPurchaseBurnRouteAcceptedV2",
    "ZDEXPurchaseBurnRouteCandidateV2",
    "ZDEXPurchaseBurnRouteCompositionJournalV3",
    "ZDEXPurchaseBurnRouteResultV2",
    "ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V3",
]
