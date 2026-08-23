"""Pure two-lane composer for an authenticated ZDEX purchase and burn."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_profile_snapshot_v1 import (
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetConservationRowV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneWriteV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
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
    FEE_BUYBACK_PRINCIPAL_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
    transition_zdex_fee_allocation_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXAMMPurchaseV1,
    VerifiedZDEXBurnV1,
    _snapshot_burn_journal_v1,
    _snapshot_purchase_journal_v1,
    _VerifiedZDEXLaneFieldsV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
)
from .zdex_tokenomics_lane_v1 import (
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCandidateV1:
    route_release: RouteReleaseV1
    purchase_module_release: LaneModuleReleaseV1
    burn_module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    buyback_budget_occurrence: ZDEXFeeAllocationOccurrenceV1
    verified_buyback_budget: VerifiedZDEXFeeAllocationV1
    buyback_budget_policy: ZDEXFeeAllocationPolicyV1
    buyback_budget_pre_state: ZDEXFeeStateV1
    purchase_journal: ZDEXAMMPurchaseJournalV1
    purchase_effects: GlobalEconomicEffectPlanV1
    verified_purchase: VerifiedZDEXAMMPurchaseV1
    burn_journal: ZDEXBurnJournalV1
    burn_effects: GlobalEconomicEffectPlanV1
    verified_burn: VerifiedZDEXBurnV1

    def __post_init__(self) -> None:
        expected = (
            (self.route_release, RouteReleaseV1, "route release"),
            (
                self.purchase_module_release,
                LaneModuleReleaseV1,
                "purchase module release",
            ),
            (
                self.burn_module_release,
                LaneModuleReleaseV1,
                "burn module release",
            ),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (
                self.buyback_budget_occurrence,
                ZDEXFeeAllocationOccurrenceV1,
                "buyback budget occurrence",
            ),
            (
                self.verified_buyback_budget,
                VerifiedZDEXFeeAllocationV1,
                "buyback budget witness",
            ),
            (
                self.buyback_budget_policy,
                ZDEXFeeAllocationPolicyV1,
                "buyback budget policy",
            ),
            (
                self.buyback_budget_pre_state,
                ZDEXFeeStateV1,
                "buyback budget pre-state",
            ),
            (self.purchase_journal, ZDEXAMMPurchaseJournalV1, "purchase journal"),
            (self.purchase_effects, GlobalEconomicEffectPlanV1, "purchase effects"),
            (self.verified_purchase, VerifiedZDEXAMMPurchaseV1, "purchase witness"),
            (self.burn_journal, ZDEXBurnJournalV1, "burn journal"),
            (self.burn_effects, GlobalEconomicEffectPlanV1, "burn effects"),
            (self.verified_burn, VerifiedZDEXBurnV1, "burn witness"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(f"ZDEX route {label} must be exact typed data")


def _require_exact_witness_fields_v1(
    witness: VerifiedZDEXAMMPurchaseV1
    | VerifiedZDEXBurnV1
    | VerifiedZDEXFeeAllocationV1,
    *,
    expected_type: type[object],
    name: str,
) -> None:
    fields = witness._fields
    if type(fields) is not expected_type:
        raise TypeError(f"ZDEX route {name} fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name=name)


def _snapshot_route_candidate_v1(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteCandidateV1:
    """Own and exact-check every structured value consumed by the composer."""

    if type(candidate) is not ZDEXPurchaseBurnRouteCandidateV1:
        raise TypeError("ZDEX purchase-burn route candidate must be exact typed data")
    candidate.__post_init__()
    _require_exact_witness_fields_v1(
        candidate.verified_purchase,
        expected_type=_VerifiedZDEXLaneFieldsV1,
        name="purchase witness",
    )
    _require_exact_witness_fields_v1(
        candidate.verified_burn,
        expected_type=_VerifiedZDEXLaneFieldsV1,
        name="burn witness",
    )
    _require_exact_witness_fields_v1(
        candidate.verified_buyback_budget,
        expected_type=_VerifiedZDEXFeeAllocationFieldsV1,
        name="buyback budget witness",
    )
    return replace(
        candidate,
        route_release=_snapshot_route_release_v1(candidate.route_release),
        purchase_module_release=_snapshot_lane_release_v1(
            candidate.purchase_module_release
        ),
        burn_module_release=_snapshot_lane_release_v1(candidate.burn_module_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        buyback_budget_occurrence=_snapshot_fee_journal_v1(
            candidate.buyback_budget_occurrence
        ),
        buyback_budget_policy=_snapshot_fee_policy_v1(
            candidate.buyback_budget_policy
        ),
        buyback_budget_pre_state=_snapshot_fee_state_v1(
            candidate.buyback_budget_pre_state
        ),
        purchase_journal=_snapshot_purchase_journal_v1(
            candidate.purchase_journal
        ),
        purchase_effects=_snapshot_effect_plan_v1(candidate.purchase_effects),
        burn_journal=_snapshot_burn_journal_v1(candidate.burn_journal),
        burn_effects=_snapshot_effect_plan_v1(candidate.burn_effects),
    )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteAcceptedV1:
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    verified_budget_binding_root: str
    effects: GlobalEconomicEffectPlanV1
    terminal_obligations_root: str

    @property
    def composition_root(self) -> str:
        return hash_global_v1(
            "zdex-purchase-burn-route-composition-v1",
            {
                "schema": GLOBAL_SETTLEMENT_ABI_V1,
                "route_release_id": self.route_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "profile_root": self.profile_root,
                "writer_epoch": self.writer_epoch,
                "ordered_lane_journal_roots": self.ordered_lane_journal_roots,
                "ordered_verified_binding_roots": self.ordered_verified_binding_roots,
                "verified_budget_binding_root": self.verified_budget_binding_root,
                "effect_plan_root": self.effects.effect_plan_root,
                "terminal_obligations_root": self.terminal_obligations_root,
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteRejectedV1:
    code: ZDEXPurchaseBurnRouteRejectCodeV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXPurchaseBurnRouteRejectCodeV1:
            raise TypeError("ZDEX route reject code is not closed")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("ZDEX route rejection must carry no effects")


ZDEXPurchaseBurnRouteResultV1 = (
    ZDEXPurchaseBurnRouteAcceptedV1 | ZDEXPurchaseBurnRouteRejectedV1
)


@dataclass(frozen=True, slots=True)
class _WitnessExpectationV1:
    route_release_id: str
    module_release_id: str
    expected_image_id: str
    occurrence_id: str
    profile_root: str
    writer_epoch: int


def _reject(code: ZDEXPurchaseBurnRouteRejectCodeV1) -> ZDEXPurchaseBurnRouteRejectedV1:
    return ZDEXPurchaseBurnRouteRejectedV1(code)


def _witness_matches(
    witness: VerifiedZDEXAMMPurchaseV1 | VerifiedZDEXBurnV1,
    *,
    expected: _WitnessExpectationV1,
    journal: ZDEXAMMPurchaseJournalV1 | ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    journal_bytes = canonical_global_bytes_v1(journal)
    return (
        witness.route_release_id == expected.route_release_id
        and witness.module_release_id == expected.module_release_id
        and witness.expected_image_id == expected.expected_image_id
        and witness.command_occurrence_id == expected.occurrence_id
        and witness.profile_root == expected.profile_root
        and witness.writer_epoch == expected.writer_epoch
        and witness.journal_root == journal.journal_root
        and witness.journal_digest == "0x" + hashlib.sha256(journal_bytes).hexdigest()
        and witness.effect_plan_root == effects.effect_plan_root
        and witness.receipt_kind is ReceiptKindV1.SUCCINCT
    )


def _checked_delta(value: int) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError("ZDEX route aggregate effect exceeds signed 128-bit atoms")
    return value


def _compose_rows(
    purchase: GlobalEconomicEffectPlanV1,
    burn: GlobalEconomicEffectPlanV1,
) -> tuple[EconomicEffectRowV1, ...]:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for plan in (purchase, burn):
        for row in plan.rows:
            exemplar, prior = totals.get(row.key, (row, 0))
            totals[row.key] = (exemplar, _checked_delta(prior + row.delta_atoms))
    return tuple(
        EconomicEffectRowV1(
            exemplar.kind,
            exemplar.principal,
            exemplar.asset,
            exemplar.custody_domain,
            total,
        )
        for _, (exemplar, total) in sorted(totals.items())
        if total != 0
    )


def _compose_conservation(
    purchase: ZDEXAMMPurchaseJournalV1,
    burn: ZDEXBurnJournalV1,
) -> tuple[AssetConservationRowV1, ...]:
    rows = (
        AssetConservationRowV1(
            purchase.quote_asset_id,
            purchase.quote_owned_atoms,
            purchase.quote_owned_atoms,
            purchase.quote_supply_atoms,
            purchase.quote_supply_atoms,
            0,
            0,
        ),
        AssetConservationRowV1(
            purchase.zdex_asset_id,
            purchase.zdex_owned_atoms,
            burn.zdex_owned_post_atoms,
            purchase.zdex_supply_atoms,
            burn.zdex_supply_post_atoms,
            0,
            burn.burned_zdex_atoms,
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.asset))


def _compose_effects(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> GlobalEconomicEffectPlanV1:
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    return GlobalEconomicEffectPlanV1(
        rows=_compose_rows(candidate.purchase_effects, candidate.burn_effects),
        asset_conservation=_compose_conservation(purchase, burn),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                purchase.pre_spot_lane_root,
                purchase.post_spot_lane_root,
            ),
        ),
        occurrence_consumptions=(candidate.occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _budget_bindings_match(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    occurrence_id: str,
) -> bool:
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    budget_root = budget.occurrence_root
    return not any(
        (
            budget.chain_id != occurrence.chain_id,
            budget.deployment_root != occurrence.deployment_root,
            budget.profile_root != occurrence.profile_root,
            budget.writer_epoch != purchase.writer_epoch,
            budget.authorized_buyback_route_release_id
            != candidate.route_release.route_release_id,
            budget.tokenomics_module_release_id != burn.tokenomics_module_release_id,
            budget.command_occurrence_id == occurrence_id,
            budget_root == occurrence_id,
            occurrence.consumed_object_ids != (budget_root,),
            purchase.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1,
        )
    )


def _budget_witness_matches(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    tokenomics_release: LaneModuleReleaseV1,
) -> bool:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    witness = candidate.verified_buyback_budget
    journal_digest = "0x" + hashlib.sha256(
        canonical_global_bytes_v1(budget)
    ).hexdigest()
    return not any(
        (
            witness.authorized_buyback_route_release_id != route.route_release_id,
            witness.allocation_route_release_id
            != budget.allocation_route_release_id,
            witness.module_release_id != burn.tokenomics_module_release_id,
            witness.expected_image_id != tokenomics_release.guest_image_id,
            witness.command_occurrence_id != budget.command_occurrence_id,
            witness.profile_root != occurrence.profile_root,
            witness.writer_epoch != purchase.writer_epoch,
            witness.journal_root != budget.occurrence_root,
            witness.journal_digest != journal_digest,
            witness.effect_plan_root != budget.effect_plan_root,
            witness.policy_root != budget.policy_root,
            witness.fee_asset_id != budget.fee_asset_id,
            witness.buyback_quote_atoms != budget.buyback_quote_atoms,
            witness.pre_lane_root != budget.pre_lane_root,
            witness.post_lane_root != budget.post_lane_root,
            witness.receipt_kind is not ReceiptKindV1.SUCCINCT,
        )
    )


def _budget_allocation_recomputes(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> bool:
    budget = candidate.buyback_budget_occurrence
    policy = candidate.buyback_budget_policy
    if policy != candidate_zdex_fee_allocation_policy_v1():
        return False
    context = ZDEXFeeAllocationContextV1(
        chain_id=budget.chain_id,
        deployment_root=budget.deployment_root,
        profile_root=budget.profile_root,
        writer_epoch=budget.writer_epoch,
        allocation_route_release_id=budget.allocation_route_release_id,
        authorized_buyback_route_release_id=(
            budget.authorized_buyback_route_release_id
        ),
        tokenomics_module_release_id=budget.tokenomics_module_release_id,
        command_occurrence_id=budget.command_occurrence_id,
        policy_root=budget.policy_root,
    )
    recomputed = transition_zdex_fee_allocation_v1(
        context,
        candidate.buyback_budget_pre_state,
        policy,
        ZDEXFeeAllocationCommandV1(budget.fee_charged_atoms),
    )
    return (
        type(recomputed) is ZDEXFeeAllocationAcceptedV1
        and recomputed.occurrence == budget
    )


def _binding_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    occurrence_id: str,
    purchase_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    if (
        route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or route.module_release_ids
        != (purchase_release.release_id, burn_release.release_id)
        or purchase_release.lane_id is not LaneIdV1.SPOT_LIQUIDITY
        or burn_release.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or purchase.spot_module_release_id != purchase_release.release_id
        or burn.tokenomics_module_release_id != burn_release.release_id
        or route.route_release_id != occurrence.route_release_id
        or route.route_release_id != purchase.route_release_id
        or route.route_release_id != burn.route_release_id
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.ROUTE_BINDING_MISMATCH
    if purchase.command_occurrence_id != occurrence_id or burn.command_occurrence_id != occurrence_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH
    if (
        purchase.profile_root != occurrence.profile_root
        or burn.profile_root != occurrence.profile_root
        or purchase.writer_epoch != burn.writer_epoch
        or purchase.chain_id != occurrence.chain_id
        or burn.chain_id != occurrence.chain_id
        or purchase.deployment_root != occurrence.deployment_root
        or burn.deployment_root != occurrence.deployment_root
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH
    if not _budget_bindings_match(candidate, occurrence_id):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if not _budget_witness_matches(candidate, burn_release):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if not _budget_allocation_recomputes(candidate):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    purchase_expected = _WitnessExpectationV1(
        route.route_release_id,
        purchase_release.release_id,
        purchase_release.guest_image_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
    )
    if not _witness_matches(
        candidate.verified_purchase,
        expected=purchase_expected,
        journal=purchase,
        effects=candidate.purchase_effects,
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    burn_expected = _WitnessExpectationV1(
        route.route_release_id,
        burn_release.release_id,
        burn_release.guest_image_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
    )
    if not _witness_matches(
        candidate.verified_burn,
        expected=burn_expected,
        journal=burn,
        effects=candidate.burn_effects,
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH
    return None


def _economic_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    if purchase.zdex_asset_id != burn.zdex_asset_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.ASSET_MISMATCH
    if burn.purchase_occurrence_root != purchase.journal_root:
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_OCCURRENCE_MISMATCH
    if purchase.purchased_zdex_atoms != burn.burned_zdex_atoms:
        return ZDEXPurchaseBurnRouteRejectCodeV1.AMOUNT_MISMATCH
    if (
        purchase.burn_bucket_id != burn.burn_bucket_id
        or purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_BUCKET_MISMATCH
    if (
        purchase.buyback_budget_occurrence_root != budget.occurrence_root
        or burn.buyback_budget_occurrence_root != budget.occurrence_root
        or purchase.quote_asset_id != budget.fee_asset_id
        or purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
        or purchase.quote_amount_in_atoms != budget.buyback_quote_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if (
        purchase.zdex_owned_atoms != burn.zdex_owned_pre_atoms
        or purchase.zdex_supply_atoms != burn.zdex_supply_pre_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.CONSERVATION_HISTORY_DISCONNECTED
    return None


def compose_zdex_purchase_burn_route_v1(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteResultV1:
    """Pair two verified leaf outputs and derive one exact route effect plan."""

    candidate = _snapshot_route_candidate_v1(candidate)
    route = candidate.route_release
    purchase_release = candidate.purchase_module_release
    burn_release = candidate.burn_module_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    occurrence_id = occurrence.occurrence_id
    reject_code = _binding_reject_code(
        candidate,
        occurrence_id,
        purchase_release,
        burn_release,
    )
    if reject_code is not None:
        return _reject(reject_code)
    reject_code = _economic_reject_code(candidate)
    if reject_code is not None:
        return _reject(reject_code)

    burn = candidate.burn_journal

    effects = _compose_effects(candidate)
    return ZDEXPurchaseBurnRouteAcceptedV1(
        route.route_release_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
        (purchase.journal_root, burn.journal_root),
        (
            candidate.verified_purchase.binding_root,
            candidate.verified_burn.binding_root,
        ),
        candidate.verified_buyback_budget.binding_root,
        effects,
        zdex_tokenomics_complete_lane_obligation_root_v1(),
    )


__all__ = [
    "ZDEXPurchaseBurnRouteAcceptedV1",
    "ZDEXPurchaseBurnRouteCandidateV1",
    "ZDEXPurchaseBurnRouteRejectedV1",
    "ZDEXPurchaseBurnRouteResultV1",
    "compose_zdex_purchase_burn_route_v1",
]
