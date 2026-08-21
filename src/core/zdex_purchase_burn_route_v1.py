"""Pure two-lane composer for an authenticated ZDEX purchase and burn."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXAMMPurchaseV1,
    VerifiedZDEXBurnV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCandidateV1:
    route_release: RouteReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    purchase_journal: ZDEXAMMPurchaseJournalV1
    purchase_effects: GlobalEconomicEffectPlanV1
    verified_purchase: VerifiedZDEXAMMPurchaseV1
    burn_journal: ZDEXBurnJournalV1
    burn_effects: GlobalEconomicEffectPlanV1
    verified_burn: VerifiedZDEXBurnV1

    def __post_init__(self) -> None:
        expected = (
            (self.route_release, RouteReleaseV1, "route release"),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
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


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteAcceptedV1:
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    effects: GlobalEconomicEffectPlanV1
    terminal_obligations_root: str = ZERO_ROOT_V1

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
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                burn.pre_tokenomics_lane_root,
                burn.post_tokenomics_lane_root,
            ),
        ),
        occurrence_consumptions=(candidate.occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _binding_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    occurrence_id: str,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    if (
        route.route_release_id != occurrence.route_release_id
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
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH
    expected = _WitnessExpectationV1(
        route.route_release_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
    )
    if not _witness_matches(
        candidate.verified_purchase,
        expected=expected,
        journal=purchase,
        effects=candidate.purchase_effects,
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    if not _witness_matches(
        candidate.verified_burn,
        expected=expected,
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
        purchase.buyback_budget_occurrence_root
        != burn.buyback_budget_occurrence_root
        or purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
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

    if type(candidate) is not ZDEXPurchaseBurnRouteCandidateV1:
        raise TypeError("ZDEX purchase-burn route candidate must be exact typed data")
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    occurrence_id = occurrence.occurrence_id
    reject_code = _binding_reject_code(candidate, occurrence_id)
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
        effects,
    )


__all__ = [
    "ZDEXPurchaseBurnRouteAcceptedV1",
    "ZDEXPurchaseBurnRouteCandidateV1",
    "ZDEXPurchaseBurnRouteRejectedV1",
    "ZDEXPurchaseBurnRouteResultV1",
    "compose_zdex_purchase_burn_route_v1",
]
