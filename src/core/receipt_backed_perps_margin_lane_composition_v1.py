"""Receipt-backed structural composition for one `PERPS_MARKET` margin leaf.

The module receipt is cryptographically verified before this boundary. This
module replays the deterministic perps coordinator over exact typed projections
and binds the resulting journal to the profile-selected coordinator release.
The output remains structural until a separate coordinator receipt verifier
checks the selected image and exact journal.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneModuleTransitionJournalV1,
    ReceiptKindV1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .lane_module_receipt_verification_v1 import VerifiedLaneModuleTransitionV1
from .perps_margin_lane_coordinator_v1 import (
    PerpsMarginLaneCompositionAcceptedV1,
    PerpsMarginLaneCompositionCandidateV1,
    PerpsMarginLaneCoordinatorContextV1,
    PerpsMarginLaneProjectionV1,
    PerpsMarginModuleCompatibilityV1,
    compose_perps_margin_lane_single_v1,
)
from .perps_margin_types_v1 import PerpsMarginPrivatePortV1
from .receipt_backed_asset_lane_composition_v1 import (
    LaneCompositionAuthorityLevelV1,
)

RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_SCHEMA_V1: Final = (
    "zenodex/receipt-backed-perps-margin-lane-composition/v1"
)
_RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_TOKEN = object()


@dataclass(frozen=True, slots=True)
class ReceiptBackedPerpsMarginLaneCompositionCandidateV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    coordinator_context: PerpsMarginLaneCoordinatorContextV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: PerpsMarginPrivatePortV1
    pre_state: PerpsMarginLaneProjectionV1
    post_state: PerpsMarginLaneProjectionV1
    module_effects: GlobalEconomicEffectPlanV1
    verified_module: VerifiedLaneModuleTransitionV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.occurrence, EconomicCommandOccurrenceV1, "command occurrence"),
            (
                self.coordinator_context,
                PerpsMarginLaneCoordinatorContextV1,
                "coordinator context",
            ),
            (self.module_journal, LaneModuleTransitionJournalV1, "module journal"),
            (self.private_port, PerpsMarginPrivatePortV1, "private port"),
            (self.pre_state, PerpsMarginLaneProjectionV1, "pre-state projection"),
            (self.post_state, PerpsMarginLaneProjectionV1, "post-state projection"),
            (self.module_effects, GlobalEconomicEffectPlanV1, "module effects"),
            (
                self.verified_module,
                VerifiedLaneModuleTransitionV1,
                "verified module witness",
            ),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"receipt-backed perps lane {label} must be exact typed data")


@dataclass(frozen=True, slots=True)
class _ReceiptBackedPerpsMarginLaneCompositionFieldsV1:
    authority_level: LaneCompositionAuthorityLevelV1
    profile_id: str
    route_release_id: str
    lane_id: LaneIdV1
    declared_coordinator_release_id: str
    command_occurrence_id: str
    verified_module_binding_root: str
    module_receipt_digest: str
    module_journal_digest: str
    lane_journal_root: str
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    terminal_obligations_root: str


class ReceiptBackedPerpsMarginLaneCompositionV1:
    """Opaque perps structural candidate without coordinator-proof authority."""

    _fields: _ReceiptBackedPerpsMarginLaneCompositionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _ReceiptBackedPerpsMarginLaneCompositionFieldsV1,
    ) -> None:
        if token is not _RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_TOKEN:
            raise TypeError(
                "ReceiptBackedPerpsMarginLaneCompositionV1 is composition-constructed"
            )
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("ReceiptBackedPerpsMarginLaneCompositionV1 is immutable")

    @property
    def authority_level(self) -> LaneCompositionAuthorityLevelV1:
        return self._fields.authority_level

    @property
    def profile_id(self) -> str:
        return self._fields.profile_id

    @property
    def route_release_id(self) -> str:
        return self._fields.route_release_id

    @property
    def lane_id(self) -> LaneIdV1:
        return self._fields.lane_id

    @property
    def declared_coordinator_release_id(self) -> str:
        return self._fields.declared_coordinator_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def verified_module_binding_root(self) -> str:
        return self._fields.verified_module_binding_root

    @property
    def module_receipt_digest(self) -> str:
        return self._fields.module_receipt_digest

    @property
    def module_journal_digest(self) -> str:
        return self._fields.module_journal_digest

    @property
    def lane_journal_root(self) -> str:
        return self._fields.lane_journal_root

    @property
    def pre_lane_root(self) -> str:
        return self._fields.pre_lane_root

    @property
    def post_lane_root(self) -> str:
        return self._fields.post_lane_root

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

    @property
    def terminal_obligations_root(self) -> str:
        return self._fields.terminal_obligations_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "receipt-backed-perps-margin-lane-composition-v1",
            {
                "schema": RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_SCHEMA_V1,
                "authority_level": self.authority_level,
                "profile_id": self.profile_id,
                "route_release_id": self.route_release_id,
                "lane_id": self.lane_id,
                "declared_coordinator_release_id": self.declared_coordinator_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "verified_module_binding_root": self.verified_module_binding_root,
                "module_receipt_digest": self.module_receipt_digest,
                "module_journal_digest": self.module_journal_digest,
                "lane_journal_root": self.lane_journal_root,
                "pre_lane_root": self.pre_lane_root,
                "post_lane_root": self.post_lane_root,
                "effect_plan_root": self.effect_plan_root,
                "terminal_obligations_root": self.terminal_obligations_root,
            },
        )


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_profile_route_bindings_v1(
    candidate: ReceiptBackedPerpsMarginLaneCompositionCandidateV1,
) -> RouteReleaseV1:
    profile = candidate.profile
    occurrence = candidate.occurrence
    context = candidate.coordinator_context
    journal = candidate.module_journal
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("receipt-backed perps lane profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != (LaneIdV1.PERPS_MARKET,):
        raise ValueError("receipt-backed perps lane requires the single perps route")
    if len(route.module_release_ids) != 1:
        raise ValueError("receipt-backed perps lane requires one module release")
    coordinator = profile.lane_coordinator_registry.release_for(LaneIdV1.PERPS_MARKET)
    if coordinator.status is not ReleaseStatusV1.ACTIVE_NEW or not coordinator.accepts_new_objects:
        raise ValueError("receipt-backed perps lane coordinator is not ACTIVE_NEW")
    if context.coordinator_release_id != coordinator.coordinator_release_id:
        raise ValueError("receipt-backed perps lane coordinator release mismatch")

    exact_bindings = (
        (occurrence.profile_root, profile.profile_id, "occurrence profile"),
        (context.profile_root, profile.profile_id, "coordinator profile"),
        (context.chain_id, occurrence.chain_id, "coordinator chain"),
        (context.deployment_root, occurrence.deployment_root, "coordinator deployment"),
        (context.command_occurrence_id, occurrence.occurrence_id, "coordinator occurrence"),
        (journal.chain_id, occurrence.chain_id, "module journal chain"),
        (journal.deployment_root, occurrence.deployment_root, "module journal deployment"),
        (journal.profile_root, profile.profile_id, "module journal profile"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "module journal occurrence"),
        (journal.module_release_id, route.module_release_ids[0], "route module release"),
    )
    for actual, expected, label in exact_bindings:
        if actual != expected:
            raise ValueError(f"receipt-backed perps lane {label} mismatch")
    if context.writer_epoch != profile.authority_epoch or journal.writer_epoch != profile.authority_epoch:
        raise ValueError("receipt-backed perps lane writer epoch mismatch")

    expected_compatibility = (
        PerpsMarginModuleCompatibilityV1(
            route.module_release_ids[0],
            candidate.private_port.producer_module_schema,
        ),
    )
    if context.compatible_modules != expected_compatibility:
        raise ValueError("receipt-backed perps lane compatible module set mismatch")
    return route


def _require_verified_module_binding_v1(
    candidate: ReceiptBackedPerpsMarginLaneCompositionCandidateV1,
) -> None:
    verified = candidate.verified_module
    journal = candidate.module_journal
    if verified.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("receipt-backed perps lane requires a succinct module receipt")
    if verified.command_occurrence_id != candidate.occurrence.occurrence_id:
        raise ValueError("verified module occurrence mismatch")
    if verified.module_journal_root != journal.journal_root:
        raise ValueError("verified module journal root mismatch")
    journal_digest = _sha256_root_v1(canonical_global_bytes_v1(journal))
    if verified.module_journal_digest != journal_digest:
        raise ValueError("verified module journal digest mismatch")
    release = candidate.profile.lane_registry.release_for(LaneIdV1.PERPS_MARKET)
    if verified.expected_image_id != release.guest_image_id:
        raise ValueError("verified module image mismatch")


def compose_receipt_backed_perps_margin_lane_single_v1(
    candidate: ReceiptBackedPerpsMarginLaneCompositionCandidateV1,
) -> ReceiptBackedPerpsMarginLaneCompositionV1:
    """Replay one perps coordinator and bind its exact module receipt input."""

    if type(candidate) is not ReceiptBackedPerpsMarginLaneCompositionCandidateV1:
        raise TypeError("receipt-backed perps lane candidate must be exact typed data")
    candidate.__post_init__()
    route = _require_profile_route_bindings_v1(candidate)
    _require_verified_module_binding_v1(candidate)
    result = compose_perps_margin_lane_single_v1(
        PerpsMarginLaneCompositionCandidateV1(
            candidate.coordinator_context,
            candidate.module_journal,
            candidate.private_port,
            candidate.pre_state,
            candidate.post_state,
            candidate.module_effects,
        )
    )
    if type(result) is not PerpsMarginLaneCompositionAcceptedV1:
        raise ValueError(f"perps lane composition rejected: {result.code.value}")
    if result.lane_journal.ordered_module_journal_roots != (
        candidate.verified_module.module_journal_root,
    ):
        raise ValueError("receipt-backed perps lane ordered module roots mismatch")

    return ReceiptBackedPerpsMarginLaneCompositionV1(
        _RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_TOKEN,
        _ReceiptBackedPerpsMarginLaneCompositionFieldsV1(
            LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY,
            candidate.profile.profile_id,
            route.route_release_id,
            LaneIdV1.PERPS_MARKET,
            candidate.coordinator_context.coordinator_release_id,
            candidate.occurrence.occurrence_id,
            candidate.verified_module.binding_root,
            candidate.verified_module.receipt_digest,
            candidate.verified_module.module_journal_digest,
            result.lane_journal.journal_root,
            result.lane_journal.pre_lane_root,
            result.lane_journal.post_lane_root,
            result.lane_journal.effect_plan_root,
            result.lane_journal.terminal_obligations_root,
        ),
    )


__all__ = [
    "RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_SCHEMA_V1",
    "ReceiptBackedPerpsMarginLaneCompositionCandidateV1",
    "ReceiptBackedPerpsMarginLaneCompositionV1",
    "compose_receipt_backed_perps_margin_lane_single_v1",
]
