"""Receipt-backed structural composition for the `ASSET_TRANSFER` lane.

This boundary pairs one opaque, receipt-verified module witness with the exact
module journal consumed by the deterministic asset-lane coordinator. Its output
is a structural candidate for a future coordinator-proof verifier. It binds the
profile-selected coordinator release but grants no route, epoch, publication, or
settlement authority until a separate coordinator receipt verifier accepts the
exact governed image and lane journal.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final

from .asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from .asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1,
    AssetLanePrivatePortV1,
)
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

RECEIPT_BACKED_ASSET_LANE_COMPOSITION_SCHEMA_V1: Final = (
    "zenodex/receipt-backed-asset-lane-composition/v1"
)
_RECEIPT_BACKED_ASSET_LANE_COMPOSITION_TOKEN = object()


class LaneCompositionAuthorityLevelV1(str, Enum):
    RECEIPT_BACKED_STRUCTURAL_ONLY = "RECEIPT_BACKED_STRUCTURAL_ONLY"


@dataclass(frozen=True, slots=True)
class ReceiptBackedAssetLaneCompositionCandidateV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    coordinator_context: AssetLaneCoordinatorContextV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: AssetLanePrivatePortV1
    module_effects: GlobalEconomicEffectPlanV1
    verified_module: VerifiedLaneModuleTransitionV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.occurrence, EconomicCommandOccurrenceV1, "command occurrence"),
            (
                self.coordinator_context,
                AssetLaneCoordinatorContextV1,
                "coordinator context",
            ),
            (self.module_journal, LaneModuleTransitionJournalV1, "module journal"),
            (self.private_port, AssetLanePrivatePortV1, "private port"),
            (self.module_effects, GlobalEconomicEffectPlanV1, "module effects"),
            (
                self.verified_module,
                VerifiedLaneModuleTransitionV1,
                "verified module witness",
            ),
        )
        for value, expected_type, label in expected_types:
            # Exact types (Opus P30 NEW-4): the composition reads roots through
            # properties a subclass could override.
            if type(value) is not expected_type:
                raise TypeError(f"receipt-backed lane {label} must be the exact typed value")


@dataclass(frozen=True, slots=True)
class _ReceiptBackedAssetLaneCompositionFieldsV1:
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


class ReceiptBackedAssetLaneCompositionV1:
    """Opaque structural candidate without coordinator-proof authority."""

    _fields: _ReceiptBackedAssetLaneCompositionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _ReceiptBackedAssetLaneCompositionFieldsV1,
    ) -> None:
        if token is not _RECEIPT_BACKED_ASSET_LANE_COMPOSITION_TOKEN:
            raise TypeError("ReceiptBackedAssetLaneCompositionV1 is composition-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("ReceiptBackedAssetLaneCompositionV1 is immutable")

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
            "receipt-backed-asset-lane-composition-v1",
            {
                "schema": RECEIPT_BACKED_ASSET_LANE_COMPOSITION_SCHEMA_V1,
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
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1,
) -> RouteReleaseV1:
    profile = candidate.profile
    occurrence = candidate.occurrence
    context = candidate.coordinator_context
    journal = candidate.module_journal
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("receipt-backed lane profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != (LaneIdV1.ASSET_TRANSFER,):
        raise ValueError("receipt-backed lane requires the single asset lane route")
    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    if (
        coordinator_release.status is not ReleaseStatusV1.ACTIVE_NEW
        or not coordinator_release.accepts_new_objects
    ):
        raise ValueError("receipt-backed lane selected coordinator release is not ACTIVE_NEW")
    if context.coordinator_release_id != coordinator_release.coordinator_release_id:
        raise ValueError("receipt-backed lane selected coordinator release mismatch")

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
            raise ValueError(f"receipt-backed lane {label} mismatch")
    if (
        context.writer_epoch != profile.authority_epoch
        or journal.writer_epoch != profile.authority_epoch
    ):
        raise ValueError("receipt-backed lane writer epoch mismatch")

    expected_compatibility = (
        AssetLaneModuleCompatibilityV1(
            route.module_release_ids[0],
            candidate.private_port.producer_module_schema,
        ),
    )
    if context.compatible_modules != expected_compatibility:
        raise ValueError("receipt-backed lane compatible module set mismatch")
    return route


def _require_verified_module_binding_v1(
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1,
) -> None:
    verified = candidate.verified_module
    journal = candidate.module_journal
    if verified.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("receipt-backed lane requires a succinct module receipt")
    if verified.command_occurrence_id != candidate.occurrence.occurrence_id:
        raise ValueError("verified module occurrence mismatch")
    if verified.module_journal_root != journal.journal_root:
        raise ValueError("verified module journal root mismatch")
    journal_digest = _sha256_root_v1(canonical_global_bytes_v1(journal))
    if verified.module_journal_digest != journal_digest:
        raise ValueError("verified module journal digest mismatch")
    release = candidate.profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    if verified.expected_image_id != release.guest_image_id:
        raise ValueError("verified module image mismatch")


def compose_receipt_backed_asset_lane_single_v1(
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1,
) -> ReceiptBackedAssetLaneCompositionV1:
    """Bind one verified module receipt to deterministic lane composition.

    The returned witness is structurally checked and receipt-backed at the
    module layer. It remains ineligible for route or settlement admission until
    a governed coordinator image and its exact journal are cryptographically
    verified by a separate boundary.
    """

    if type(candidate) is not ReceiptBackedAssetLaneCompositionCandidateV1:
        raise TypeError("receipt-backed asset lane candidate must be the exact typed value")
    route = _require_profile_route_bindings_v1(candidate)
    _require_verified_module_binding_v1(candidate)

    result = compose_asset_lane_single_v1(
        candidate.coordinator_context,
        candidate.module_journal,
        candidate.private_port,
        candidate.module_effects,
    )
    if type(result) is not AssetLaneCompositionAcceptedV1:
        raise ValueError(f"asset lane composition rejected: {result.code.value}")
    if result.lane_journal.ordered_module_journal_roots != (
        candidate.verified_module.module_journal_root,
    ):
        raise ValueError("receipt-backed lane ordered module roots mismatch")

    return ReceiptBackedAssetLaneCompositionV1(
        _RECEIPT_BACKED_ASSET_LANE_COMPOSITION_TOKEN,
        _ReceiptBackedAssetLaneCompositionFieldsV1(
            LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY,
            candidate.profile.profile_id,
            route.route_release_id,
            LaneIdV1.ASSET_TRANSFER,
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
    "LaneCompositionAuthorityLevelV1",
    "RECEIPT_BACKED_ASSET_LANE_COMPOSITION_SCHEMA_V1",
    "ReceiptBackedAssetLaneCompositionCandidateV1",
    "ReceiptBackedAssetLaneCompositionV1",
    "compose_receipt_backed_asset_lane_single_v1",
]
