"""Coordinator-release-bound receipt verification for lane composition.

This boundary selects the coordinator image from the active economic profile,
checks the exact structural lane-composition candidate and canonical lane
journal, and delegates cryptographic receipt validation to a verifier port.

The opaque result is only an input to a future route verifier. It does not
authorize a route, epoch, ledger settlement, publication, or production claim.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, Protocol

from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    ReceiptKindV1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .receipt_backed_asset_lane_composition_v1 import (
    ReceiptBackedAssetLaneCompositionV1,
)

VERIFIED_LANE_COMPOSITION_SCHEMA_V1: Final = "zenodex/verified-lane-composition/v1"
_VERIFIED_LANE_COMPOSITION_TOKEN = object()


class LaneCompositionSuccinctReceiptVerifierV1(Protocol):
    """Port implemented by the coordinator-release-selected verifier."""

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


@dataclass(frozen=True, slots=True)
class LaneCompositionReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.receipt_kind, ReceiptKindV1):
            raise TypeError("lane composition receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("lane composition receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class LaneCompositionReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    structural_composition: ReceiptBackedAssetLaneCompositionV1
    lane_journal: LaneCompositionJournalV1
    receipt: LaneCompositionReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.occurrence, EconomicCommandOccurrenceV1, "command occurrence"),
            (
                self.structural_composition,
                ReceiptBackedAssetLaneCompositionV1,
                "structural composition",
            ),
            (self.lane_journal, LaneCompositionJournalV1, "lane journal"),
            (self.receipt, LaneCompositionReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if not isinstance(value, expected_type):
                raise TypeError(f"lane composition {label} must be typed")


@dataclass(frozen=True, slots=True)
class _VerifiedLaneCompositionFieldsV1:
    profile_id: str
    route_release_id: str
    lane_id: LaneIdV1
    coordinator_release_id: str
    command_occurrence_id: str
    writer_epoch: int
    structural_composition_root: str
    lane_journal_root: str
    lane_journal_digest: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1


class VerifiedLaneCompositionV1:
    """Opaque lane-composition proof input produced only by receipt verification."""

    _fields: _VerifiedLaneCompositionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedLaneCompositionFieldsV1,
    ) -> None:
        if token is not _VERIFIED_LANE_COMPOSITION_TOKEN:
            raise TypeError("VerifiedLaneCompositionV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneCompositionV1 is immutable")

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
    def coordinator_release_id(self) -> str:
        return self._fields.coordinator_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def writer_epoch(self) -> int:
        return self._fields.writer_epoch

    @property
    def structural_composition_root(self) -> str:
        return self._fields.structural_composition_root

    @property
    def lane_journal_root(self) -> str:
        return self._fields.lane_journal_root

    @property
    def lane_journal_digest(self) -> str:
        return self._fields.lane_journal_digest

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def receipt_kind(self) -> ReceiptKindV1:
        return self._fields.receipt_kind

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-lane-composition-v1",
            {
                "schema": VERIFIED_LANE_COMPOSITION_SCHEMA_V1,
                "profile_id": self.profile_id,
                "route_release_id": self.route_release_id,
                "lane_id": self.lane_id,
                "coordinator_release_id": self.coordinator_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "writer_epoch": self.writer_epoch,
                "structural_composition_root": self.structural_composition_root,
                "lane_journal_root": self.lane_journal_root,
                "lane_journal_digest": self.lane_journal_digest,
                "expected_image_id": self.expected_image_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
            },
        )


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_exact_lane_composition_binding_v1(
    candidate: LaneCompositionReceiptCandidateV1,
) -> LaneCoordinatorReleaseV1:
    profile = candidate.profile
    occurrence = candidate.occurrence
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("lane composition profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != (LaneIdV1.ASSET_TRANSFER,):
        raise ValueError("lane composition receipt requires the single asset lane route")
    coordinator_release = profile.lane_coordinator_registry.release_for(
        LaneIdV1.ASSET_TRANSFER
    )
    if (
        coordinator_release.status is not ReleaseStatusV1.ACTIVE_NEW
        or not coordinator_release.accepts_new_objects
    ):
        raise ValueError("lane composition selected coordinator release is not ACTIVE_NEW")
    _require_exact_lane_journal_bindings_v1(
        candidate,
        coordinator_release,
        route.route_release_id,
    )
    return coordinator_release


def _require_exact_lane_journal_bindings_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    coordinator_release: LaneCoordinatorReleaseV1,
    route_release_id: str,
) -> None:
    occurrence = candidate.occurrence
    structural = candidate.structural_composition
    lane_journal = candidate.lane_journal

    occurrence_id = occurrence.occurrence_id
    exact_bindings = (
        (occurrence.profile_root, candidate.profile.profile_id, "occurrence profile"),
        (structural.profile_id, candidate.profile.profile_id, "structural profile"),
        (structural.route_release_id, route_release_id, "structural route"),
        (structural.lane_id, LaneIdV1.ASSET_TRANSFER, "structural lane"),
        (
            structural.declared_coordinator_release_id,
            coordinator_release.coordinator_release_id,
            "structural coordinator release",
        ),
        (structural.command_occurrence_id, occurrence_id, "structural occurrence"),
        (lane_journal.chain_id, occurrence.chain_id, "journal chain"),
        (lane_journal.deployment_root, occurrence.deployment_root, "journal deployment"),
        (lane_journal.profile_root, candidate.profile.profile_id, "journal profile"),
        (lane_journal.lane_id, LaneIdV1.ASSET_TRANSFER, "journal lane"),
        (
            lane_journal.coordinator_release_id,
            coordinator_release.coordinator_release_id,
            "journal coordinator release",
        ),
        (lane_journal.command_occurrence_id, occurrence_id, "journal occurrence"),
        (lane_journal.pre_lane_root, structural.pre_lane_root, "journal pre-lane root"),
        (lane_journal.post_lane_root, structural.post_lane_root, "journal post-lane root"),
        (lane_journal.effect_plan_root, structural.effect_plan_root, "journal effect plan"),
        (
            lane_journal.terminal_obligations_root,
            structural.terminal_obligations_root,
            "journal terminal obligations",
        ),
        (lane_journal.journal_root, structural.lane_journal_root, "journal root"),
    )
    for actual, expected, label in exact_bindings:
        if actual != expected:
            raise ValueError(f"lane composition {label} mismatch")
    if lane_journal.writer_epoch != candidate.profile.authority_epoch:
        raise ValueError("lane composition writer epoch mismatch")


def verify_asset_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    receipt_verifier: LaneCompositionSuccinctReceiptVerifierV1,
) -> VerifiedLaneCompositionV1:
    """Verify an asset-lane coordinator receipt under the active profile image."""

    if not isinstance(candidate, LaneCompositionReceiptCandidateV1):
        raise TypeError("lane composition receipt candidate must be typed")
    coordinator_release = _require_exact_lane_composition_binding_v1(candidate)
    if candidate.receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("lane composition verification requires a succinct receipt")
    if not candidate.receipt.receipt_bytes:
        raise ValueError("lane composition receipt bytes must be non-empty bytes")

    lane_journal_bytes = canonical_global_bytes_v1(candidate.lane_journal)
    if len(lane_journal_bytes) > coordinator_release.max_journal_bytes:
        raise ValueError("lane composition canonical journal exceeds its release byte ceiling")
    lane_journal_digest = _sha256_root_v1(lane_journal_bytes)
    receipt_digest = _sha256_root_v1(candidate.receipt.receipt_bytes)
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        expected_image_id=coordinator_release.guest_image_id,
        expected_journal_bytes=lane_journal_bytes,
    )

    return VerifiedLaneCompositionV1(
        _VERIFIED_LANE_COMPOSITION_TOKEN,
        _VerifiedLaneCompositionFieldsV1(
            candidate.profile.profile_id,
            candidate.structural_composition.route_release_id,
            LaneIdV1.ASSET_TRANSFER,
            coordinator_release.coordinator_release_id,
            candidate.occurrence.occurrence_id,
            candidate.profile.authority_epoch,
            candidate.structural_composition.binding_root,
            candidate.lane_journal.journal_root,
            lane_journal_digest,
            coordinator_release.guest_image_id,
            receipt_digest,
            candidate.receipt.receipt_kind,
        ),
    )


__all__ = [
    "LaneCompositionReceiptCandidateV1",
    "LaneCompositionReceiptEnvelopeV1",
    "LaneCompositionSuccinctReceiptVerifierV1",
    "VERIFIED_LANE_COMPOSITION_SCHEMA_V1",
    "VerifiedLaneCompositionV1",
    "verify_asset_lane_composition_receipt_v1",
]
