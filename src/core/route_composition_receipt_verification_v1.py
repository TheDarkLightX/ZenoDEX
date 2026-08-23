"""Release-selected receipt admission for one governed command route.

The pure boundary consumes the exact ordered lane journals and opaque
coordinator-verified lane witnesses selected by the active route. It delegates
cryptographic verification of the canonical route journal to a verifier port.

The resulting witness is only an input to epoch recursion. It grants no epoch,
commit, settlement, migration, publication, or production authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, Protocol

from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    ReceiptKindV1,
    RouteCompositionJournalV1,
)
from .global_economic_refinement_snapshot_v1 import (
    _snapshot_lane_journal_v1,
    _snapshot_occurrence_v1,
    _snapshot_route_journal_v1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .lane_composition_receipt_verification_v1 import (
    VERIFIED_LANE_COMPOSITION_SCHEMA_V1,
    VerifiedLaneCompositionV1,
)

VERIFIED_ROUTE_COMPOSITION_SCHEMA_V1: Final = "zenodex/verified-route-composition/v1"
ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1: Final = "zenodex/route-composition-assumption/v1"
_VERIFIED_ROUTE_COMPOSITION_TOKEN = object()


class RouteCompositionSuccinctReceiptVerifierV1(Protocol):
    """Port implemented by the route-release-selected verifier."""

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


@dataclass(frozen=True, slots=True)
class RouteCompositionReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("route composition receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("route composition receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class RouteCompositionReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    lane_journals: tuple[LaneCompositionJournalV1, ...]
    verified_lanes: tuple[VerifiedLaneCompositionV1, ...]
    route_journal: RouteCompositionJournalV1
    receipt: RouteCompositionReceiptEnvelopeV1

    def __post_init__(self) -> None:
        if type(self.profile) is not EconomicProfileSnapshotV1:
            raise TypeError("route composition economic profile must be exact typed data")
        if type(self.occurrence) is not EconomicCommandOccurrenceV1:
            raise TypeError("route composition command occurrence must be exact typed data")
        if type(self.lane_journals) is not tuple:
            raise TypeError("route composition lane journals must be an exact tuple")
        if any(type(item) is not LaneCompositionJournalV1 for item in self.lane_journals):
            raise TypeError("route composition lane journals must be exact typed data")
        if type(self.verified_lanes) is not tuple:
            raise TypeError("route composition verified lane witnesses must be an exact tuple")
        if any(type(item) is not VerifiedLaneCompositionV1 for item in self.verified_lanes):
            raise TypeError("route composition verified lane witnesses must be exact typed data")
        if type(self.route_journal) is not RouteCompositionJournalV1:
            raise TypeError("route composition route journal must be exact typed data")
        if type(self.receipt) is not RouteCompositionReceiptEnvelopeV1:
            raise TypeError("route composition receipt envelope must be exact typed data")


@dataclass(frozen=True, slots=True)
class _VerifiedLaneCompositionSnapshotV1:
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

    def __post_init__(self) -> None:
        for field_name in (
            "profile_id",
            "route_release_id",
            "coordinator_release_id",
            "command_occurrence_id",
            "structural_composition_root",
            "lane_journal_root",
            "lane_journal_digest",
            "expected_image_id",
            "receipt_digest",
        ):
            _require_nonzero_root_v1(
                getattr(self, field_name),
                name=f"route lane witness {field_name}",
            )
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("route lane witness lane id is not closed")
        if type(self.writer_epoch) is not int or not 0 <= self.writer_epoch <= (1 << 64) - 1:
            raise ValueError("route lane witness writer epoch must fit unsigned 64-bit")
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("route lane witness receipt kind is not closed")

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


@dataclass(frozen=True, slots=True)
class _RouteCompositionReceiptSnapshotV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    lane_journals: tuple[LaneCompositionJournalV1, ...]
    verified_lanes: tuple[_VerifiedLaneCompositionSnapshotV1, ...]
    route_journal: RouteCompositionJournalV1
    receipt: RouteCompositionReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class _VerifiedRouteCompositionFieldsV1:
    profile_id: str
    route_release_id: str
    command_occurrence_id: str
    writer_epoch: int
    ordered_lane_ids: tuple[LaneIdV1, ...]
    ordered_lane_binding_roots: tuple[str, ...]
    ordered_lane_journal_roots: tuple[str, ...]
    route_journal_root: str
    route_journal_digest: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1


class VerifiedRouteCompositionV1:
    """Opaque route-composition proof input produced only by receipt verification."""

    _fields: _VerifiedRouteCompositionFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _VerifiedRouteCompositionFieldsV1) -> None:
        if token is not _VERIFIED_ROUTE_COMPOSITION_TOKEN:
            raise TypeError("VerifiedRouteCompositionV1 is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedRouteCompositionV1 is immutable")

    @property
    def profile_id(self) -> str:
        return self._fields.profile_id

    @property
    def route_release_id(self) -> str:
        return self._fields.route_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def writer_epoch(self) -> int:
        return self._fields.writer_epoch

    @property
    def ordered_lane_ids(self) -> tuple[LaneIdV1, ...]:
        return self._fields.ordered_lane_ids

    @property
    def ordered_lane_binding_roots(self) -> tuple[str, ...]:
        return self._fields.ordered_lane_binding_roots

    @property
    def ordered_lane_journal_roots(self) -> tuple[str, ...]:
        return self._fields.ordered_lane_journal_roots

    @property
    def route_journal_root(self) -> str:
        return self._fields.route_journal_root

    @property
    def route_journal_digest(self) -> str:
        return self._fields.route_journal_digest

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
    def assumption_root(self) -> str:
        """Bind the exact guest-visible child claim without receipt-private bytes."""

        return derive_route_composition_assumption_root_v1(
            profile_id=self.profile_id,
            route_release_id=self.route_release_id,
            command_occurrence_id=self.command_occurrence_id,
            writer_epoch=self.writer_epoch,
            route_journal_root=self.route_journal_root,
            route_journal_digest=self.route_journal_digest,
            expected_image_id=self.expected_image_id,
        )

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-route-composition-v1",
            {
                "schema": VERIFIED_ROUTE_COMPOSITION_SCHEMA_V1,
                "profile_id": self.profile_id,
                "route_release_id": self.route_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "writer_epoch": self.writer_epoch,
                "ordered_lane_ids": self.ordered_lane_ids,
                "ordered_lane_binding_roots": self.ordered_lane_binding_roots,
                "ordered_lane_journal_roots": self.ordered_lane_journal_roots,
                "route_journal_root": self.route_journal_root,
                "route_journal_digest": self.route_journal_digest,
                "expected_image_id": self.expected_image_id,
                "receipt_digest": self.receipt_digest,
                "receipt_kind": self.receipt_kind,
            },
        )


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_nonzero_root_v1(value: object, *, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value == "0x" + "00" * 32
        or value != value.lower()
    ):
        raise ValueError(f"{name} must be a nonzero canonical root")
    try:
        decoded = bytes.fromhex(value[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be a nonzero canonical root") from exc
    if len(decoded) != 32:
        raise ValueError(f"{name} must be a nonzero canonical root")
    return value


def _snapshot_verified_lane_v1(
    verified_lane: VerifiedLaneCompositionV1,
) -> _VerifiedLaneCompositionSnapshotV1:
    if type(verified_lane) is not VerifiedLaneCompositionV1:
        raise TypeError("route composition lane witness must be exact typed data")
    return _VerifiedLaneCompositionSnapshotV1(
        profile_id=verified_lane.profile_id,
        route_release_id=verified_lane.route_release_id,
        lane_id=verified_lane.lane_id,
        coordinator_release_id=verified_lane.coordinator_release_id,
        command_occurrence_id=verified_lane.command_occurrence_id,
        writer_epoch=verified_lane.writer_epoch,
        structural_composition_root=verified_lane.structural_composition_root,
        lane_journal_root=verified_lane.lane_journal_root,
        lane_journal_digest=verified_lane.lane_journal_digest,
        expected_image_id=verified_lane.expected_image_id,
        receipt_digest=verified_lane.receipt_digest,
        receipt_kind=verified_lane.receipt_kind,
    )


def _snapshot_route_composition_candidate_v1(
    candidate: RouteCompositionReceiptCandidateV1,
) -> _RouteCompositionReceiptSnapshotV1:
    """Own and revalidate every value read across the verifier callback."""

    if type(candidate) is not RouteCompositionReceiptCandidateV1:
        raise TypeError("route composition receipt candidate must be exact typed data")
    candidate.__post_init__()
    return _RouteCompositionReceiptSnapshotV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        lane_journals=tuple(
            _snapshot_lane_journal_v1(journal) for journal in candidate.lane_journals
        ),
        verified_lanes=tuple(
            _snapshot_verified_lane_v1(verified_lane) for verified_lane in candidate.verified_lanes
        ),
        route_journal=_snapshot_route_journal_v1(candidate.route_journal),
        receipt=RouteCompositionReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def derive_route_composition_assumption_root_v1(
    *,
    profile_id: str,
    route_release_id: str,
    command_occurrence_id: str,
    writer_epoch: int,
    route_journal_root: str,
    route_journal_digest: str,
    expected_image_id: str,
) -> str:
    """Derive the public claim a recursive guest must resolve exactly."""

    roots = {
        "profile_id": profile_id,
        "route_release_id": route_release_id,
        "command_occurrence_id": command_occurrence_id,
        "route_journal_root": route_journal_root,
        "route_journal_digest": route_journal_digest,
        "expected_image_id": expected_image_id,
    }
    for name, root in roots.items():
        _require_nonzero_root_v1(root, name=f"route assumption {name}")
    if type(writer_epoch) is not int or not 0 <= writer_epoch <= (1 << 64) - 1:
        raise ValueError("route assumption writer epoch must fit an unsigned 64-bit integer")
    return hash_global_v1(
        "route-composition-assumption-v1",
        {
            "schema": ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
            "profile_id": profile_id,
            "route_release_id": route_release_id,
            "command_occurrence_id": command_occurrence_id,
            "writer_epoch": writer_epoch,
            "route_journal_root": route_journal_root,
            "route_journal_digest": route_journal_digest,
            "expected_image_id": expected_image_id,
        },
    )


def _require_route_shape_v1(
    candidate: _RouteCompositionReceiptSnapshotV1,
    route: RouteReleaseV1,
) -> None:
    if len(candidate.lane_journals) != len(route.ordered_lanes):
        raise ValueError("route composition lane journal count mismatch")
    if len(candidate.verified_lanes) != len(route.ordered_lanes):
        raise ValueError("route composition lane witness count mismatch")
    lane_ids = tuple(item.lane_id for item in candidate.lane_journals)
    if lane_ids != route.ordered_lanes:
        raise ValueError("route composition lane journal order mismatch")
    witness_lane_ids = tuple(item.lane_id for item in candidate.verified_lanes)
    if witness_lane_ids != route.ordered_lanes:
        raise ValueError("route composition lane witness order mismatch")


def _require_route_journal_binding_v1(
    candidate: _RouteCompositionReceiptSnapshotV1,
    route: RouteReleaseV1,
) -> None:
    occurrence = candidate.occurrence
    journal = candidate.route_journal
    occurrence_id = occurrence.occurrence_id
    expected_lane_roots = tuple(item.journal_root for item in candidate.lane_journals)
    bindings = (
        (occurrence.profile_root, candidate.profile.profile_id, "occurrence profile"),
        (journal.chain_id, occurrence.chain_id, "journal chain"),
        (journal.deployment_root, occurrence.deployment_root, "journal deployment"),
        (journal.profile_root, candidate.profile.profile_id, "journal profile"),
        (journal.route_release_id, route.route_release_id, "journal route release"),
        (journal.command_occurrence_id, occurrence_id, "journal occurrence"),
        (journal.ordered_lane_journal_roots, expected_lane_roots, "journal lane roots"),
        (journal.pre_state_root, occurrence.pre_state_root, "journal pre-state root"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"route composition {label} mismatch")
    if journal.writer_epoch != candidate.profile.authority_epoch:
        raise ValueError("route composition writer epoch mismatch")
    if len(candidate.lane_journals) == 1:
        lane_journal = candidate.lane_journals[0]
        if journal.effect_plan_root != lane_journal.effect_plan_root:
            raise ValueError("route composition single-lane effect plan mismatch")
        if journal.terminal_obligations_root != lane_journal.terminal_obligations_root:
            raise ValueError("route composition single-lane terminal obligations mismatch")


def _require_verified_lane_bindings_v1(
    candidate: _RouteCompositionReceiptSnapshotV1,
    route: RouteReleaseV1,
) -> None:
    occurrence_id = candidate.occurrence.occurrence_id
    for lane_id, lane_journal, verified_lane in zip(
        route.ordered_lanes,
        candidate.lane_journals,
        candidate.verified_lanes,
        strict=True,
    ):
        coordinator = candidate.profile.lane_coordinator_registry.release_for(lane_id)
        lane_journal_bytes = canonical_global_bytes_v1(lane_journal)
        bindings = (
            (verified_lane.profile_id, candidate.profile.profile_id, "lane witness profile"),
            (verified_lane.route_release_id, route.route_release_id, "lane witness route"),
            (verified_lane.lane_id, lane_id, "lane witness lane"),
            (
                verified_lane.coordinator_release_id,
                coordinator.coordinator_release_id,
                "lane witness coordinator release",
            ),
            (verified_lane.command_occurrence_id, occurrence_id, "lane witness occurrence"),
            (verified_lane.lane_journal_root, lane_journal.journal_root, "lane witness journal"),
            (
                verified_lane.lane_journal_digest,
                _sha256_root_v1(lane_journal_bytes),
                "lane witness journal digest",
            ),
            (
                verified_lane.expected_image_id,
                coordinator.guest_image_id,
                "lane witness image",
            ),
        )
        for actual, expected, label in bindings:
            if actual != expected:
                raise ValueError(f"route composition {label} mismatch")
        if verified_lane.writer_epoch != candidate.profile.authority_epoch:
            raise ValueError("route composition lane witness writer epoch mismatch")
        if verified_lane.receipt_kind is not ReceiptKindV1.SUCCINCT:
            raise ValueError("route composition lane witness is not succinct")


def _require_exact_route_composition_binding_v1(
    candidate: _RouteCompositionReceiptSnapshotV1,
) -> RouteReleaseV1:
    if candidate.profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("route composition profile is not ACTIVE")
    route = candidate.profile.route_registry.route_for_command(
        candidate.occurrence.command_kind,
        claimed_route_release_id=candidate.occurrence.route_release_id,
    )
    _require_route_shape_v1(candidate, route)
    _require_route_journal_binding_v1(candidate, route)
    _require_verified_lane_bindings_v1(candidate, route)
    return route


def verify_route_composition_receipt_v1(
    candidate: RouteCompositionReceiptCandidateV1,
    receipt_verifier: RouteCompositionSuccinctReceiptVerifierV1,
) -> VerifiedRouteCompositionV1:
    """Verify one route receipt against its profile-selected composer image."""

    owned = _snapshot_route_composition_candidate_v1(candidate)
    route = _require_exact_route_composition_binding_v1(owned)
    if owned.receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("route composition verification requires a succinct receipt")
    if not owned.receipt.receipt_bytes:
        raise ValueError("route composition receipt bytes must be non-empty bytes")

    route_journal_bytes = canonical_global_bytes_v1(owned.route_journal)
    if len(route_journal_bytes) > route.max_journal_bytes:
        raise ValueError("route composition canonical journal exceeds its release byte ceiling")
    route_journal_digest = _sha256_root_v1(route_journal_bytes)
    receipt_digest = _sha256_root_v1(owned.receipt.receipt_bytes)
    receipt_verifier.verify_succinct_receipt(
        owned.receipt.receipt_bytes,
        expected_image_id=route.guest_image_id,
        expected_journal_bytes=route_journal_bytes,
    )

    return VerifiedRouteCompositionV1(
        _VERIFIED_ROUTE_COMPOSITION_TOKEN,
        _VerifiedRouteCompositionFieldsV1(
            owned.profile.profile_id,
            route.route_release_id,
            owned.occurrence.occurrence_id,
            owned.profile.authority_epoch,
            route.ordered_lanes,
            tuple(item.binding_root for item in owned.verified_lanes),
            tuple(item.journal_root for item in owned.lane_journals),
            owned.route_journal.journal_root,
            route_journal_digest,
            route.guest_image_id,
            receipt_digest,
            owned.receipt.receipt_kind,
        ),
    )


__all__ = [
    "ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1",
    "RouteCompositionReceiptCandidateV1",
    "RouteCompositionReceiptEnvelopeV1",
    "RouteCompositionSuccinctReceiptVerifierV1",
    "VERIFIED_ROUTE_COMPOSITION_SCHEMA_V1",
    "VerifiedRouteCompositionV1",
    "derive_route_composition_assumption_root_v1",
    "verify_route_composition_receipt_v1",
]
