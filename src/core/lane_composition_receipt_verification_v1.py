"""Prepare coordinator-release-bound receipt requests for lane composition.

The deterministic core selects the coordinator image from the active economic
profile, checks the exact structural lane-composition candidate and canonical
lane journal, and prepares the exact canonical request that one measured
integration port executes. Only :func:`bind_verified_lane_composition_receipt_v1`
can mint the final :class:`VerifiedLaneCompositionV1`, and only from exact
execution evidence over the complete prepared subject.

This module does not select or authenticate a verifier implementation, execute
the guest verifier, compose routes, or publish ledger state. The opaque result
is only an input to a future route verifier. It does not authorize a route,
epoch, ledger settlement, publication, or production claim.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneCompositionJournalV1,
    ReceiptKindV1,
)
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_lane_journal_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    MAX_U64_V1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .receipt_backed_asset_lane_composition_v1 import (
    ReceiptBackedAssetLaneCompositionV1,
)
from .receipt_backed_perps_margin_lane_composition_v1 import (
    ReceiptBackedPerpsMarginLaneCompositionV1,
)

VERIFIED_LANE_COMPOSITION_SCHEMA_V1: Final = "zenodex/verified-lane-composition/v1"
_VERIFIED_LANE_COMPOSITION_TOKEN = object()
_PREPARED_LANE_COMPOSITION_RECEIPT_TOKEN_V1 = object()
_VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1 = object()


@dataclass(frozen=True, slots=True)
class LaneCompositionReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("lane composition receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("lane composition receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class LaneCompositionReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    structural_composition: (
        ReceiptBackedAssetLaneCompositionV1
        | ReceiptBackedPerpsMarginLaneCompositionV1
    )
    lane_journal: LaneCompositionJournalV1
    receipt: LaneCompositionReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1, "economic profile"),
            (self.occurrence, EconomicCommandOccurrenceV1, "command occurrence"),
            (self.lane_journal, LaneCompositionJournalV1, "lane journal"),
            (self.receipt, LaneCompositionReceiptEnvelopeV1, "receipt envelope"),
        )
        for value, expected_type, label in expected_types:
            if type(value) is not expected_type:
                raise TypeError(f"lane composition {label} must be exact typed data")
        if type(self.structural_composition) not in (
            ReceiptBackedAssetLaneCompositionV1,
            ReceiptBackedPerpsMarginLaneCompositionV1,
        ):
            raise TypeError(
                "lane composition structural composition must be exact typed data"
            )


@dataclass(frozen=True, slots=True)
class _StructuralLaneCompositionSnapshotV1:
    profile_id: str
    route_release_id: str
    lane_id: LaneIdV1
    declared_coordinator_release_id: str
    command_occurrence_id: str
    lane_journal_root: str
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    terminal_obligations_root: str
    binding_root: str


@dataclass(frozen=True, slots=True)
class _LaneCompositionReceiptSnapshotV1:
    profile: EconomicProfileSnapshotV1
    occurrence: EconomicCommandOccurrenceV1
    structural_composition: _StructuralLaneCompositionSnapshotV1
    lane_journal: LaneCompositionJournalV1
    receipt: LaneCompositionReceiptEnvelopeV1


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


def _snapshot_structural_composition_v1(
    structural: (
        ReceiptBackedAssetLaneCompositionV1
        | ReceiptBackedPerpsMarginLaneCompositionV1
    ),
) -> _StructuralLaneCompositionSnapshotV1:
    if type(structural) not in (
        ReceiptBackedAssetLaneCompositionV1,
        ReceiptBackedPerpsMarginLaneCompositionV1,
    ):
        raise TypeError("lane composition structural composition must be exact typed data")
    return _StructuralLaneCompositionSnapshotV1(
        profile_id=structural.profile_id,
        route_release_id=structural.route_release_id,
        lane_id=structural.lane_id,
        declared_coordinator_release_id=structural.declared_coordinator_release_id,
        command_occurrence_id=structural.command_occurrence_id,
        lane_journal_root=structural.lane_journal_root,
        pre_lane_root=structural.pre_lane_root,
        post_lane_root=structural.post_lane_root,
        effect_plan_root=structural.effect_plan_root,
        terminal_obligations_root=structural.terminal_obligations_root,
        binding_root=structural.binding_root,
    )


def _snapshot_lane_composition_candidate_v1(
    candidate: LaneCompositionReceiptCandidateV1,
) -> _LaneCompositionReceiptSnapshotV1:
    """Own and revalidate every value read before the prepared subject is fixed."""

    if type(candidate) is not LaneCompositionReceiptCandidateV1:
        raise TypeError("lane composition receipt candidate must be exact typed data")
    candidate.__post_init__()
    return _LaneCompositionReceiptSnapshotV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        structural_composition=_snapshot_structural_composition_v1(
            candidate.structural_composition
        ),
        lane_journal=_snapshot_lane_journal_v1(candidate.lane_journal),
        receipt=LaneCompositionReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _require_exact_lane_composition_binding_v1(
    candidate: _LaneCompositionReceiptSnapshotV1,
    *,
    expected_lane_id: LaneIdV1,
) -> LaneCoordinatorReleaseV1:
    profile = candidate.profile
    occurrence = candidate.occurrence
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("lane composition profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.ordered_lanes != (expected_lane_id,):
        raise ValueError("lane composition receipt requires its declared single-lane route")
    coordinator_release = profile.lane_coordinator_registry.release_for(expected_lane_id)
    if (
        coordinator_release.status is not ReleaseStatusV1.ACTIVE_NEW
        or not coordinator_release.accepts_new_objects
    ):
        raise ValueError("lane composition selected coordinator release is not ACTIVE_NEW")
    _require_exact_lane_journal_bindings_v1(
        candidate,
        coordinator_release,
        route.route_release_id,
        expected_lane_id,
    )
    return coordinator_release


def _require_exact_lane_journal_bindings_v1(
    candidate: _LaneCompositionReceiptSnapshotV1,
    coordinator_release: LaneCoordinatorReleaseV1,
    route_release_id: str,
    expected_lane_id: LaneIdV1,
) -> None:
    occurrence = candidate.occurrence
    structural = candidate.structural_composition
    lane_journal = candidate.lane_journal

    occurrence_id = occurrence.occurrence_id
    exact_bindings = (
        (occurrence.profile_root, candidate.profile.profile_id, "occurrence profile"),
        (structural.profile_id, candidate.profile.profile_id, "structural profile"),
        (structural.route_release_id, route_release_id, "structural route"),
        (structural.lane_id, expected_lane_id, "structural lane"),
        (
            structural.declared_coordinator_release_id,
            coordinator_release.coordinator_release_id,
            "structural coordinator release",
        ),
        (structural.command_occurrence_id, occurrence_id, "structural occurrence"),
        (lane_journal.chain_id, occurrence.chain_id, "journal chain"),
        (lane_journal.deployment_root, occurrence.deployment_root, "journal deployment"),
        (lane_journal.profile_root, candidate.profile.profile_id, "journal profile"),
        (lane_journal.lane_id, expected_lane_id, "journal lane"),
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


@dataclass(frozen=True, slots=True)
class _PreparedLaneCompositionReceiptFieldsV1:
    """The complete prepared subject: exact final witness fields plus request bytes.

    The port-facing coordinates are the witness fields themselves, so no
    duplicated request coordinate can disagree with the minted witness.
    """

    composition_fields: _VerifiedLaneCompositionFieldsV1
    receipt_bytes: bytes
    expected_journal_bytes: bytes


# Old entry-point domains, each fixed by an actual upstream validator on the path the
# entry point already walked (hash provenance establishes nothing; hash_global_v1 and
# sha256 outputs are canonical 32-byte values that may be zero):
# - profile_id: EconomicProfileSnapshotV1.__post_init__ "economic profile id" (nonzero)
#   on the owned profile snapshot.
# - route_release_id: exact binding to route.route_release_id, which
#   RouteReleaseV1.__post_init__ "route release id" requires nonzero.
# - coordinator_release_id: LaneCoordinatorReleaseV1.__post_init__
#   "lane coordinator release id" (nonzero).
# - command_occurrence_id: exact binding to lane_journal.command_occurrence_id, which
#   LaneCompositionJournalV1.validate "lane composition command_occurrence_id" requires
#   nonzero (its allow_zero set is pre_lane_root, post_lane_root, terminal_obligations_root).
# - expected_image_id: LaneCoordinatorReleaseV1.__post_init__
#   "lane coordinator guest_image_id" (nonzero).
_PREPARED_LANE_COMPOSITION_NONZERO_ROOT_FIELDS_V1: Final = (
    "profile_id",
    "route_release_id",
    "coordinator_release_id",
    "command_occurrence_id",
    "expected_image_id",
)
# No pre-existing admission check constrains these four, so the prepared guard permits
# zero exactly as the old entry point did: structural_composition_root (the structural
# binding_root hash), lane_journal_root (LaneCompositionJournalV1.journal_root, bound only
# by equality to the unvalidated structural field), lane_journal_digest and
# receipt_digest. Later consumers keep their own unchanged nonzero rules.
_PREPARED_LANE_COMPOSITION_ZERO_PERMITTED_ROOT_FIELDS_V1: Final = (
    "structural_composition_root",
    "lane_journal_root",
    "lane_journal_digest",
    "receipt_digest",
)


def _copy_verified_lane_composition_fields_v1(
    fields: _VerifiedLaneCompositionFieldsV1,
) -> _VerifiedLaneCompositionFieldsV1:
    return _VerifiedLaneCompositionFieldsV1(
        fields.profile_id,
        fields.route_release_id,
        fields.lane_id,
        fields.coordinator_release_id,
        fields.command_occurrence_id,
        fields.writer_epoch,
        fields.structural_composition_root,
        fields.lane_journal_root,
        fields.lane_journal_digest,
        fields.expected_image_id,
        fields.receipt_digest,
        fields.receipt_kind,
    )


def _require_prepared_lane_composition_fields_v1(
    fields: object,
) -> _VerifiedLaneCompositionFieldsV1:
    if type(fields) is not _VerifiedLaneCompositionFieldsV1:
        raise TypeError("prepared lane composition fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name="prepared lane composition")
    for name in _PREPARED_LANE_COMPOSITION_NONZERO_ROOT_FIELDS_V1:
        _require_root(getattr(fields, name), name=f"prepared lane composition {name}")
    for name in _PREPARED_LANE_COMPOSITION_ZERO_PERMITTED_ROOT_FIELDS_V1:
        _require_root(
            getattr(fields, name),
            name=f"prepared lane composition {name}",
            allow_zero=True,
        )
    if type(fields.lane_id) is not LaneIdV1:
        raise TypeError("prepared lane composition lane id is not closed")
    if type(fields.writer_epoch) is not int or not 0 <= fields.writer_epoch <= MAX_U64_V1:
        raise ValueError("prepared lane composition writer epoch must fit unsigned 64-bit")
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError("prepared lane composition receipt kind is not closed")
    if fields.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("prepared lane composition receipt kind must be succinct")
    return fields


def _require_prepared_lane_composition_receipt_fields_v1(
    fields: object,
) -> _PreparedLaneCompositionReceiptFieldsV1:
    if type(fields) is not _PreparedLaneCompositionReceiptFieldsV1:
        raise TypeError("prepared lane composition receipt fields must be exact typed data")
    _require_prepared_lane_composition_fields_v1(fields.composition_fields)
    if type(fields.receipt_bytes) is not bytes or not fields.receipt_bytes:
        raise TypeError("prepared lane composition receipt bytes must be non-empty exact bytes")
    if type(fields.expected_journal_bytes) is not bytes or not fields.expected_journal_bytes:
        raise TypeError("prepared lane composition journal bytes must be non-empty exact bytes")
    return fields


def _validate_prepared_lane_composition_receipt_content_digests_v1(
    fields: _PreparedLaneCompositionReceiptFieldsV1,
) -> None:
    composition_fields = fields.composition_fields
    if composition_fields.receipt_digest != _sha256_root_v1(fields.receipt_bytes):
        raise ValueError("prepared lane composition receipt digest mismatch")
    if composition_fields.lane_journal_digest != _sha256_root_v1(fields.expected_journal_bytes):
        raise ValueError("prepared lane composition journal digest mismatch")


def _snapshot_prepared_lane_composition_receipt_fields_v1(
    fields: object,
) -> _PreparedLaneCompositionReceiptFieldsV1:
    prepared = _require_prepared_lane_composition_receipt_fields_v1(fields)
    return _PreparedLaneCompositionReceiptFieldsV1(
        _copy_verified_lane_composition_fields_v1(prepared.composition_fields),
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    )


class PreparedLaneCompositionReceiptV1:
    """Opaque, immutable exact request for a measured coordinator verifier port."""

    _fields: _PreparedLaneCompositionReceiptFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _PreparedLaneCompositionReceiptFieldsV1,
    ) -> None:
        if token is not _PREPARED_LANE_COMPOSITION_RECEIPT_TOKEN_V1:
            raise TypeError("PreparedLaneCompositionReceiptV1 is core-constructed")
        object.__setattr__(
            self,
            "_fields",
            _snapshot_prepared_lane_composition_receipt_fields_v1(fields),
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("PreparedLaneCompositionReceiptV1 is immutable")

    @property
    def profile_root(self) -> str:
        return self._fields.composition_fields.profile_id

    @property
    def lane_id(self) -> LaneIdV1:
        return self._fields.composition_fields.lane_id

    @property
    def coordinator_release_id(self) -> str:
        return self._fields.composition_fields.coordinator_release_id

    @property
    def expected_image_id(self) -> str:
        return self._fields.composition_fields.expected_image_id

    @property
    def receipt_bytes(self) -> bytes:
        return self._fields.receipt_bytes

    @property
    def expected_journal_bytes(self) -> bytes:
        return self._fields.expected_journal_bytes


def _prepared_lane_composition_receipt_fields_v1(
    prepared: object,
) -> _PreparedLaneCompositionReceiptFieldsV1:
    if type(prepared) is not PreparedLaneCompositionReceiptV1:
        raise TypeError("prepared lane composition receipt must be the exact typed value")
    fields = object.__getattribute__(prepared, "_fields")
    return _require_prepared_lane_composition_receipt_fields_v1(fields)


def snapshot_prepared_lane_composition_receipt_v1(
    prepared: PreparedLaneCompositionReceiptV1,
) -> PreparedLaneCompositionReceiptV1:
    """Return a validated detached request snapshot for measured verifier I/O."""

    fields = _prepared_lane_composition_receipt_fields_v1(prepared)
    return PreparedLaneCompositionReceiptV1(
        _PREPARED_LANE_COMPOSITION_RECEIPT_TOKEN_V1,
        fields,
    )


@dataclass(frozen=True, slots=True)
class _VerifiedLaneCompositionReceiptExecutionFieldsV1:
    prepared_fields: _PreparedLaneCompositionReceiptFieldsV1
    verifier_binding_root: str


class VerifiedLaneCompositionReceiptExecutionV1:
    """Opaque evidence that a measured coordinator port executed one exact request.

    The private token disciplines ordinary Python construction. It does not
    establish protection against a compromised interpreter or process.
    """

    _fields: _VerifiedLaneCompositionReceiptExecutionFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        prepared: PreparedLaneCompositionReceiptV1,
        verifier_binding_root: str,
    ) -> None:
        if token is not _VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1:
            raise TypeError("VerifiedLaneCompositionReceiptExecutionV1 is port-constructed")
        prepared_fields = _prepared_lane_composition_receipt_fields_v1(prepared)
        # New phase input with no old entry-point domain: the measured port's
        # BoundEconomicReceiptVerifierV1.binding_root. No upstream validator constrains
        # it; nonzero here is the same rule the module port evidence in
        # isolated_profile_receipt_ports_v1 applies to this exact value.
        _require_root(
            verifier_binding_root,
            name="lane composition receipt verifier binding root",
        )
        object.__setattr__(
            self,
            "_fields",
            _VerifiedLaneCompositionReceiptExecutionFieldsV1(
                _snapshot_prepared_lane_composition_receipt_fields_v1(prepared_fields),
                verifier_binding_root,
            ),
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedLaneCompositionReceiptExecutionV1 is immutable")

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root


def _verified_lane_composition_receipt_execution_fields_v1(
    execution: object,
) -> _VerifiedLaneCompositionReceiptExecutionFieldsV1:
    if type(execution) is not VerifiedLaneCompositionReceiptExecutionV1:
        raise TypeError("lane composition receipt execution must be the exact typed value")
    fields = object.__getattribute__(execution, "_fields")
    if type(fields) is not _VerifiedLaneCompositionReceiptExecutionFieldsV1:
        raise TypeError("lane composition receipt execution fields must be exact typed data")
    _require_prepared_lane_composition_receipt_fields_v1(fields.prepared_fields)
    _require_root(
        fields.verifier_binding_root,
        name="lane composition receipt execution verifier binding root",
    )
    return fields


def bind_verified_lane_composition_receipt_v1(
    prepared: PreparedLaneCompositionReceiptV1,
    execution: VerifiedLaneCompositionReceiptExecutionV1,
    *,
    expected_verifier_binding_root: str,
) -> VerifiedLaneCompositionV1:
    """Mint the existing lane witness from exact measured execution evidence."""

    prepared_fields = _prepared_lane_composition_receipt_fields_v1(prepared)
    execution_fields = _verified_lane_composition_receipt_execution_fields_v1(execution)
    _require_root(
        expected_verifier_binding_root,
        name="expected lane composition receipt verifier binding root",
    )
    if execution_fields.prepared_fields != prepared_fields:
        raise ValueError("lane composition receipt execution subject mismatch")
    if execution_fields.verifier_binding_root != expected_verifier_binding_root:
        raise ValueError("lane composition receipt verifier binding mismatch")
    _validate_prepared_lane_composition_receipt_content_digests_v1(prepared_fields)
    return VerifiedLaneCompositionV1(
        _VERIFIED_LANE_COMPOSITION_TOKEN,
        _copy_verified_lane_composition_fields_v1(prepared_fields.composition_fields),
    )


def _prepare_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    *,
    expected_lane_id: LaneIdV1,
) -> PreparedLaneCompositionReceiptV1:
    owned = _snapshot_lane_composition_candidate_v1(candidate)
    coordinator_release = _require_exact_lane_composition_binding_v1(
        owned,
        expected_lane_id=expected_lane_id,
    )
    if owned.receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("lane composition verification requires a succinct receipt")
    if not owned.receipt.receipt_bytes:
        raise ValueError("lane composition receipt bytes must be non-empty bytes")

    lane_journal_bytes = canonical_global_bytes_v1(owned.lane_journal)
    if len(lane_journal_bytes) > coordinator_release.max_journal_bytes:
        raise ValueError("lane composition canonical journal exceeds its release byte ceiling")
    lane_journal_digest = _sha256_root_v1(lane_journal_bytes)
    receipt_digest = _sha256_root_v1(owned.receipt.receipt_bytes)
    return PreparedLaneCompositionReceiptV1(
        _PREPARED_LANE_COMPOSITION_RECEIPT_TOKEN_V1,
        _PreparedLaneCompositionReceiptFieldsV1(
            _VerifiedLaneCompositionFieldsV1(
                owned.profile.profile_id,
                owned.structural_composition.route_release_id,
                expected_lane_id,
                coordinator_release.coordinator_release_id,
                owned.occurrence.occurrence_id,
                owned.profile.authority_epoch,
                owned.structural_composition.binding_root,
                owned.lane_journal.journal_root,
                lane_journal_digest,
                coordinator_release.guest_image_id,
                receipt_digest,
                owned.receipt.receipt_kind,
            ),
            owned.receipt.receipt_bytes,
            lane_journal_bytes,
        ),
    )


def prepare_asset_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
) -> PreparedLaneCompositionReceiptV1:
    """Prepare an asset-lane coordinator receipt request under the active profile image.

    The owned snapshot, exact binding checks, receipt shape, canonical journal
    ceiling and digests are fixed here, before any verifier I/O.
    """

    return _prepare_lane_composition_receipt_v1(
        candidate,
        expected_lane_id=LaneIdV1.ASSET_TRANSFER,
    )


def prepare_perps_margin_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
) -> PreparedLaneCompositionReceiptV1:
    """Prepare a perps-margin coordinator receipt request under its governed image."""

    return _prepare_lane_composition_receipt_v1(
        candidate,
        expected_lane_id=LaneIdV1.PERPS_MARKET,
    )


__all__ = [
    "LaneCompositionReceiptCandidateV1",
    "LaneCompositionReceiptEnvelopeV1",
    "PreparedLaneCompositionReceiptV1",
    "VERIFIED_LANE_COMPOSITION_SCHEMA_V1",
    "VerifiedLaneCompositionReceiptExecutionV1",
    "VerifiedLaneCompositionV1",
    "bind_verified_lane_composition_receipt_v1",
    "prepare_asset_lane_composition_receipt_v1",
    "prepare_perps_margin_lane_composition_receipt_v1",
    "snapshot_prepared_lane_composition_receipt_v1",
]
