"""Exact immutable values for unmounted M5-P4B0 refinement evidence.

These records contain only exact scalars, bytes, tuples, enums, and other
final frozen records.  They carry evidence, never mounted commit authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from .fcis_step_evaluation_values import FCISFeeAllocationV1

PathPartV1: TypeAlias = str | int
FieldPathV1: TypeAlias = tuple[PathPartV1, ...]


class CanonicalParseCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    EMPTY_INPUT = "empty_input"
    BYTE_LIMIT = "byte_limit"
    DEPTH_LIMIT = "depth_limit"
    BOM = "bom"
    INVALID_UTF8 = "invalid_utf8"
    DUPLICATE_KEY = "duplicate_key"
    FLOAT_FORBIDDEN = "float_forbidden"
    NONFINITE_FORBIDDEN = "nonfinite_forbidden"
    INVALID_JSON = "invalid_json"
    NONCANONICAL_JSON = "noncanonical_json"


@final
@dataclass(frozen=True, slots=True)
class CanonicalParseRejectV1:
    code: CanonicalParseCodeV1
    path: FieldPathV1 = ()

    def __post_init__(self) -> None:
        if type(self.code) is not CanonicalParseCodeV1 or type(self.path) is not tuple:
            raise TypeError("canonical parse rejection must be exact")


class ObservationResultKindV1(Enum):
    ACCEPT = "accept"
    REJECT = "reject"


class EvidenceFieldStatusV1(Enum):
    ABSENT = "absent"
    UNAVAILABLE = "unavailable_in_legacy_v1"
    PRESENT = "present"


def _require_status_value(
    status: EvidenceFieldStatusV1,
    value_is_present: bool,
) -> None:
    if type(status) is not EvidenceFieldStatusV1:
        raise TypeError("evidence field status must be exact")
    if (status is EvidenceFieldStatusV1.PRESENT) != value_is_present:
        raise TypeError("evidence field status/value mismatch")


@final
@dataclass(frozen=True, slots=True)
class CanonicalBytesFieldV1:
    status: EvidenceFieldStatusV1
    value: bytes | None

    def __post_init__(self) -> None:
        _require_status_value(self.status, self.value is not None)
        if self.value is not None and (type(self.value) is not bytes or not self.value):
            raise TypeError("present canonical bytes must be exact nonempty bytes")


def _is_digest_v1(value: str) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and all(character in "0123456789abcdef" for character in value[2:])
    )


@final
@dataclass(frozen=True, slots=True)
class CanonicalDigestFieldV1:
    status: EvidenceFieldStatusV1
    value: str | None

    def __post_init__(self) -> None:
        _require_status_value(self.status, self.value is not None)
        if self.value is not None and not _is_digest_v1(self.value):
            raise TypeError("present digest must be lowercase 0x-prefixed SHA-256")


@final
@dataclass(frozen=True, slots=True)
class OutboxIdentityValueV1:
    effect_identity: str
    effect_index: int
    idempotency_key: str

    def __post_init__(self) -> None:
        if not _is_digest_v1(self.effect_identity):
            raise TypeError("effect identity must be a canonical digest")
        if type(self.effect_index) is not int or self.effect_index < 0:
            raise TypeError("effect index must be an exact nonnegative int")
        if not _is_digest_v1(self.idempotency_key):
            raise TypeError("idempotency key must be a canonical digest")


@final
@dataclass(frozen=True, slots=True)
class CanonicalIdentitiesFieldV1:
    status: EvidenceFieldStatusV1
    value: tuple[OutboxIdentityValueV1, ...] | None

    def __post_init__(self) -> None:
        _require_status_value(self.status, self.value is not None)
        if self.value is not None and (
            type(self.value) is not tuple
            or any(type(identity) is not OutboxIdentityValueV1 for identity in self.value)
        ):
            raise TypeError("present identities must be exact owned values")


@final
@dataclass(frozen=True, slots=True)
class RejectionValueV1:
    code: str
    path: tuple[str, ...]
    precedence: str
    public_reason: str
    unavailable_fields: tuple[str, ...]

    def __post_init__(self) -> None:
        strings = (self.code, self.precedence, self.public_reason)
        if any(type(value) is not str or not value for value in strings):
            raise TypeError("rejection fields must be exact nonempty strings")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("rejection path must be an exact string tuple")
        if type(self.unavailable_fields) is not tuple or any(
            type(field) is not str or not field for field in self.unavailable_fields
        ):
            raise TypeError("unavailable fields must be an exact string tuple")


@final
@dataclass(frozen=True, slots=True)
class InputBindingV1:
    baseline_artifact_hash: str
    differential_artifact_hash: str
    reviewed_start_sha: str
    packet_commit: str
    packet_tree_hash: str
    fixture_id: str
    command_kind: str
    command_bytes: tuple[bytes, ...]
    command_hash: str
    pre_state_bytes: bytes
    pre_state_root: str
    context_bytes: bytes
    context_hash: str

    def __post_init__(self) -> None:
        digests = (
            self.baseline_artifact_hash,
            self.differential_artifact_hash,
            self.command_hash,
            self.pre_state_root,
            self.context_hash,
        )
        if any(not _is_digest_v1(value) for value in digests):
            raise TypeError("input binding digests must be canonical")
        git_ids = (self.reviewed_start_sha, self.packet_commit, self.packet_tree_hash)
        if any(
            type(value) is not str
            or len(value) != 40
            or any(character not in "0123456789abcdef" for character in value)
            for value in git_ids
        ):
            raise TypeError("input binding source IDs must be lowercase git object IDs")
        if type(self.fixture_id) is not str or not self.fixture_id:
            raise TypeError("fixture ID must be an exact nonempty string")
        if type(self.command_kind) is not str or not self.command_kind:
            raise TypeError("command kind must be an exact nonempty string")
        if (
            type(self.command_bytes) is not tuple
            or not self.command_bytes
            or any(type(value) is not bytes or not value for value in self.command_bytes)
        ):
            raise TypeError("command bytes must be an exact nonempty byte tuple")
        if type(self.pre_state_bytes) is not bytes or not self.pre_state_bytes:
            raise TypeError("pre-state bytes must be exact and nonempty")
        if type(self.context_bytes) is not bytes or not self.context_bytes:
            raise TypeError("context bytes must be exact and nonempty")


@final
@dataclass(frozen=True, slots=True)
class ObservationValueV1:
    algorithm_id: str
    algorithm_version: int
    codec_version: int
    schema_version: int
    snapshot_version: int | None
    support_root_version: int | None
    result_kind: ObservationResultKindV1
    rejection: RejectionValueV1 | None
    next_state_snapshot_bytes: bytes | None
    next_state_snapshot_root: str | None
    next_nonce_table_hash: str | None
    settlement_bytes: bytes | None
    support_root: str | None
    total_swap_fees: int | None
    fee_allocation: FCISFeeAllocationV1 | None
    bundle_bytes: CanonicalBytesFieldV1
    bundle_root: CanonicalDigestFieldV1
    commit_plan_bytes: CanonicalBytesFieldV1
    effects_bytes: CanonicalBytesFieldV1
    outbox_bytes: CanonicalBytesFieldV1
    outbox_identities: CanonicalIdentitiesFieldV1
    patch_bytes: CanonicalBytesFieldV1
    receipt_bytes: CanonicalBytesFieldV1
    receipt_root: CanonicalDigestFieldV1
    replay_bytes: CanonicalBytesFieldV1

    def __post_init__(self) -> None:
        if type(self.algorithm_id) is not str or not self.algorithm_id:
            raise TypeError("algorithm ID must be an exact nonempty string")
        versions = (
            self.algorithm_version,
            self.codec_version,
            self.schema_version,
            self.snapshot_version,
            self.support_root_version,
        )
        if any(value is not None and (type(value) is not int or value < 0) for value in versions):
            raise TypeError("observation versions must be exact nonnegative ints or None")
        if type(self.result_kind) is not ObservationResultKindV1:
            raise TypeError("observation result kind must be exact")
        if self.rejection is not None and type(self.rejection) is not RejectionValueV1:
            raise TypeError("observation rejection must be exact or None")
        byte_values = (
            self.next_state_snapshot_bytes,
            self.settlement_bytes,
        )
        if any(
            value is not None and (type(value) is not bytes or not value) for value in byte_values
        ):
            raise TypeError("observation byte values must be exact nonempty bytes or None")
        digest_values = (
            self.next_state_snapshot_root,
            self.next_nonce_table_hash,
            self.support_root,
        )
        if any(value is not None and not _is_digest_v1(value) for value in digest_values):
            raise TypeError("observation roots must be canonical digests or None")
        if self.total_swap_fees is not None and (
            type(self.total_swap_fees) is not int or self.total_swap_fees < 0
        ):
            raise TypeError("total fees must be an exact nonnegative int or None")
        if self.fee_allocation is not None and type(self.fee_allocation) is not FCISFeeAllocationV1:
            raise TypeError("fee allocation must be exact or None")
        exact_children = (
            (self.bundle_bytes, CanonicalBytesFieldV1),
            (self.bundle_root, CanonicalDigestFieldV1),
            (self.commit_plan_bytes, CanonicalBytesFieldV1),
            (self.effects_bytes, CanonicalBytesFieldV1),
            (self.outbox_bytes, CanonicalBytesFieldV1),
            (self.outbox_identities, CanonicalIdentitiesFieldV1),
            (self.patch_bytes, CanonicalBytesFieldV1),
            (self.receipt_bytes, CanonicalBytesFieldV1),
            (self.receipt_root, CanonicalDigestFieldV1),
            (self.replay_bytes, CanonicalBytesFieldV1),
        )
        if any(type(value) is not expected for value, expected in exact_children):
            raise TypeError("exact-only observation children must have exact types")


@final
@dataclass(frozen=True, slots=True)
class BoundObservationV1:
    binding: InputBindingV1
    observation: ObservationValueV1

    def __post_init__(self) -> None:
        if (
            type(self.binding) is not InputBindingV1
            or type(self.observation) is not ObservationValueV1
        ):
            raise TypeError("bound observation children must be exact")


@final
@dataclass(frozen=True, slots=True)
class ObservationPairV1:
    legacy: BoundObservationV1
    exact: BoundObservationV1
    canonical_source_bytes: bytes
    canonical_source_hash: str

    def __post_init__(self) -> None:
        if (
            type(self.legacy) is not BoundObservationV1
            or type(self.exact) is not BoundObservationV1
        ):
            raise TypeError("observation pair children must be exact")
        if type(self.canonical_source_bytes) is not bytes or not self.canonical_source_bytes:
            raise TypeError("observation pair source bytes must be exact and nonempty")
        if not _is_digest_v1(self.canonical_source_hash):
            raise TypeError("observation pair source hash must be canonical")


@final
@dataclass(frozen=True, slots=True)
class AppliedVersionDeltaV1:
    stable_id: str
    field_name: str
    legacy_value: str
    exact_value: str
    result_kind: ObservationResultKindV1

    def __post_init__(self) -> None:
        values = (self.stable_id, self.field_name, self.legacy_value, self.exact_value)
        if any(type(value) is not str or not value for value in values):
            raise TypeError("version delta fields must be exact nonempty strings")
        if type(self.result_kind) is not ObservationResultKindV1:
            raise TypeError("version delta result kind must be exact")


@final
@dataclass(frozen=True, slots=True)
class RefinementWitnessV1:
    fixture_id: str
    command_hash: str
    pre_state_root: str
    context_hash: str
    policy_version: str
    policy_hash: str
    reviewed_source_sha: str
    baseline_artifact_hash: str
    differential_artifact_hash: str
    packet_commit: str
    packet_tree_hash: str
    version_deltas: tuple[AppliedVersionDeltaV1, ...]

    def __post_init__(self) -> None:
        if type(self.fixture_id) is not str or not self.fixture_id:
            raise TypeError("witness fixture ID must be exact")
        digests = (
            self.command_hash,
            self.pre_state_root,
            self.context_hash,
            self.policy_hash,
            self.baseline_artifact_hash,
            self.differential_artifact_hash,
        )
        if any(not _is_digest_v1(value) for value in digests):
            raise TypeError("witness digests must be canonical")
        git_ids = (self.reviewed_source_sha, self.packet_commit, self.packet_tree_hash)
        if any(
            type(value) is not str
            or len(value) != 40
            or any(character not in "0123456789abcdef" for character in value)
            for value in git_ids
        ):
            raise TypeError("witness source IDs must be canonical git object IDs")
        if type(self.policy_version) is not str or not self.policy_version:
            raise TypeError("witness policy version must be exact")
        if type(self.version_deltas) is not tuple or any(
            type(delta) is not AppliedVersionDeltaV1 for delta in self.version_deltas
        ):
            raise TypeError("witness version deltas must be exact")


@final
@dataclass(frozen=True, slots=True)
class RefinesV1:
    witness: RefinementWitnessV1

    def __post_init__(self) -> None:
        if type(self.witness) is not RefinementWitnessV1:
            raise TypeError("refinement witness must be exact")


@final
@dataclass(frozen=True, slots=True)
class MismatchV1:
    code: str
    path: FieldPathV1
    legacy_value: bytes
    exact_value: bytes

    def __post_init__(self) -> None:
        if type(self.code) is not str or not self.code:
            raise TypeError("mismatch code must be exact")
        if type(self.path) is not tuple or any(type(part) not in (str, int) for part in self.path):
            raise TypeError("mismatch path must be exact")
        if type(self.legacy_value) is not bytes or type(self.exact_value) is not bytes:
            raise TypeError("mismatch values must be exact bytes")


@final
@dataclass(frozen=True, slots=True)
class InvalidEvidenceV1:
    code: str
    path: FieldPathV1

    def __post_init__(self) -> None:
        if type(self.code) is not str or not self.code:
            raise TypeError("invalid-evidence code must be exact")
        if type(self.path) is not tuple or any(type(part) not in (str, int) for part in self.path):
            raise TypeError("invalid-evidence path must be exact")


RefinementDecisionV1: TypeAlias = RefinesV1 | MismatchV1 | InvalidEvidenceV1


__all__ = (
    "AppliedVersionDeltaV1",
    "BoundObservationV1",
    "CanonicalBytesFieldV1",
    "CanonicalDigestFieldV1",
    "CanonicalIdentitiesFieldV1",
    "CanonicalParseCodeV1",
    "CanonicalParseRejectV1",
    "EvidenceFieldStatusV1",
    "FieldPathV1",
    "InputBindingV1",
    "InvalidEvidenceV1",
    "MismatchV1",
    "ObservationPairV1",
    "ObservationResultKindV1",
    "ObservationValueV1",
    "OutboxIdentityValueV1",
    "RefinementDecisionV1",
    "RefinementWitnessV1",
    "RefinesV1",
    "RejectionValueV1",
)
