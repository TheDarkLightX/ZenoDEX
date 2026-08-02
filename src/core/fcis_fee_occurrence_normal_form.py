"""Pure unmounted Segmented Lineage Normal Form for protocol-fee witnesses.

The semantic carrier is a word of transition-local amount vectors. Same-key
witnesses are grouped only inside one accepted-transition boundary. The exact
ordered witness tuple is retained as a provenance lift above that semantic
quotient, so split/merge representations can agree semantically without becoming
lineage-identical.

Boundary and policy roots are externally supplied equality targets. This module
does not authenticate them, evaluate settlement witnesses, authorize a policy,
or publish value.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import TypeAlias, cast, final

from .fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_CANDIDATES_V2,
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
)

FEE_OCCURRENCE_NORMAL_FORM_VERSION_V1 = "zenodex/fcis/fee-occurrence-slnf/v1"
FEE_OCCURRENCE_ROLE_ORDER_V1 = ("buyback", "treasury", "rewards")
MAX_FEE_OCCURRENCE_HISTORY_SEGMENTS_V1 = 4096

_FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1 = object()
_HEX_LOWER = frozenset("0123456789abcdef")


class FeeOccurrenceNormalizationCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    INVALID_DIGEST = "invalid_digest"
    INVALID_WITNESS = "invalid_witness"
    NONCANONICAL_POSITION = "noncanonical_position"
    DUPLICATE_WITNESS = "duplicate_witness"
    DUPLICATE_BOUNDARY = "duplicate_boundary"
    AGGREGATE_OVERFLOW = "aggregate_overflow"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


def _digest_is_canonical_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 64
        and value == value.lower()
        and all(character in _HEX_LOWER for character in value)
    )


def _require_digest_v1(name: str, value: object) -> str:
    if not _digest_is_canonical_v1(value):
        raise ValueError(f"{name} must be a lowercase SHA-256 hex digest")
    return cast(str, value)


def _require_position_v1(value: object) -> int:
    if type(value) is not int:
        raise TypeError("fee witness position must be an exact integer")
    if not 0 <= value < MAX_FEE_AMOUNT_CANDIDATES_V2:
        raise ValueError("fee witness position exceeds its bounded segment")
    return value


def _require_amount_v1(value: object) -> int:
    if type(value) is not int:
        raise TypeError("fee witness amount must be an exact integer")
    if not 0 <= value <= MAX_FEE_AMOUNT_V2:
        raise ValueError("fee witness amount must be a U256 value")
    return value


def _encode_text_v1(value: str) -> bytes:
    return value.encode("utf-8")


def _encode_u256_v1(value: int) -> bytes:
    return value.to_bytes(32, "big")


def _encode_nat_v1(value: int) -> bytes:
    if not 0 <= value < 1 << 64:
        raise ValueError("fee occurrence frame integer exceeds U64")
    return value.to_bytes(8, "big")


def _encode_digest_v1(value: str) -> bytes:
    return bytes.fromhex(value)


def _hash_frames_v1(domain: str, *fields: bytes) -> str:
    digest = sha256()
    domain_bytes = domain.encode("ascii")
    digest.update(len(domain_bytes).to_bytes(4, "big"))
    digest.update(domain_bytes)
    digest.update(len(fields).to_bytes(4, "big"))
    for field in fields:
        digest.update(len(field).to_bytes(8, "big"))
        digest.update(field)
    return digest.hexdigest()


def _key_fields_v1(key: FeeApportionmentKeyV2) -> tuple[bytes, bytes]:
    return (
        _encode_text_v1(key.fee_distribution_domain_id),
        _encode_text_v1(key.asset),
    )


@final
@dataclass(frozen=True, slots=True)
class FeeWitnessOccurrenceClaimV1:
    """One untrusted fill-bound fee witness at its settlement position."""

    position: int
    key: FeeApportionmentKeyV2
    amount: int
    source_witness_root: str

    def __post_init__(self) -> None:
        _require_position_v1(self.position)
        if type(self.key) is not FeeApportionmentKeyV2:
            raise TypeError("fee witness key must be exact")
        self.key.__post_init__()
        _require_amount_v1(self.amount)
        _require_digest_v1("source witness root", self.source_witness_root)


@final
@dataclass(frozen=True, slots=True)
class FeeAllocatorOccurrenceV1:
    """One transition-local allocator invocation plus its provenance fiber."""

    key: FeeApportionmentKeyV2
    amount: int
    contributors: tuple[FeeWitnessOccurrenceClaimV1, ...]
    semantic_occurrence_root: str
    lineage_occurrence_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("fee allocator occurrence requires controlled derivation")
        _validate_allocator_occurrence_v1(self)


@final
@dataclass(frozen=True, slots=True)
class CanonicalFeeOccurrenceSegmentV1:
    """One accepted-transition semantic vector and exact witness lift."""

    boundary_root: str
    policy_root: str
    algorithm_version: str
    role_order: tuple[str, str, str]
    ordered_witnesses: tuple[FeeWitnessOccurrenceClaimV1, ...]
    occurrences: tuple[FeeAllocatorOccurrenceV1, ...]
    witness_tuple_root: str
    semantic_stream_root: str
    lineage_stream_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("fee occurrence segment requires controlled derivation")
        _validate_segment_v1(self)

    @property
    def semantic_vector(self) -> tuple[tuple[FeeApportionmentKeyV2, int], ...]:
        return tuple((occurrence.key, occurrence.amount) for occurrence in self.occurrences)


@final
@dataclass(frozen=True, slots=True)
class CanonicalFeeOccurrenceHistoryV1:
    """An ordered word of accepted-transition occurrence segments."""

    segments: tuple[CanonicalFeeOccurrenceSegmentV1, ...]
    semantic_word_root: str
    lineage_word_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("fee occurrence history requires controlled derivation")
        _validate_history_v1(self)

    @property
    def semantic_word(
        self,
    ) -> tuple[tuple[tuple[FeeApportionmentKeyV2, int], ...], ...]:
        return tuple(segment.semantic_vector for segment in self.segments)


@final
@dataclass(frozen=True, slots=True)
class FeeOccurrenceNormalizationRejectV1:
    """Stable failure with no candidate, receipt, or publication authority."""

    code: FeeOccurrenceNormalizationCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("fee occurrence rejection requires controlled derivation")
        if type(self.code) is not FeeOccurrenceNormalizationCodeV1:
            raise TypeError("fee occurrence rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("fee occurrence rejection path must be an exact string tuple")


FeeOccurrenceSegmentResultV1: TypeAlias = (
    CanonicalFeeOccurrenceSegmentV1 | FeeOccurrenceNormalizationRejectV1
)
FeeOccurrenceHistoryResultV1: TypeAlias = (
    CanonicalFeeOccurrenceHistoryV1 | FeeOccurrenceNormalizationRejectV1
)


def _reject_v1(
    code: FeeOccurrenceNormalizationCodeV1,
    *path: str,
) -> FeeOccurrenceNormalizationRejectV1:
    return FeeOccurrenceNormalizationRejectV1(
        code=code,
        path=path,
        _construction_token=_FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1,
    )


def _normalized_witness_root_v1(
    boundary_root: str,
    policy_root: str,
    witness: FeeWitnessOccurrenceClaimV1,
) -> str:
    key_domain, key_asset = _key_fields_v1(witness.key)
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/witness/v1",
        _encode_digest_v1(boundary_root),
        _encode_digest_v1(policy_root),
        _encode_nat_v1(witness.position),
        key_domain,
        key_asset,
        _encode_u256_v1(witness.amount),
        _encode_digest_v1(witness.source_witness_root),
    )


def _semantic_occurrence_root_v1(
    boundary_root: str,
    policy_root: str,
    key: FeeApportionmentKeyV2,
    amount: int,
) -> str:
    key_domain, key_asset = _key_fields_v1(key)
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/semantic/v1",
        _encode_text_v1(FEE_OCCURRENCE_NORMAL_FORM_VERSION_V1),
        _encode_text_v1(SRGD_ALGORITHM_VERSION_V1),
        *(_encode_text_v1(role) for role in FEE_OCCURRENCE_ROLE_ORDER_V1),
        _encode_digest_v1(boundary_root),
        _encode_digest_v1(policy_root),
        key_domain,
        key_asset,
        _encode_u256_v1(amount),
    )


def _lineage_occurrence_root_v1(
    semantic_root: str,
    normalized_witness_roots: tuple[str, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/lineage/v1",
        _encode_digest_v1(semantic_root),
        _encode_nat_v1(len(normalized_witness_roots)),
        *(_encode_digest_v1(root) for root in normalized_witness_roots),
    )


def _witness_tuple_root_v1(
    boundary_root: str,
    policy_root: str,
    normalized_witness_roots: tuple[str, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/witness-tuple/v1",
        _encode_digest_v1(boundary_root),
        _encode_digest_v1(policy_root),
        _encode_nat_v1(len(normalized_witness_roots)),
        *(_encode_digest_v1(root) for root in normalized_witness_roots),
    )


def _semantic_stream_root_v1(
    boundary_root: str,
    policy_root: str,
    occurrences: tuple[FeeAllocatorOccurrenceV1, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/semantic-stream/v1",
        _encode_text_v1(FEE_OCCURRENCE_NORMAL_FORM_VERSION_V1),
        _encode_digest_v1(boundary_root),
        _encode_digest_v1(policy_root),
        _encode_nat_v1(len(occurrences)),
        *(_encode_digest_v1(item.semantic_occurrence_root) for item in occurrences),
    )


def _lineage_stream_root_v1(
    semantic_stream_root: str,
    witness_tuple_root: str,
    occurrences: tuple[FeeAllocatorOccurrenceV1, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/lineage-stream/v1",
        _encode_digest_v1(semantic_stream_root),
        _encode_digest_v1(witness_tuple_root),
        _encode_nat_v1(len(occurrences)),
        *(_encode_digest_v1(item.lineage_occurrence_root) for item in occurrences),
    )


def _validate_allocator_occurrence_v1(occurrence: FeeAllocatorOccurrenceV1) -> None:
    if type(occurrence.key) is not FeeApportionmentKeyV2:
        raise TypeError("fee allocator occurrence key must be exact")
    occurrence.key.__post_init__()
    _require_amount_v1(occurrence.amount)
    if type(occurrence.contributors) is not tuple or not occurrence.contributors:
        raise TypeError("fee allocator occurrence contributors must be a nonempty exact tuple")
    previous_position = -1
    for contributor in occurrence.contributors:
        if type(contributor) is not FeeWitnessOccurrenceClaimV1:
            raise TypeError("fee allocator occurrence contributor must be exact")
        contributor.__post_init__()
        if contributor.key != occurrence.key:
            raise ValueError("fee allocator occurrence contributor key mismatch")
        if contributor.position <= previous_position:
            raise ValueError("fee allocator occurrence contributors must retain settlement order")
        previous_position = contributor.position
    if sum(contributor.amount for contributor in occurrence.contributors) != occurrence.amount:
        raise ValueError("fee allocator occurrence amount does not match its provenance")
    _require_digest_v1("semantic occurrence root", occurrence.semantic_occurrence_root)
    _require_digest_v1("lineage occurrence root", occurrence.lineage_occurrence_root)


def _validate_segment_v1(segment: CanonicalFeeOccurrenceSegmentV1) -> None:
    boundary_root = _require_digest_v1("boundary root", segment.boundary_root)
    policy_root = _require_digest_v1("policy root", segment.policy_root)
    if segment.algorithm_version != SRGD_ALGORITHM_VERSION_V1:
        raise ValueError("fee occurrence segment algorithm version mismatch")
    if segment.role_order != FEE_OCCURRENCE_ROLE_ORDER_V1:
        raise ValueError("fee occurrence segment role order mismatch")
    if type(segment.ordered_witnesses) is not tuple:
        raise TypeError("fee occurrence ordered witnesses must be an exact tuple")
    if type(segment.occurrences) is not tuple:
        raise TypeError("fee occurrence allocator stream must be an exact tuple")
    if len(segment.ordered_witnesses) > MAX_FEE_AMOUNT_CANDIDATES_V2:
        raise ValueError("fee occurrence witness limit exceeded")
    for witness in segment.ordered_witnesses:
        if type(witness) is not FeeWitnessOccurrenceClaimV1:
            raise TypeError("fee occurrence witness must be exact")
        witness.__post_init__()
    positions = tuple(witness.position for witness in segment.ordered_witnesses)
    if positions != tuple(range(len(segment.ordered_witnesses))):
        raise ValueError("fee occurrence witness positions are noncanonical")
    if len({witness.source_witness_root for witness in segment.ordered_witnesses}) != len(
        segment.ordered_witnesses
    ):
        raise ValueError("fee occurrence source witness roots must be unique")
    previous_key: tuple[bytes, bytes] | None = None
    for occurrence in segment.occurrences:
        if type(occurrence) is not FeeAllocatorOccurrenceV1:
            raise TypeError("fee occurrence allocator item must be exact")
        _validate_allocator_occurrence_v1(occurrence)
        current_key = occurrence.key.protocol_order_key
        if previous_key is not None and previous_key >= current_key:
            raise ValueError("fee allocator occurrences must be in strict protocol order")
        previous_key = current_key
    recovered = tuple(
        sorted(
            (
                contributor
                for occurrence in segment.occurrences
                for contributor in occurrence.contributors
            ),
            key=lambda witness: witness.position,
        )
    )
    if recovered != segment.ordered_witnesses:
        raise ValueError("fee occurrence provenance does not reconstruct the witness tuple")
    normalized_roots = tuple(
        _normalized_witness_root_v1(boundary_root, policy_root, witness)
        for witness in segment.ordered_witnesses
    )
    if segment.witness_tuple_root != _witness_tuple_root_v1(
        boundary_root,
        policy_root,
        normalized_roots,
    ):
        raise ValueError("fee occurrence witness tuple root mismatch")
    root_by_position = {
        witness.position: normalized_root
        for witness, normalized_root in zip(
            segment.ordered_witnesses,
            normalized_roots,
            strict=True,
        )
    }
    for occurrence in segment.occurrences:
        expected_semantic = _semantic_occurrence_root_v1(
            boundary_root,
            policy_root,
            occurrence.key,
            occurrence.amount,
        )
        expected_lineage = _lineage_occurrence_root_v1(
            expected_semantic,
            tuple(root_by_position[item.position] for item in occurrence.contributors),
        )
        if occurrence.semantic_occurrence_root != expected_semantic:
            raise ValueError("fee occurrence semantic root mismatch")
        if occurrence.lineage_occurrence_root != expected_lineage:
            raise ValueError("fee occurrence lineage root mismatch")
    expected_semantic_stream = _semantic_stream_root_v1(
        boundary_root,
        policy_root,
        segment.occurrences,
    )
    expected_lineage_stream = _lineage_stream_root_v1(
        expected_semantic_stream,
        segment.witness_tuple_root,
        segment.occurrences,
    )
    if segment.semantic_stream_root != expected_semantic_stream:
        raise ValueError("fee occurrence semantic stream root mismatch")
    if segment.lineage_stream_root != expected_lineage_stream:
        raise ValueError("fee occurrence lineage stream root mismatch")


def _validate_history_v1(history: CanonicalFeeOccurrenceHistoryV1) -> None:
    if type(history.segments) is not tuple:
        raise TypeError("fee occurrence history segments must be an exact tuple")
    if len(history.segments) > MAX_FEE_OCCURRENCE_HISTORY_SEGMENTS_V1:
        raise ValueError("fee occurrence history segment limit exceeded")
    for segment in history.segments:
        if type(segment) is not CanonicalFeeOccurrenceSegmentV1:
            raise TypeError("fee occurrence history segment must be exact")
        _validate_segment_v1(segment)
    boundaries = tuple(segment.boundary_root for segment in history.segments)
    if len(set(boundaries)) != len(boundaries):
        raise ValueError("fee occurrence history contains duplicate boundaries")
    expected_semantic = _semantic_word_root_v1(history.segments)
    expected_lineage = _lineage_word_root_v1(expected_semantic, history.segments)
    if history.semantic_word_root != expected_semantic:
        raise ValueError("fee occurrence semantic word root mismatch")
    if history.lineage_word_root != expected_lineage:
        raise ValueError("fee occurrence lineage word root mismatch")


def canonicalize_fee_occurrence_segment_v1(
    *,
    boundary_root: object,
    policy_root: object,
    witnesses: object,
) -> FeeOccurrenceSegmentResultV1:
    """Group exact same-key witnesses inside one externally fixed boundary."""

    if not _digest_is_canonical_v1(boundary_root):
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.INVALID_DIGEST, "boundary_root")
    if not _digest_is_canonical_v1(policy_root):
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.INVALID_DIGEST, "policy_root")
    if type(witnesses) is not tuple:
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.WRONG_EXACT_TYPE, "witnesses")
    exact_witnesses = cast(tuple[object, ...], witnesses)
    if len(exact_witnesses) > MAX_FEE_AMOUNT_CANDIDATES_V2:
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.ITEM_LIMIT, "witnesses")
    for index, witness_object in enumerate(exact_witnesses):
        if type(witness_object) is not FeeWitnessOccurrenceClaimV1:
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.WRONG_EXACT_TYPE,
                "witnesses",
                str(index),
            )
        try:
            witness_object.__post_init__()
        except (TypeError, ValueError, ArithmeticError):
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.INVALID_WITNESS,
                "witnesses",
                str(index),
            )
    typed_witnesses = cast(tuple[FeeWitnessOccurrenceClaimV1, ...], exact_witnesses)
    ordered = tuple(sorted(typed_witnesses, key=lambda witness: witness.position))
    if tuple(witness.position for witness in ordered) != tuple(range(len(ordered))):
        return _reject_v1(
            FeeOccurrenceNormalizationCodeV1.NONCANONICAL_POSITION,
            "witnesses",
            "position",
        )
    if len({witness.source_witness_root for witness in ordered}) != len(ordered):
        return _reject_v1(
            FeeOccurrenceNormalizationCodeV1.DUPLICATE_WITNESS,
            "witnesses",
            "source_witness_root",
        )

    exact_boundary = cast(str, boundary_root)
    exact_policy = cast(str, policy_root)
    normalized_roots = tuple(
        _normalized_witness_root_v1(exact_boundary, exact_policy, witness) for witness in ordered
    )
    root_by_position = {
        witness.position: root for witness, root in zip(ordered, normalized_roots, strict=True)
    }
    witness_tuple_root = _witness_tuple_root_v1(
        exact_boundary,
        exact_policy,
        normalized_roots,
    )
    grouped: dict[FeeApportionmentKeyV2, list[FeeWitnessOccurrenceClaimV1]] = {}
    for witness in ordered:
        grouped.setdefault(witness.key, []).append(witness)

    occurrences: list[FeeAllocatorOccurrenceV1] = []
    for key in sorted(grouped, key=lambda item: item.protocol_order_key):
        contributors = tuple(grouped[key])
        amount = sum(contributor.amount for contributor in contributors)
        if amount > MAX_FEE_AMOUNT_V2:
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.AGGREGATE_OVERFLOW,
                "witnesses",
                "aggregate",
                key.fee_distribution_domain_id,
                key.asset,
            )
        semantic_root = _semantic_occurrence_root_v1(
            exact_boundary,
            exact_policy,
            key,
            amount,
        )
        lineage_root = _lineage_occurrence_root_v1(
            semantic_root,
            tuple(root_by_position[item.position] for item in contributors),
        )
        try:
            occurrences.append(
                FeeAllocatorOccurrenceV1(
                    key=key,
                    amount=amount,
                    contributors=contributors,
                    semantic_occurrence_root=semantic_root,
                    lineage_occurrence_root=lineage_root,
                    _construction_token=_FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1,
                )
            )
        except (TypeError, ValueError, ArithmeticError):
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.INTERNAL_RELATION_FAILURE,
                "occurrences",
            )
    exact_occurrences = tuple(occurrences)
    semantic_stream_root = _semantic_stream_root_v1(
        exact_boundary,
        exact_policy,
        exact_occurrences,
    )
    lineage_stream_root = _lineage_stream_root_v1(
        semantic_stream_root,
        witness_tuple_root,
        exact_occurrences,
    )
    try:
        return CanonicalFeeOccurrenceSegmentV1(
            boundary_root=exact_boundary,
            policy_root=exact_policy,
            algorithm_version=SRGD_ALGORITHM_VERSION_V1,
            role_order=FEE_OCCURRENCE_ROLE_ORDER_V1,
            ordered_witnesses=ordered,
            occurrences=exact_occurrences,
            witness_tuple_root=witness_tuple_root,
            semantic_stream_root=semantic_stream_root,
            lineage_stream_root=lineage_stream_root,
            _construction_token=_FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FeeOccurrenceNormalizationCodeV1.INTERNAL_RELATION_FAILURE,
            "segment",
        )


def _semantic_word_root_v1(
    segments: tuple[CanonicalFeeOccurrenceSegmentV1, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/semantic-word/v1",
        _encode_text_v1(FEE_OCCURRENCE_NORMAL_FORM_VERSION_V1),
        _encode_nat_v1(len(segments)),
        *(_encode_digest_v1(segment.semantic_stream_root) for segment in segments),
    )


def _lineage_word_root_v1(
    semantic_word_root: str,
    segments: tuple[CanonicalFeeOccurrenceSegmentV1, ...],
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/lineage-word/v1",
        _encode_digest_v1(semantic_word_root),
        _encode_nat_v1(len(segments)),
        *(_encode_digest_v1(segment.lineage_stream_root) for segment in segments),
    )


def canonicalize_fee_occurrence_history_v1(
    segments: object,
) -> FeeOccurrenceHistoryResultV1:
    """Retain the ordered free word of already normalized transition segments."""

    if type(segments) is not tuple:
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.WRONG_EXACT_TYPE, "segments")
    exact_objects = cast(tuple[object, ...], segments)
    if len(exact_objects) > MAX_FEE_OCCURRENCE_HISTORY_SEGMENTS_V1:
        return _reject_v1(FeeOccurrenceNormalizationCodeV1.ITEM_LIMIT, "segments")
    for index, segment_object in enumerate(exact_objects):
        if type(segment_object) is not CanonicalFeeOccurrenceSegmentV1:
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.WRONG_EXACT_TYPE,
                "segments",
                str(index),
            )
        try:
            _validate_segment_v1(segment_object)
        except (TypeError, ValueError, ArithmeticError):
            return _reject_v1(
                FeeOccurrenceNormalizationCodeV1.INTERNAL_RELATION_FAILURE,
                "segments",
                str(index),
            )
    exact_segments = cast(tuple[CanonicalFeeOccurrenceSegmentV1, ...], exact_objects)
    boundaries = tuple(segment.boundary_root for segment in exact_segments)
    if len(set(boundaries)) != len(boundaries):
        return _reject_v1(
            FeeOccurrenceNormalizationCodeV1.DUPLICATE_BOUNDARY,
            "segments",
            "boundary_root",
        )
    semantic_word_root = _semantic_word_root_v1(exact_segments)
    lineage_word_root = _lineage_word_root_v1(semantic_word_root, exact_segments)
    try:
        return CanonicalFeeOccurrenceHistoryV1(
            segments=exact_segments,
            semantic_word_root=semantic_word_root,
            lineage_word_root=lineage_word_root,
            _construction_token=_FEE_OCCURRENCE_CONSTRUCTION_TOKEN_V1,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FeeOccurrenceNormalizationCodeV1.INTERNAL_RELATION_FAILURE,
            "history",
        )


def fee_amount_candidates_from_segment_v1(
    segment: CanonicalFeeOccurrenceSegmentV1,
) -> tuple[FeeAmountCandidateV2, ...]:
    """Project one segment to the existing allocator input without flattening history."""

    if type(segment) is not CanonicalFeeOccurrenceSegmentV1:
        raise TypeError("fee occurrence segment projection requires the exact type")
    _validate_segment_v1(segment)
    return tuple(
        FeeAmountCandidateV2(occurrence.key, occurrence.amount)
        for occurrence in segment.occurrences
    )


def fee_amount_candidate_word_from_history_v1(
    history: CanonicalFeeOccurrenceHistoryV1,
) -> tuple[tuple[FeeAmountCandidateV2, ...], ...]:
    """Project history as a tuple of segments; no boundary-erasing flat API is supplied."""

    if type(history) is not CanonicalFeeOccurrenceHistoryV1:
        raise TypeError("fee occurrence history projection requires the exact type")
    _validate_history_v1(history)
    return tuple(fee_amount_candidates_from_segment_v1(segment) for segment in history.segments)


__all__ = (
    "CanonicalFeeOccurrenceHistoryV1",
    "CanonicalFeeOccurrenceSegmentV1",
    "FEE_OCCURRENCE_NORMAL_FORM_VERSION_V1",
    "FEE_OCCURRENCE_ROLE_ORDER_V1",
    "FeeAllocatorOccurrenceV1",
    "FeeOccurrenceHistoryResultV1",
    "FeeOccurrenceNormalizationCodeV1",
    "FeeOccurrenceNormalizationRejectV1",
    "FeeOccurrenceSegmentResultV1",
    "FeeWitnessOccurrenceClaimV1",
    "canonicalize_fee_occurrence_history_v1",
    "canonicalize_fee_occurrence_segment_v1",
    "fee_amount_candidate_word_from_history_v1",
    "fee_amount_candidates_from_segment_v1",
)
