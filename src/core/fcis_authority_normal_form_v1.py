"""Canonical unmounted FCIS M6 Authority Normal Form carrier.

The value names the complete root tuple that later R04 consumers must bind to
one accepted transition.  It is a research carrier, not an authority witness:
all roots are supplied by the surrounding verifier and this module only
checks exact shape, canonical encoding, and root recomputation.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast, final

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)
from .fcis_m6_profile_ids import ANF_VERSION_V1

FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1: Final[str] = ANF_VERSION_V1
FCIS_AUTHORITY_NORMAL_FORM_CODEC_VERSION_V1: Final[int] = 1
MAX_FCIS_AUTHORITY_NORMAL_FORM_BYTES_V1: Final[int] = 64 * 1024
MAX_FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1: Final[int] = 64

FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1: Final[
    tuple[str, ...]
] = (
    "command_root",
    "execution_context_root",
    "pre_state_root",
    "next_state_root",
    "support_root",
    "support_set_commitment",
    "snapshot_commitment",
    "boundary_root",
    "policy_root",
    "witness_tuple_root",
    "semantic_stream_root",
    "lineage_stream_root",
    "patch_root",
    "commit_plan_root",
    "c3_claim_set_root",
    "budget_root",
    "evaluation_certificate_root",
    "receipt_certificate_root",
    "bundle_certificate_root",
    "outbox_certificate_root",
    "acceptance_decision_root",
    "acceptance_receipt_root",
    "base_bundle_root",
    "outbox_plan_root",
    "tcg_topology_root",
    "tcg_instance_root",
    "dra_pre_history_root",
    "dra_post_history_root",
    "migration_authority_epoch_root",
)

FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1: Final[
    tuple[str, ...]
] = FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1 + (
    "proof_context_requirement",
    "proof_context_root",
)


class FCISProofContextRequirementV1(Enum):
    """Closed proof-context presence policy for one ANF value."""

    NOT_REQUIRED = "not_required"
    REQUIRED = "required"


class FCISAuthorityNormalFormCodeV1(Enum):
    """Typed fail-closed decoder outcomes for D01."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_BYTES = "invalid_bytes"
    INVALID_UTF8 = "invalid_utf8"
    INVALID_JSON = "invalid_json"
    DUPLICATE_FIELD = "duplicate_field"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    WRONG_SCHEMA = "wrong_schema"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    INVALID_VALUE = "invalid_value"
    PROOF_CONTEXT_MISMATCH = "proof_context_mismatch"


@final
@dataclass(frozen=True, slots=True)
class FCISAuthorityNormalFormRejectV1:
    """Typed rejection returned by the D01 byte decoder."""

    code: FCISAuthorityNormalFormCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not FCISAuthorityNormalFormCodeV1:
            raise TypeError("ANF rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("ANF rejection path must be an exact string tuple")


def _require_root(name: str, value: object) -> str:
    if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
        raise TypeError(f"{name} must be a canonical 0x digest")
    if value != value.lower() or any(character not in "0123456789abcdef" for character in value[2:]):
        raise ValueError(f"{name} must use lowercase hexadecimal digits")
    hex_to_bytes_fixed(value, nbytes=32, name=name)
    return value


def _reject(
    code: FCISAuthorityNormalFormCodeV1,
    *path: str,
) -> FCISAuthorityNormalFormRejectV1:
    return FCISAuthorityNormalFormRejectV1(code, path)


@final
@dataclass(frozen=True, slots=True)
class FCISAuthorityNormalFormV1:
    """One immutable root tuple for the unmounted M6 R04 transition."""

    command_root: str
    execution_context_root: str
    pre_state_root: str
    next_state_root: str
    support_root: str
    support_set_commitment: str
    snapshot_commitment: str
    boundary_root: str
    policy_root: str
    witness_tuple_root: str
    semantic_stream_root: str
    lineage_stream_root: str
    patch_root: str
    commit_plan_root: str
    c3_claim_set_root: str
    budget_root: str
    evaluation_certificate_root: str
    receipt_certificate_root: str
    bundle_certificate_root: str
    outbox_certificate_root: str
    acceptance_decision_root: str
    acceptance_receipt_root: str
    base_bundle_root: str
    outbox_plan_root: str
    tcg_topology_root: str
    tcg_instance_root: str
    dra_pre_history_root: str
    dra_post_history_root: str
    migration_authority_epoch_root: str
    proof_context_requirement: FCISProofContextRequirementV1
    proof_context_root: str | None

    def __post_init__(self) -> None:
        for field_name in FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1:
            _require_root(field_name, object.__getattribute__(self, field_name))
        if type(self.proof_context_requirement) is not FCISProofContextRequirementV1:
            raise TypeError("proof context requirement must be exact")
        if self.proof_context_requirement is FCISProofContextRequirementV1.REQUIRED:
            if self.proof_context_root is None:
                raise ValueError("required proof context root is missing")
            _require_root("proof_context_root", self.proof_context_root)
        elif self.proof_context_root is not None:
            raise ValueError("proof context root is present when proof is not required")

    @property
    def root(self) -> str:
        """Freshly recompute the complete ANF root from every field."""

        return canonical_authority_normal_form_root_v1(self)


FCISAuthorityNormalFormDecodeResultV1: TypeAlias = (
    FCISAuthorityNormalFormV1 | FCISAuthorityNormalFormRejectV1
)


def _projection(value: FCISAuthorityNormalFormV1) -> dict[str, object]:
    value.__post_init__()
    projection: dict[str, object] = {
        field_name: object.__getattribute__(value, field_name)
        for field_name in FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1
    }
    projection["proof_context_requirement"] = value.proof_context_requirement.value
    projection["proof_context_root"] = value.proof_context_root
    return projection


def encode_authority_normal_form_v1(value: object) -> bytes:
    """Encode one exact ANF value with closed canonical fields."""

    if type(value) is not FCISAuthorityNormalFormV1:
        raise TypeError("ANF codec requires an exact FCISAuthorityNormalFormV1")
    envelope = {
        "schema": FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1,
        "value": _projection(value),
    }
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_FCIS_AUTHORITY_NORMAL_FORM_BYTES_V1,
        max_depth=8,
        max_items=MAX_FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1,
    )
    return cast(bytes, canonical_json_bytes(envelope))


def canonical_authority_normal_form_root_v1(value: object) -> str:
    """Return the root freshly derived from canonical ANF bytes."""

    return cast(str, sha256_hex(encode_authority_normal_form_v1(value)))


def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def _decode_json(payload: bytes) -> object | FCISAuthorityNormalFormRejectV1:
    if len(payload) > MAX_FCIS_AUTHORITY_NORMAL_FORM_BYTES_V1:
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_BYTES, "payload")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_UTF8, "payload")
    try:
        value = json.loads(text, object_pairs_hook=_reject_duplicate_pairs)
    except ValueError as exc:
        if "duplicate JSON field" in str(exc):
            return _reject(FCISAuthorityNormalFormCodeV1.DUPLICATE_FIELD, "payload")
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_JSON, "payload")
    if type(value) is not dict:
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_JSON, "payload")
    try:
        canonical = canonical_json_bytes(value)
    except (TypeError, ValueError):
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_JSON, "payload")
    if canonical != payload:
        return _reject(FCISAuthorityNormalFormCodeV1.NONCANONICAL_BYTES, "payload")
    return value


def _decode_fields(
    value: object,
) -> dict[str, object] | FCISAuthorityNormalFormRejectV1:
    if type(value) is not dict:
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_JSON, "value")
    fields = cast(dict[str, object], value)
    actual = frozenset(fields)
    expected = frozenset(FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1)
    unknown = actual - expected
    if unknown:
        return _reject(
            FCISAuthorityNormalFormCodeV1.UNKNOWN_FIELD,
            "value",
            sorted(unknown)[0],
        )
    missing = expected - actual
    if missing:
        return _reject(
            FCISAuthorityNormalFormCodeV1.MISSING_FIELD,
            "value",
            sorted(missing)[0],
        )
    if len(fields) > MAX_FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1:
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_VALUE, "value")
    return fields


def decode_authority_normal_form_v1(payload: object) -> FCISAuthorityNormalFormDecodeResultV1:
    """Decode canonical ANF bytes into a value or a typed rejection."""

    if type(payload) is not bytes:
        return _reject(FCISAuthorityNormalFormCodeV1.WRONG_EXACT_TYPE, "payload")
    envelope = _decode_json(payload)
    if type(envelope) is FCISAuthorityNormalFormRejectV1:
        return envelope
    envelope_fields = cast(dict[str, object], envelope)
    if set(envelope_fields) != {"schema", "value"}:
        unknown = set(envelope_fields) - {"schema", "value"}
        if unknown:
            return _reject(
                FCISAuthorityNormalFormCodeV1.UNKNOWN_FIELD,
                "payload",
                sorted(unknown)[0],
            )
        return _reject(FCISAuthorityNormalFormCodeV1.MISSING_FIELD, "payload")
    if envelope_fields.get("schema") != FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1:
        return _reject(FCISAuthorityNormalFormCodeV1.WRONG_SCHEMA, "schema")
    fields = _decode_fields(envelope_fields.get("value"))
    if type(fields) is FCISAuthorityNormalFormRejectV1:
        return fields
    try:
        requirement = FCISProofContextRequirementV1(
            cast(str, fields["proof_context_requirement"])
        )
    except (TypeError, ValueError):
        return _reject(
            FCISAuthorityNormalFormCodeV1.INVALID_VALUE,
            "value",
            "proof_context_requirement",
        )
    try:
        result = FCISAuthorityNormalFormV1(
            command_root=cast(str, fields["command_root"]),
            execution_context_root=cast(str, fields["execution_context_root"]),
            pre_state_root=cast(str, fields["pre_state_root"]),
            next_state_root=cast(str, fields["next_state_root"]),
            support_root=cast(str, fields["support_root"]),
            support_set_commitment=cast(str, fields["support_set_commitment"]),
            snapshot_commitment=cast(str, fields["snapshot_commitment"]),
            boundary_root=cast(str, fields["boundary_root"]),
            policy_root=cast(str, fields["policy_root"]),
            witness_tuple_root=cast(str, fields["witness_tuple_root"]),
            semantic_stream_root=cast(str, fields["semantic_stream_root"]),
            lineage_stream_root=cast(str, fields["lineage_stream_root"]),
            patch_root=cast(str, fields["patch_root"]),
            commit_plan_root=cast(str, fields["commit_plan_root"]),
            c3_claim_set_root=cast(str, fields["c3_claim_set_root"]),
            budget_root=cast(str, fields["budget_root"]),
            evaluation_certificate_root=cast(str, fields["evaluation_certificate_root"]),
            receipt_certificate_root=cast(str, fields["receipt_certificate_root"]),
            bundle_certificate_root=cast(str, fields["bundle_certificate_root"]),
            outbox_certificate_root=cast(str, fields["outbox_certificate_root"]),
            acceptance_decision_root=cast(str, fields["acceptance_decision_root"]),
            acceptance_receipt_root=cast(str, fields["acceptance_receipt_root"]),
            base_bundle_root=cast(str, fields["base_bundle_root"]),
            outbox_plan_root=cast(str, fields["outbox_plan_root"]),
            tcg_topology_root=cast(str, fields["tcg_topology_root"]),
            tcg_instance_root=cast(str, fields["tcg_instance_root"]),
            dra_pre_history_root=cast(str, fields["dra_pre_history_root"]),
            dra_post_history_root=cast(str, fields["dra_post_history_root"]),
            migration_authority_epoch_root=cast(str, fields["migration_authority_epoch_root"]),
            proof_context_requirement=requirement,
            proof_context_root=cast(str | None, fields["proof_context_root"]),
        )
    except (TypeError, ValueError):
        return _reject(FCISAuthorityNormalFormCodeV1.INVALID_VALUE, "value")
    if (
        result.proof_context_requirement is FCISProofContextRequirementV1.REQUIRED
    ) != (result.proof_context_root is not None):
        return _reject(
            FCISAuthorityNormalFormCodeV1.PROOF_CONTEXT_MISMATCH,
            "value",
            "proof_context_root",
        )
    return result


__all__: Final[tuple[str, ...]] = (
    "FCIS_AUTHORITY_NORMAL_FORM_CODEC_VERSION_V1",
    "FCIS_AUTHORITY_NORMAL_FORM_FIELDS_V1",
    "FCIS_AUTHORITY_NORMAL_FORM_ROOT_FIELDS_V1",
    "FCIS_AUTHORITY_NORMAL_FORM_SCHEMA_ID_V1",
    "FCISProofContextRequirementV1",
    "FCISAuthorityNormalFormCodeV1",
    "FCISAuthorityNormalFormDecodeResultV1",
    "FCISAuthorityNormalFormRejectV1",
    "FCISAuthorityNormalFormV1",
    "canonical_authority_normal_form_root_v1",
    "decode_authority_normal_form_v1",
    "encode_authority_normal_form_v1",
)
