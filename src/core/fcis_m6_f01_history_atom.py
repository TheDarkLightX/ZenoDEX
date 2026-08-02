"""Canonical research schema for the FCIS M6 authoritative history atom.

F01 gives the later durable-retraction tasks one owned value that carries the
transition facts which must be published together.  It deliberately grants no
runtime authority and does not authenticate a caller.  Its purpose is to make
omission, crossing, non-canonical encoding, and stale derived roots visible at
the value boundary.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)
from .fcis_durable_retraction import (
    derive_destination_idempotency_root,
    derive_effect_id,
)
from .fcis_m6_e01_request_identity import E01CommandFamilyV1
from .fcis_m6_e02_nonce_nullifier import MAX_E02_U64_V1, nullifier_root_from_body_v1

FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f01/history-atom/v1"
FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f01/history-nullifier/v1"
FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f01/history-outbox/v1"
FCIS_M6_F01_MAX_ATOM_BYTES_V1: Final[int] = 512 * 1024
FCIS_M6_F01_MAX_OUTBOX_RECORDS_V1: Final[int] = 4_096
FCIS_M6_F01_MAX_TEXT_BYTES_V1: Final[int] = 256
FCIS_M6_F01_MAX_U32_V1: Final[int] = (1 << 32) - 1

_HEX_DIGITS: Final[frozenset[str]] = frozenset("0123456789abcdef")
_NO_PROOF_CONTEXT_ROOT_V1: Final[str] = sha256_hex(
    domain_sep_bytes("zenodex/fcis/m6/f01/no-proof-context", version=1)
)


class F01HistoryAtomError(ValueError):
    """Raised when a history-atom value is outside its closed schema."""


class F01HistoryAtomCodeV1(Enum):
    """Stable fail-closed outcomes for the canonical atom decoder."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_BYTES = "invalid_bytes"
    INVALID_UTF8 = "invalid_utf8"
    INVALID_JSON = "invalid_json"
    DUPLICATE_FIELD = "duplicate_field"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    WRONG_SCHEMA = "wrong_schema"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    INVALID_VALUE = "invalid_value"


class F01ProofContextRequirementV1(Enum):
    """Closed proof-context policy carried by every atom."""

    NOT_REQUIRED = "not_required"
    REQUIRED = "required"


def _text(value: object, name: str, *, maximum_bytes: int = FCIS_M6_F01_MAX_TEXT_BYTES_V1) -> str:
    if type(value) is not str or not value:
        raise F01HistoryAtomError(f"{name} must be a nonempty exact string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise F01HistoryAtomError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > maximum_bytes:
        raise F01HistoryAtomError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise F01HistoryAtomError(f"{name} contains a control character")
    return value


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _HEX_DIGITS for character in value[2:])
    ):
        raise F01HistoryAtomError(f"{name} must be a lowercase 0x digest")
    try:
        hex_to_bytes_fixed(value, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise F01HistoryAtomError(f"{name} must be a 32-byte digest") from exc
    return value


def _u32(value: object, name: str, *, positive: bool = False) -> int:
    minimum = 1 if positive else 0
    if type(value) is not int or value < minimum or value > FCIS_M6_F01_MAX_U32_V1:
        raise F01HistoryAtomError(f"{name} is outside its closed u32 domain")
    return value


def _nonce(value: object) -> int:
    if type(value) is not int or value < 1 or value > MAX_E02_U64_V1:
        raise F01HistoryAtomError("nonce is outside its closed u64 domain")
    return value


def _raw_root(value: str) -> str:
    return value[2:]


@dataclass(frozen=True, slots=True)
class F01HistoryNullifierV1:
    """Durable projection of the E02 sender/nonce nullifier relation."""

    deployment_config_root: str
    sender_id: str
    command_family: E01CommandFamilyV1
    nonce: int
    request_identity_root: str
    nullifier_root: str

    def __post_init__(self) -> None:
        _root(self.deployment_config_root, "nullifier.deployment_config_root")
        _text(self.sender_id, "nullifier.sender_id")
        if type(self.command_family) is not E01CommandFamilyV1:
            raise F01HistoryAtomError("nullifier.command_family has the wrong exact type")
        _nonce(self.nonce)
        _root(self.request_identity_root, "nullifier.request_identity_root")
        checked_root = _root(self.nullifier_root, "nullifier.nullifier_root")
        try:
            expected = nullifier_root_from_body_v1(
                {
                    "deployment_config_root": _raw_root(self.deployment_config_root),
                    "sender_id": self.sender_id,
                    "command_family": self.command_family.value,
                    "nonce": self.nonce,
                }
            )
        except (TypeError, ValueError, ArithmeticError) as exc:
            raise F01HistoryAtomError("E02 nullifier preimage is invalid") from exc
        if checked_root != f"0x{expected}":
            raise F01HistoryAtomError("nullifier root does not rederive from E02 fields")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1,
            "deployment_config_root": self.deployment_config_root,
            "sender_id": self.sender_id,
            "command_family": self.command_family.value,
            "nonce": self.nonce,
            "request_identity_root": self.request_identity_root,
            "nullifier_root": self.nullifier_root,
        }


@dataclass(frozen=True, slots=True)
class F01HistoryOutboxRecordV1:
    """One canonical outbox projection nested inside the publication atom."""

    ordinal: int
    effect_id: str
    destination: str
    payload_root: str
    adapter_profile_root: str
    idempotency_root: str

    def __post_init__(self) -> None:
        _u32(self.ordinal, "outbox.ordinal")
        _root(self.effect_id, "outbox.effect_id")
        _text(self.destination, "outbox.destination")
        _root(self.payload_root, "outbox.payload_root")
        _root(self.adapter_profile_root, "outbox.adapter_profile_root")
        _root(self.idempotency_root, "outbox.idempotency_root")

    def validate_for_atom(self, *, commit_id: str, writer_profile_root: str) -> None:
        """Check effect and idempotency roots against the owning atom."""

        _root(commit_id, "commit_id")
        _root(writer_profile_root, "writer_profile_root")
        expected_effect = derive_effect_id(
            commit_id=_raw_root(commit_id),
            ordinal=self.ordinal,
            destination=self.destination,
            payload_root=_raw_root(self.payload_root),
            writer_profile_root=_raw_root(writer_profile_root),
        )
        if self.effect_id != f"0x{expected_effect}":
            raise F01HistoryAtomError("outbox effect ID is crossed with its atom")
        expected_idempotency = derive_destination_idempotency_root(expected_effect)
        if self.idempotency_root != f"0x{expected_idempotency}":
            raise F01HistoryAtomError("outbox idempotency root does not rederive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1,
            "ordinal": self.ordinal,
            "effect_id": self.effect_id,
            "destination": self.destination,
            "payload_root": self.payload_root,
            "adapter_profile_root": self.adapter_profile_root,
            "idempotency_root": self.idempotency_root,
        }


@dataclass(frozen=True, slots=True)
class F01HistoryAtomV1:
    """One complete immutable transition atom for later durable refinement."""

    sequence: int
    commit_id: str
    command_root: str
    expected_pre_state_root: str
    post_state_root: str
    deployment_config_root: str
    verifier_profile_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    anf_root: str
    proof_context_requirement: F01ProofContextRequirementV1
    proof_context_root: str
    nullifier: F01HistoryNullifierV1
    response_root: str
    receipt_root: str
    decision_root: str
    bundle_root: str
    replay_root: str
    outbox: tuple[F01HistoryOutboxRecordV1, ...]

    def __post_init__(self) -> None:
        _u32(self.sequence, "sequence", positive=True)
        for name in (
            "commit_id",
            "command_root",
            "expected_pre_state_root",
            "post_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "writer_profile_root",
            "authority_state_root",
            "anf_root",
            "response_root",
            "receipt_root",
            "decision_root",
            "bundle_root",
            "replay_root",
        ):
            _root(object.__getattribute__(self, name), name)
        _u32(self.authority_epoch_index, "authority_epoch_index")
        if type(self.proof_context_requirement) is not F01ProofContextRequirementV1:
            raise F01HistoryAtomError("proof_context_requirement has the wrong exact type")
        _root(self.proof_context_root, "proof_context_root")
        if self.proof_context_requirement is F01ProofContextRequirementV1.NOT_REQUIRED:
            if self.proof_context_root != _NO_PROOF_CONTEXT_ROOT_V1:
                raise F01HistoryAtomError("not-required proof context has a non-sentinel root")
        if type(self.nullifier) is not F01HistoryNullifierV1:
            raise F01HistoryAtomError("nullifier has the wrong exact type")
        self.nullifier.__post_init__()
        if self.nullifier.deployment_config_root != self.deployment_config_root:
            raise F01HistoryAtomError("nullifier is crossed with deployment context")
        if type(self.outbox) is not tuple:
            raise F01HistoryAtomError("outbox must be an exact tuple")
        if len(self.outbox) > FCIS_M6_F01_MAX_OUTBOX_RECORDS_V1:
            raise F01HistoryAtomError("outbox exceeds its closed collection bound")
        for record in self.outbox:
            if type(record) is not F01HistoryOutboxRecordV1:
                raise F01HistoryAtomError("outbox contains the wrong exact type")
            record.__post_init__()
            record.validate_for_atom(
                commit_id=self.commit_id,
                writer_profile_root=self.writer_profile_root,
            )
        if tuple(record.ordinal for record in self.outbox) != tuple(range(len(self.outbox))):
            raise F01HistoryAtomError("outbox ordinals must be contiguous")
        effect_ids = tuple(record.effect_id for record in self.outbox)
        if len(effect_ids) != len(set(effect_ids)):
            raise F01HistoryAtomError("outbox effect IDs must be unique")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        value: dict[str, object] = {
            "sequence": self.sequence,
            "commit_id": self.commit_id,
            "command_root": self.command_root,
            "expected_pre_state_root": self.expected_pre_state_root,
            "post_state_root": self.post_state_root,
            "deployment_config_root": self.deployment_config_root,
            "verifier_profile_root": self.verifier_profile_root,
            "writer_profile_root": self.writer_profile_root,
            "authority_epoch_index": self.authority_epoch_index,
            "authority_state_root": self.authority_state_root,
            "anf_root": self.anf_root,
            "proof_context_requirement": self.proof_context_requirement.value,
            "proof_context_root": self.proof_context_root,
            "nullifier": self.nullifier.to_wire(),
            "response_root": self.response_root,
            "receipt_root": self.receipt_root,
            "decision_root": self.decision_root,
            "bundle_root": self.bundle_root,
            "replay_root": self.replay_root,
            "outbox": [record.to_wire() for record in self.outbox],
        }
        return {"schema": FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1, "value": value}

    @property
    def atom_root(self) -> str:
        return cast(str, sha256_hex(encode_history_atom_v1(self)))


@dataclass(frozen=True, slots=True)
class F01HistoryAtomRejectV1:
    """Typed partial-decoder rejection; no partially trusted atom is returned."""

    code: F01HistoryAtomCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F01HistoryAtomCodeV1:
            raise F01HistoryAtomError("rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F01HistoryAtomError("rejection path must be an exact string tuple")


F01HistoryAtomDecodeResultV1: TypeAlias = F01HistoryAtomV1 | F01HistoryAtomRejectV1


def _reject(code: F01HistoryAtomCodeV1, *path: str) -> F01HistoryAtomRejectV1:
    return F01HistoryAtomRejectV1(code, path)


def encode_history_atom_v1(value: object) -> bytes:
    """Encode one exact atom using closed canonical JSON fields."""

    if type(value) is not F01HistoryAtomV1:
        raise F01HistoryAtomError("history atom codec requires an exact F01HistoryAtomV1")
    payload = value.to_wire()
    try:
        bounded_json_utf8_size(
            payload,
            max_bytes=FCIS_M6_F01_MAX_ATOM_BYTES_V1,
            max_depth=8,
            max_items=FCIS_M6_F01_MAX_OUTBOX_RECORDS_V1 * 8 + 128,
        )
        return cast(bytes, canonical_json_bytes(payload))
    except (TypeError, ValueError) as exc:
        raise F01HistoryAtomError("history atom exceeds canonical codec bounds") from exc


def history_atom_root_v1(value: object) -> str:
    """Recompute the complete atom root from canonical bytes."""

    return cast(str, sha256_hex(encode_history_atom_v1(value)))


def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def _mapping(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        raise F01HistoryAtomError(f"{path} must be an exact object")
    return cast(dict[str, object], value)


def _exact_fields(value: dict[str, object], expected: frozenset[str], path: str) -> None:
    actual = frozenset(value)
    if actual - expected:
        raise F01HistoryAtomError(f"{path} contains an unknown field")
    if expected - actual:
        raise F01HistoryAtomError(f"{path} is missing a required field")


def _field_text(value: dict[str, object], key: str, path: str) -> str:
    raw = value[key]
    if type(raw) is not str:
        raise F01HistoryAtomError(f"{path}.{key} must be text")
    return raw


def _field_int(value: dict[str, object], key: str, path: str) -> int:
    raw = value[key]
    if type(raw) is not int:
        raise F01HistoryAtomError(f"{path}.{key} must be an exact integer")
    return raw


def _decode_nullifier(value: object) -> F01HistoryNullifierV1:
    fields = _mapping(value, "value.nullifier")
    expected = frozenset(
        {
            "schema",
            "deployment_config_root",
            "sender_id",
            "command_family",
            "nonce",
            "request_identity_root",
            "nullifier_root",
        }
    )
    _exact_fields(fields, expected, "value.nullifier")
    if _field_text(fields, "schema", "value.nullifier") != (
        FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1
    ):
        raise F01HistoryAtomError("nullifier schema is not the F01 schema")
    family_raw = _field_text(fields, "command_family", "value.nullifier")
    try:
        family = E01CommandFamilyV1(family_raw)
    except ValueError as exc:
        raise F01HistoryAtomError("nullifier command family is outside the closed enum") from exc
    return F01HistoryNullifierV1(
        deployment_config_root=_field_text(fields, "deployment_config_root", "value.nullifier"),
        sender_id=_field_text(fields, "sender_id", "value.nullifier"),
        command_family=family,
        nonce=_field_int(fields, "nonce", "value.nullifier"),
        request_identity_root=_field_text(fields, "request_identity_root", "value.nullifier"),
        nullifier_root=_field_text(fields, "nullifier_root", "value.nullifier"),
    )


def _decode_outbox(value: object, index: int) -> F01HistoryOutboxRecordV1:
    fields = _mapping(value, f"value.outbox[{index}]")
    expected = frozenset(
        {
            "schema",
            "ordinal",
            "effect_id",
            "destination",
            "payload_root",
            "adapter_profile_root",
            "idempotency_root",
        }
    )
    _exact_fields(fields, expected, f"value.outbox[{index}]")
    if _field_text(fields, "schema", f"value.outbox[{index}]") != (
        FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1
    ):
        raise F01HistoryAtomError("outbox record schema is not the F01 schema")
    return F01HistoryOutboxRecordV1(
        ordinal=_field_int(fields, "ordinal", f"value.outbox[{index}]"),
        effect_id=_field_text(fields, "effect_id", f"value.outbox[{index}]"),
        destination=_field_text(fields, "destination", f"value.outbox[{index}]"),
        payload_root=_field_text(fields, "payload_root", f"value.outbox[{index}]"),
        adapter_profile_root=_field_text(fields, "adapter_profile_root", f"value.outbox[{index}]"),
        idempotency_root=_field_text(fields, "idempotency_root", f"value.outbox[{index}]"),
    )


def _decode_value(value: object) -> F01HistoryAtomV1:
    fields = _mapping(value, "value")
    expected = frozenset(
        {
            "sequence",
            "commit_id",
            "command_root",
            "expected_pre_state_root",
            "post_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "writer_profile_root",
            "authority_epoch_index",
            "authority_state_root",
            "anf_root",
            "proof_context_requirement",
            "proof_context_root",
            "nullifier",
            "response_root",
            "receipt_root",
            "decision_root",
            "bundle_root",
            "replay_root",
            "outbox",
        }
    )
    _exact_fields(fields, expected, "value")
    requirement_raw = _field_text(fields, "proof_context_requirement", "value")
    try:
        requirement = F01ProofContextRequirementV1(requirement_raw)
    except ValueError as exc:
        raise F01HistoryAtomError("proof context requirement is outside the closed enum") from exc
    outbox_raw = fields["outbox"]
    if type(outbox_raw) is not list:
        raise F01HistoryAtomError("value.outbox must be an exact list on the wire")
    if len(outbox_raw) > FCIS_M6_F01_MAX_OUTBOX_RECORDS_V1:
        raise F01HistoryAtomError("value.outbox exceeds its closed collection bound")
    return F01HistoryAtomV1(
        sequence=_field_int(fields, "sequence", "value"),
        commit_id=_field_text(fields, "commit_id", "value"),
        command_root=_field_text(fields, "command_root", "value"),
        expected_pre_state_root=_field_text(fields, "expected_pre_state_root", "value"),
        post_state_root=_field_text(fields, "post_state_root", "value"),
        deployment_config_root=_field_text(fields, "deployment_config_root", "value"),
        verifier_profile_root=_field_text(fields, "verifier_profile_root", "value"),
        writer_profile_root=_field_text(fields, "writer_profile_root", "value"),
        authority_epoch_index=_field_int(fields, "authority_epoch_index", "value"),
        authority_state_root=_field_text(fields, "authority_state_root", "value"),
        anf_root=_field_text(fields, "anf_root", "value"),
        proof_context_requirement=requirement,
        proof_context_root=_field_text(fields, "proof_context_root", "value"),
        nullifier=_decode_nullifier(fields["nullifier"]),
        response_root=_field_text(fields, "response_root", "value"),
        receipt_root=_field_text(fields, "receipt_root", "value"),
        decision_root=_field_text(fields, "decision_root", "value"),
        bundle_root=_field_text(fields, "bundle_root", "value"),
        replay_root=_field_text(fields, "replay_root", "value"),
        outbox=tuple(
            _decode_outbox(raw, index) for index, raw in enumerate(cast(list[object], outbox_raw))
        ),
    )


def decode_history_atom_v1(payload: object) -> F01HistoryAtomDecodeResultV1:
    """Decode only a complete canonical atom, otherwise return typed reject."""

    if type(payload) is not bytes:
        return _reject(F01HistoryAtomCodeV1.WRONG_EXACT_TYPE, "payload")
    if len(payload) > FCIS_M6_F01_MAX_ATOM_BYTES_V1:
        return _reject(F01HistoryAtomCodeV1.INVALID_BYTES, "payload")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(F01HistoryAtomCodeV1.INVALID_UTF8, "payload")
    try:
        decoded = json.loads(text, object_pairs_hook=_reject_duplicate_pairs)
    except ValueError as exc:
        if "duplicate JSON field" in str(exc):
            return _reject(F01HistoryAtomCodeV1.DUPLICATE_FIELD, "payload")
        return _reject(F01HistoryAtomCodeV1.INVALID_JSON, "payload")
    if type(decoded) is not dict:
        return _reject(F01HistoryAtomCodeV1.INVALID_JSON, "payload")
    try:
        if canonical_json_bytes(decoded) != payload:
            return _reject(F01HistoryAtomCodeV1.NONCANONICAL_BYTES, "payload")
        envelope = cast(dict[str, object], decoded)
        _exact_fields(envelope, frozenset({"schema", "value"}), "envelope")
        if envelope["schema"] != FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1:
            return _reject(F01HistoryAtomCodeV1.WRONG_SCHEMA, "schema")
        return _decode_value(envelope["value"])
    except F01HistoryAtomError as exc:
        message = str(exc)
        if "unknown field" in message:
            code = F01HistoryAtomCodeV1.UNKNOWN_FIELD
        elif "missing" in message:
            code = F01HistoryAtomCodeV1.MISSING_FIELD
        else:
            code = F01HistoryAtomCodeV1.INVALID_VALUE
        return _reject(code, "value")
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(F01HistoryAtomCodeV1.INVALID_VALUE, "value")


__all__ = (
    "FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1",
    "FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1",
    "FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1",
    "FCIS_M6_F01_MAX_ATOM_BYTES_V1",
    "FCIS_M6_F01_MAX_OUTBOX_RECORDS_V1",
    "F01HistoryAtomCodeV1",
    "F01HistoryAtomDecodeResultV1",
    "F01HistoryAtomError",
    "F01HistoryAtomRejectV1",
    "F01HistoryAtomV1",
    "F01HistoryNullifierV1",
    "F01HistoryOutboxRecordV1",
    "F01ProofContextRequirementV1",
    "decode_history_atom_v1",
    "encode_history_atom_v1",
    "history_atom_root_v1",
)
