"""Total fail-closed reopen for the F02 canonical durable layout.

F03 accepts untrusted layout bytes or an exact F02 layout value and returns a
complete reconstructed F02 history or a typed rejection.  The final authority
condition is a canonical fixed point:

    encode_history(reopen(layout)) == layout

The module performs no database access and grants no post-restart runtime
authority.  It is the research reference for the later datastore adapter.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, TypeGuard, cast

from ..state.canonical import canonical_json_bytes
from .fcis_durable_retraction import MigrationPhaseV1
from .fcis_m6_e01_request_identity import E01CommandFamilyV1
from .fcis_m6_f01_history_atom import (
    FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1,
    FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1,
    F01HistoryNullifierV1,
    F01HistoryOutboxRecordV1,
)
from .fcis_m6_f02_history_encoder import (
    FCIS_M6_F02_LAYOUT_SCHEMA_V1,
    FCIS_M6_F02_MAX_ACKS_V1,
    FCIS_M6_F02_MAX_ATOMS_V1,
    FCIS_M6_F02_MAX_AUTHORITY_EPOCHS_V1,
    F02AckRowV1,
    F02AuthorityEpochV1,
    F02AuthorizedHistoryV1,
    F02DurableLayoutV1,
    F02EvidenceKindV1,
    F02EvidenceRowV1,
    F02HistoryEncoderError,
    F02HistoryRowV1,
    F02NullifierRowV1,
    F02OutboxRowV1,
    F02StateHeaderV1,
    encode_history,
    encode_layout_v1,
)

FCIS_M6_F03_REOPEN_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f03/reopen/v1"
FCIS_M6_F03_MAX_LAYOUT_BYTES_V1: Final[int] = 8 * 1024 * 1024


class F03ReopenCodeV1(Enum):
    """Stable fail-closed reopen outcomes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    RESOURCE_LIMIT = "resource_limit"
    INVALID_UTF8 = "invalid_utf8"
    INVALID_JSON = "invalid_json"
    DUPLICATE_FIELD = "duplicate_field"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    WRONG_SCHEMA = "wrong_schema"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    ROW_DECODE_REJECTED = "row_decode_rejected"
    HISTORY_REJECTED = "history_rejected"
    PROJECTION_MISMATCH = "projection_mismatch"
    FIXED_POINT_MISMATCH = "fixed_point_mismatch"


class F03ReopenError(ValueError):
    """Raised internally while reconstructing a complete history."""


@dataclass(frozen=True, slots=True)
class F03ReopenRejectV1:
    code: F03ReopenCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F03ReopenCodeV1:
            raise F03ReopenError("reopen code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F03ReopenError("reopen path must be an exact string tuple")


@dataclass(frozen=True, slots=True)
class F03ReopenSuccessV1:
    history: F02AuthorizedHistoryV1
    layout_root: str
    canonical_layout_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.history) is not F02AuthorizedHistoryV1:
            raise F03ReopenError("reopen history has the wrong exact type")
        self.history.__post_init__()
        if type(self.layout_root) is not str or len(self.layout_root) != 66:
            raise F03ReopenError("reopen layout root is malformed")
        if type(self.canonical_layout_bytes) is not bytes:
            raise F03ReopenError("reopen canonical bytes have the wrong exact type")


F03ReopenResultV1: TypeAlias = F03ReopenSuccessV1 | F03ReopenRejectV1


def _reject(code: F03ReopenCodeV1, *path: str) -> F03ReopenRejectV1:
    return F03ReopenRejectV1(code, path)


def _mapping(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        raise F03ReopenError(f"{path} must be an exact object")
    return cast(dict[str, object], value)


def _text(value: object, path: str) -> str:
    if type(value) is not str or not value:
        raise F03ReopenError(f"{path} must be nonempty text")
    return value


def _integer(value: object, path: str) -> int:
    if type(value) is not int:
        raise F03ReopenError(f"{path} must be an exact integer")
    return value


def _list(value: object, path: str, maximum: int) -> list[object]:
    if type(value) is not list:
        raise F03ReopenError(f"{path} must be an exact list")
    if len(value) > maximum:
        raise F03ReopenError(f"{path} exceeds its resource bound")
    return cast(list[object], value)


def _exact_fields(value: dict[str, object], expected: frozenset[str], path: str) -> None:
    actual = frozenset(value)
    if actual - expected:
        raise F03ReopenError(f"{path} contains an unknown field")
    if expected - actual:
        raise F03ReopenError(f"{path} is missing a required field")


def _duplicate_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def _decode_header(value: object) -> F02StateHeaderV1:
    fields = _mapping(value, "value.header")
    expected = frozenset(
        {
            "genesis_state_root",
            "current_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "current_authority_state_root",
            "current_authority_epoch_index",
            "history_count",
            "evidence_count",
            "nullifier_count",
            "outbox_count",
            "authority_count",
            "ack_count",
        }
    )
    _exact_fields(fields, expected, "value.header")
    return F02StateHeaderV1(
        genesis_state_root=_text(fields["genesis_state_root"], "header.genesis_state_root"),
        current_state_root=_text(fields["current_state_root"], "header.current_state_root"),
        deployment_config_root=_text(
            fields["deployment_config_root"], "header.deployment_config_root"
        ),
        verifier_profile_root=_text(
            fields["verifier_profile_root"], "header.verifier_profile_root"
        ),
        current_authority_state_root=_text(
            fields["current_authority_state_root"], "header.current_authority_state_root"
        ),
        current_authority_epoch_index=_integer(
            fields["current_authority_epoch_index"], "header.current_authority_epoch_index"
        ),
        history_count=_integer(fields["history_count"], "header.history_count"),
        evidence_count=_integer(fields["evidence_count"], "header.evidence_count"),
        nullifier_count=_integer(fields["nullifier_count"], "header.nullifier_count"),
        outbox_count=_integer(fields["outbox_count"], "header.outbox_count"),
        authority_count=_integer(fields["authority_count"], "header.authority_count"),
        ack_count=_integer(fields["ack_count"], "header.ack_count"),
    )


def _decode_authority(value: object, index: int) -> F02AuthorityEpochV1:
    fields = _mapping(value, f"value.authority_rows[{index}]")
    _exact_fields(
        fields,
        frozenset(
            {
                "epoch_index",
                "phase",
                "authority_state_root",
                "allowed_writer_roots",
                "transition_root",
            }
        ),
        f"authority_rows[{index}]",
    )
    phase_raw = _text(fields["phase"], f"authority_rows[{index}].phase")
    try:
        phase = MigrationPhaseV1(phase_raw)
    except ValueError as exc:
        raise F03ReopenError("authority phase is outside the closed enum") from exc
    writers_raw = fields["allowed_writer_roots"]
    if type(writers_raw) is not list:
        raise F03ReopenError("authority writers must be an exact list")
    return F02AuthorityEpochV1(
        epoch_index=_integer(fields["epoch_index"], f"authority_rows[{index}].epoch_index"),
        phase=phase,
        authority_state_root=_text(
            fields["authority_state_root"], f"authority_rows[{index}].authority_state_root"
        ),
        allowed_writer_roots=tuple(
            _text(raw, f"authority_rows[{index}].allowed_writer_roots[{writer_index}]")
            for writer_index, raw in enumerate(writers_raw)
        ),
        transition_root=_text(
            fields["transition_root"], f"authority_rows[{index}].transition_root"
        ),
    )


def _decode_history(value: object, index: int) -> F02HistoryRowV1:
    fields = _mapping(value, f"value.history_rows[{index}]")
    _exact_fields(fields, frozenset({"sequence", "atom_root", "atom_bytes_utf8"}), "history_row")
    return F02HistoryRowV1(
        sequence=_integer(fields["sequence"], f"history_rows[{index}].sequence"),
        atom_root=_text(fields["atom_root"], f"history_rows[{index}].atom_root"),
        atom_bytes_utf8=_text(fields["atom_bytes_utf8"], f"history_rows[{index}].atom_bytes_utf8"),
    )


def _decode_evidence(value: object, index: int) -> F02EvidenceRowV1:
    fields = _mapping(value, f"value.evidence_rows[{index}]")
    _exact_fields(
        fields, frozenset({"sequence", "commit_id", "kind", "value_root"}), "evidence_row"
    )
    kind_raw = _text(fields["kind"], f"evidence_rows[{index}].kind")
    try:
        kind = F02EvidenceKindV1(kind_raw)
    except ValueError as exc:
        raise F03ReopenError("evidence kind is outside the closed enum") from exc
    return F02EvidenceRowV1(
        sequence=_integer(fields["sequence"], f"evidence_rows[{index}].sequence"),
        commit_id=_text(fields["commit_id"], f"evidence_rows[{index}].commit_id"),
        kind=kind,
        value_root=_text(fields["value_root"], f"evidence_rows[{index}].value_root"),
    )


def _decode_nullifier(value: object, index: int) -> F02NullifierRowV1:
    fields = _mapping(value, f"value.nullifier_rows[{index}]")
    _exact_fields(fields, frozenset({"sequence", "commit_id", "nullifier"}), "nullifier_row")
    nested = _mapping(fields["nullifier"], f"nullifier_rows[{index}].nullifier")
    _exact_fields(
        nested,
        frozenset(
            {
                "schema",
                "deployment_config_root",
                "sender_id",
                "command_family",
                "nonce",
                "request_identity_root",
                "nullifier_root",
            }
        ),
        "nullifier",
    )
    if _text(nested["schema"], "nullifier.schema") != FCIS_M6_F01_HISTORY_NULLIFIER_SCHEMA_V1:
        raise F03ReopenError("nullifier schema is foreign")
    family_raw = _text(nested["command_family"], "nullifier.command_family")
    try:
        family = E01CommandFamilyV1(family_raw)
    except ValueError as exc:
        raise F03ReopenError("nullifier command family is outside the closed enum") from exc
    return F02NullifierRowV1(
        sequence=_integer(fields["sequence"], f"nullifier_rows[{index}].sequence"),
        commit_id=_text(fields["commit_id"], f"nullifier_rows[{index}].commit_id"),
        nullifier=F01HistoryNullifierV1(
            deployment_config_root=_text(
                nested["deployment_config_root"], "nullifier.deployment_config_root"
            ),
            sender_id=_text(nested["sender_id"], "nullifier.sender_id"),
            command_family=family,
            nonce=_integer(nested["nonce"], "nullifier.nonce"),
            request_identity_root=_text(
                nested["request_identity_root"], "nullifier.request_identity_root"
            ),
            nullifier_root=_text(nested["nullifier_root"], "nullifier.nullifier_root"),
        ),
    )


def _decode_outbox(value: object, index: int) -> F02OutboxRowV1:
    fields = _mapping(value, f"value.outbox_rows[{index}]")
    _exact_fields(fields, frozenset({"sequence", "commit_id", "record"}), "outbox_row")
    nested = _mapping(fields["record"], f"outbox_rows[{index}].record")
    _exact_fields(
        nested,
        frozenset(
            {
                "schema",
                "ordinal",
                "effect_id",
                "destination",
                "payload_root",
                "adapter_profile_root",
                "idempotency_root",
            }
        ),
        "outbox_record",
    )
    if _text(nested["schema"], "outbox.schema") != FCIS_M6_F01_HISTORY_OUTBOX_SCHEMA_V1:
        raise F03ReopenError("outbox schema is foreign")
    return F02OutboxRowV1(
        sequence=_integer(fields["sequence"], f"outbox_rows[{index}].sequence"),
        commit_id=_text(fields["commit_id"], f"outbox_rows[{index}].commit_id"),
        record=F01HistoryOutboxRecordV1(
            ordinal=_integer(nested["ordinal"], "outbox.ordinal"),
            effect_id=_text(nested["effect_id"], "outbox.effect_id"),
            destination=_text(nested["destination"], "outbox.destination"),
            payload_root=_text(nested["payload_root"], "outbox.payload_root"),
            adapter_profile_root=_text(
                nested["adapter_profile_root"], "outbox.adapter_profile_root"
            ),
            idempotency_root=_text(nested["idempotency_root"], "outbox.idempotency_root"),
        ),
    )


def _decode_ack(value: object, index: int) -> F02AckRowV1:
    fields = _mapping(value, f"value.ack_rows[{index}]")
    expected = frozenset(
        {
            "effect_id",
            "commit_id",
            "destination",
            "payload_root",
            "destination_receipt_root",
            "adapter_profile_root",
            "idempotency_root",
            "response_root",
        }
    )
    _exact_fields(fields, expected, "ack_row")
    return F02AckRowV1(
        effect_id=_text(fields["effect_id"], "ack.effect_id"),
        commit_id=_text(fields["commit_id"], "ack.commit_id"),
        destination=_text(fields["destination"], "ack.destination"),
        payload_root=_text(fields["payload_root"], "ack.payload_root"),
        destination_receipt_root=_text(
            fields["destination_receipt_root"], "ack.destination_receipt_root"
        ),
        adapter_profile_root=_text(fields["adapter_profile_root"], "ack.adapter_profile_root"),
        idempotency_root=_text(fields["idempotency_root"], "ack.idempotency_root"),
        response_root=_text(fields["response_root"], "ack.response_root"),
    )


def _decode_layout_value(value: object) -> F02DurableLayoutV1:
    fields = _mapping(value, "value")
    _exact_fields(
        fields,
        frozenset(
            {
                "header",
                "authority_rows",
                "history_rows",
                "evidence_rows",
                "nullifier_rows",
                "outbox_rows",
                "ack_rows",
                "layout_root",
            }
        ),
        "value",
    )
    authority_raw = _list(
        fields["authority_rows"], "value.authority_rows", FCIS_M6_F02_MAX_AUTHORITY_EPOCHS_V1
    )
    history_raw = _list(fields["history_rows"], "value.history_rows", FCIS_M6_F02_MAX_ATOMS_V1)
    evidence_raw = _list(
        fields["evidence_rows"], "value.evidence_rows", FCIS_M6_F02_MAX_ATOMS_V1 * 8
    )
    nullifier_raw = _list(
        fields["nullifier_rows"], "value.nullifier_rows", FCIS_M6_F02_MAX_ATOMS_V1
    )
    outbox_raw = _list(fields["outbox_rows"], "value.outbox_rows", FCIS_M6_F02_MAX_ATOMS_V1 * 4096)
    ack_raw = _list(fields["ack_rows"], "value.ack_rows", FCIS_M6_F02_MAX_ACKS_V1)
    return F02DurableLayoutV1(
        header=_decode_header(fields["header"]),
        authority_rows=tuple(_decode_authority(raw, i) for i, raw in enumerate(authority_raw)),
        history_rows=tuple(_decode_history(raw, i) for i, raw in enumerate(history_raw)),
        evidence_rows=tuple(_decode_evidence(raw, i) for i, raw in enumerate(evidence_raw)),
        nullifier_rows=tuple(_decode_nullifier(raw, i) for i, raw in enumerate(nullifier_raw)),
        outbox_rows=tuple(_decode_outbox(raw, i) for i, raw in enumerate(outbox_raw)),
        ack_rows=tuple(_decode_ack(raw, i) for i, raw in enumerate(ack_raw)),
        layout_root=_text(fields["layout_root"], "value.layout_root"),
    )


def _is_layout(value: object) -> TypeGuard[F02DurableLayoutV1]:
    return type(value) is F02DurableLayoutV1


def reopen_layout(layout: object) -> F03ReopenResultV1:
    """Reopen an exact F02 layout through a complete fixed-point check."""

    if not _is_layout(layout):
        return _reject(F03ReopenCodeV1.WRONG_EXACT_TYPE, "layout")
    exact = layout
    try:
        if len(exact.history_rows) > FCIS_M6_F02_MAX_ATOMS_V1:
            return _reject(F03ReopenCodeV1.RESOURCE_LIMIT, "history_rows")
        exact.__post_init__()
    except (AttributeError, F02HistoryEncoderError, TypeError, ValueError, ArithmeticError):
        return _reject(F03ReopenCodeV1.ROW_DECODE_REJECTED, "layout")
    try:
        atoms = tuple(row.atom for row in exact.history_rows)
        history = F02AuthorizedHistoryV1(
            genesis_state_root=exact.header.genesis_state_root,
            deployment_config_root=exact.header.deployment_config_root,
            verifier_profile_root=exact.header.verifier_profile_root,
            authority_epochs=exact.authority_rows,
            atoms=atoms,
            acks=exact.ack_rows,
        )
    except (AttributeError, F02HistoryEncoderError, TypeError, ValueError, ArithmeticError):
        return _reject(F03ReopenCodeV1.HISTORY_REJECTED, "history")
    try:
        canonical = encode_history(history)
    except (F02HistoryEncoderError, TypeError, ValueError, ArithmeticError):
        return _reject(F03ReopenCodeV1.PROJECTION_MISMATCH, "history")
    if canonical != exact:
        return _reject(F03ReopenCodeV1.FIXED_POINT_MISMATCH, "layout")
    try:
        canonical_bytes = encode_layout_v1(canonical)
    except (F02HistoryEncoderError, TypeError, ValueError, ArithmeticError):
        return _reject(F03ReopenCodeV1.PROJECTION_MISMATCH, "layout")
    return F03ReopenSuccessV1(
        history=history,
        layout_root=exact.layout_root,
        canonical_layout_bytes=canonical_bytes,
    )


def reopen_layout_bytes(payload: object) -> F03ReopenResultV1:
    """Decode canonical layout bytes and then run the complete reopen gate."""

    if type(payload) is not bytes:
        return _reject(F03ReopenCodeV1.WRONG_EXACT_TYPE, "payload")
    if len(payload) > FCIS_M6_F03_MAX_LAYOUT_BYTES_V1:
        return _reject(F03ReopenCodeV1.RESOURCE_LIMIT, "payload")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        return _reject(F03ReopenCodeV1.INVALID_UTF8, "payload")
    try:
        decoded = json.loads(text, object_pairs_hook=_duplicate_pairs)
    except ValueError as exc:
        if "duplicate JSON field" in str(exc):
            return _reject(F03ReopenCodeV1.DUPLICATE_FIELD, "payload")
        return _reject(F03ReopenCodeV1.INVALID_JSON, "payload")
    if type(decoded) is not dict:
        return _reject(F03ReopenCodeV1.INVALID_JSON, "payload")
    try:
        if canonical_json_bytes(decoded) != payload:
            return _reject(F03ReopenCodeV1.NONCANONICAL_BYTES, "payload")
        envelope = cast(dict[str, object], decoded)
        _exact_fields(envelope, frozenset({"schema", "value"}), "envelope")
        if _text(envelope["schema"], "schema") != FCIS_M6_F02_LAYOUT_SCHEMA_V1:
            return _reject(F03ReopenCodeV1.WRONG_SCHEMA, "schema")
        layout = _decode_layout_value(envelope["value"])
    except F03ReopenError as exc:
        message = str(exc)
        if "unknown field" in message:
            code = F03ReopenCodeV1.UNKNOWN_FIELD
        elif "missing" in message:
            code = F03ReopenCodeV1.MISSING_FIELD
        elif "resource" in message or "bound" in message:
            code = F03ReopenCodeV1.RESOURCE_LIMIT
        else:
            code = F03ReopenCodeV1.ROW_DECODE_REJECTED
        return _reject(code, "value")
    except (F02HistoryEncoderError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(F03ReopenCodeV1.ROW_DECODE_REJECTED, "value")
    return reopen_layout(layout)


__all__ = (
    "FCIS_M6_F03_MAX_LAYOUT_BYTES_V1",
    "FCIS_M6_F03_REOPEN_SCHEMA_V1",
    "F03ReopenCodeV1",
    "F03ReopenError",
    "F03ReopenRejectV1",
    "F03ReopenResultV1",
    "F03ReopenSuccessV1",
    "reopen_layout",
    "reopen_layout_bytes",
)
