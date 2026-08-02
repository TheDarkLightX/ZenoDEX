"""Canonical length-framed proof-context codec for the G02 research lane."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import domain_sep_bytes, sha256_hex
from .fcis_m6_g01_proof_context import (
    G01ProofContextError,
    G01ProofContextV1,
    build_g01_proof_context_v1,
)

FCIS_M6_G02_PROOF_CONTEXT_CODEC_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/g02/proof-context-codec/v1"
FCIS_M6_G02_MAX_CODEC_BYTES_V1: Final[int] = 64 * 1024
_MAGIC: Final[bytes] = b"FCIS-M6-G02\x01"
_CODEC_ROOT_DOMAIN: Final[str] = "zenodex/fcis/m6/g02/proof-context-codec"

_FIELD_SPECS: Final[tuple[tuple[str, bytes], ...]] = (
    ("chain_id", b"T"),
    ("deployment_id", b"T"),
    ("state_root", b"R"),
    ("configuration_root", b"R"),
    ("protocol_version", b"T"),
    ("language_runtime_version", b"T"),
    ("verifier_implementation_id", b"T"),
    ("verification_key_digest", b"R"),
    ("statement_schema_id", b"T"),
    ("algorithm_profile_id", b"T"),
    ("history_genesis_authority_root", b"R"),
    ("authority_epoch", b"U"),
    ("not_before_epoch", b"U"),
    ("expires_at_epoch", b"O"),
    ("context_root", b"R"),
)
_FIELD_NAMES: Final[frozenset[str]] = frozenset(name for name, _ in _FIELD_SPECS)


class G02ProofContextCodeV1(Enum):
    """Stable typed G02 codec outcomes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    RESOURCE_LIMIT = "resource_limit"
    INVALID_HEADER = "invalid_header"
    WRONG_VERSION = "wrong_version"
    INVALID_FIELD_COUNT = "invalid_field_count"
    INVALID_FRAME = "invalid_frame"
    UNKNOWN_FIELD = "unknown_field"
    DUPLICATE_FIELD = "duplicate_field"
    NONCANONICAL_ORDER = "noncanonical_order"
    WRONG_FIELD_TYPE = "wrong_field_type"
    INVALID_FIELD_VALUE = "invalid_field_value"
    CONTEXT_REJECTED = "context_rejected"
    CODEC_ROOT_MISMATCH = "codec_root_mismatch"


class G02ProofContextError(ValueError):
    """Internal G02 codec failure."""


@dataclass(frozen=True, slots=True)
class G02ProofContextRejectV1:
    code: G02ProofContextCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not G02ProofContextCodeV1:
            raise G02ProofContextError("G02 code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise G02ProofContextError("G02 path must be an exact string tuple")


@dataclass(frozen=True, slots=True)
class G02ProofContextSuccessV1:
    context: G01ProofContextV1
    canonical_bytes: bytes
    codec_root: str

    def __post_init__(self) -> None:
        if type(self.context) is not G01ProofContextV1:
            raise G02ProofContextError("G02 context has the wrong exact type")
        if type(self.canonical_bytes) is not bytes:
            raise G02ProofContextError("G02 bytes have the wrong exact type")
        if type(self.codec_root) is not str or len(self.codec_root) != 66:
            raise G02ProofContextError("G02 codec root is malformed")
        self.context.__post_init__()
        if encode_g02_proof_context_v1(self.context) != self.canonical_bytes:
            raise G02ProofContextError("G02 bytes are not canonical")
        if derive_g02_codec_root_v1(self.canonical_bytes) != self.codec_root:
            raise G02ProofContextError("G02 codec root does not rederive")


G02ProofContextResultV1: TypeAlias = G02ProofContextSuccessV1 | G02ProofContextRejectV1


def _frame(value: bytes) -> bytes:
    if len(value) >= 1 << 32:
        raise G02ProofContextError("frame exceeds u32 length")
    return len(value).to_bytes(4, "big") + value


def _field_bytes(context: G01ProofContextV1, name: str, tag: bytes) -> bytes:
    raw = object.__getattribute__(context, name)
    if tag in (b"T", b"R"):
        if type(raw) is not str:
            raise G02ProofContextError(f"{name} is not text")
        return raw.encode("utf-8")
    if tag == b"U":
        if type(raw) is not int:
            raise G02ProofContextError(f"{name} is not an integer")
        return raw.to_bytes(8, "big")
    if tag == b"O":
        if raw is None:
            return b"\x00"
        if type(raw) is not int:
            raise G02ProofContextError(f"{name} is not an optional epoch")
        return b"\x01" + raw.to_bytes(8, "big")
    raise G02ProofContextError(f"{name} has an unsupported field tag")


def encode_g02_proof_context_v1(context: object) -> bytes:
    """Encode one exact G01 value in fixed field order and length frames."""

    if type(context) is not G01ProofContextV1:
        raise G02ProofContextError("G02 encoder requires an exact G01 context")
    value = cast(G01ProofContextV1, context)
    value.__post_init__()
    output = bytearray(_MAGIC)
    output.extend(len(_FIELD_SPECS).to_bytes(2, "big"))
    for name, tag in _FIELD_SPECS:
        output.extend(_frame(name.encode("ascii")))
        output.extend(tag)
        output.extend(_frame(_field_bytes(value, name, tag)))
    encoded = bytes(output)
    if len(encoded) > FCIS_M6_G02_MAX_CODEC_BYTES_V1:
        raise G02ProofContextError("G02 codec bytes exceed their bound")
    return encoded


def derive_g02_codec_root_v1(canonical_bytes: bytes) -> str:
    """Derive a length-framed identity for the canonical G02 bytes."""

    if type(canonical_bytes) is not bytes:
        raise G02ProofContextError("G02 codec root requires exact bytes")
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes(_CODEC_ROOT_DOMAIN, version=1)
            + len(canonical_bytes).to_bytes(8, "big")
            + canonical_bytes
        ),
    )


def _take_frame(payload: bytes, offset: int, name: str) -> tuple[bytes, int]:
    if offset + 4 > len(payload):
        raise G02ProofContextError(f"{name} frame length is truncated")
    size = int.from_bytes(payload[offset : offset + 4], "big")
    start = offset + 4
    end = start + size
    if end > len(payload):
        raise G02ProofContextError(f"{name} frame value is truncated")
    return payload[start:end], end


def _decode_text(raw: bytes, name: str) -> str:
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise G02ProofContextError(f"{name} is not UTF-8") from exc


def _decode_field(raw: bytes, tag: bytes, name: str) -> object:
    if tag in (b"T", b"R"):
        return _decode_text(raw, name)
    if tag == b"U":
        if len(raw) != 8:
            raise G02ProofContextError(f"{name} is not an exact u64 frame")
        return int.from_bytes(raw, "big")
    if tag == b"O":
        if raw == b"\x00":
            return None
        if len(raw) != 9 or raw[0] != 1:
            raise G02ProofContextError(f"{name} is not an exact optional u64 frame")
        return int.from_bytes(raw[1:], "big")
    raise G02ProofContextError(f"{name} has an unknown field tag")


def _reject(code: G02ProofContextCodeV1, *path: str) -> G02ProofContextRejectV1:
    return G02ProofContextRejectV1(code=code, path=path)


def decode_g02_proof_context_v1(payload: object) -> G02ProofContextResultV1:
    """Decode only the exact canonical G02 byte sequence."""

    if type(payload) is not bytes:
        return _reject(G02ProofContextCodeV1.WRONG_EXACT_TYPE, "payload")
    if len(payload) > FCIS_M6_G02_MAX_CODEC_BYTES_V1:
        return _reject(G02ProofContextCodeV1.RESOURCE_LIMIT, "payload")
    if len(payload) < len(_MAGIC) + 2:
        return _reject(G02ProofContextCodeV1.INVALID_HEADER, "payload")
    if payload[: len(_MAGIC) - 1] != _MAGIC[: len(_MAGIC) - 1]:
        return _reject(G02ProofContextCodeV1.INVALID_HEADER, "header")
    if payload[len(_MAGIC) - 1] != _MAGIC[-1]:
        return _reject(G02ProofContextCodeV1.WRONG_VERSION, "header")
    offset = len(_MAGIC)
    field_count = int.from_bytes(payload[offset : offset + 2], "big")
    offset += 2
    if field_count != len(_FIELD_SPECS):
        return _reject(G02ProofContextCodeV1.INVALID_FIELD_COUNT, "fields")
    values: dict[str, object] = {}
    try:
        for index, (expected_name, expected_tag) in enumerate(_FIELD_SPECS):
            raw_name, offset = _take_frame(payload, offset, f"field[{index}].name")
            name = _decode_text(raw_name, f"field[{index}].name")
            if name in values:
                return _reject(G02ProofContextCodeV1.DUPLICATE_FIELD, name)
            if name not in _FIELD_NAMES:
                return _reject(G02ProofContextCodeV1.UNKNOWN_FIELD, name)
            if name != expected_name:
                return _reject(G02ProofContextCodeV1.NONCANONICAL_ORDER, name)
            if offset >= len(payload):
                raise G02ProofContextError(f"field[{index}] tag is truncated")
            tag = payload[offset : offset + 1]
            offset += 1
            if tag != expected_tag:
                return _reject(G02ProofContextCodeV1.WRONG_FIELD_TYPE, name)
            raw_value, offset = _take_frame(payload, offset, f"{name}.value")
            values[name] = _decode_field(raw_value, tag, name)
        if offset != len(payload):
            return _reject(G02ProofContextCodeV1.INVALID_FRAME, "trailing")
        context = build_g01_proof_context_v1(
            chain_id=cast(str, values["chain_id"]),
            deployment_id=cast(str, values["deployment_id"]),
            state_root=cast(str, values["state_root"]),
            configuration_root=cast(str, values["configuration_root"]),
            protocol_version=cast(str, values["protocol_version"]),
            language_runtime_version=cast(str, values["language_runtime_version"]),
            verifier_implementation_id=cast(str, values["verifier_implementation_id"]),
            verification_key_digest=cast(str, values["verification_key_digest"]),
            statement_schema_id=cast(str, values["statement_schema_id"]),
            algorithm_profile_id=cast(str, values["algorithm_profile_id"]),
            history_genesis_authority_root=cast(str, values["history_genesis_authority_root"]),
            authority_epoch=cast(int, values["authority_epoch"]),
            not_before_epoch=cast(int, values["not_before_epoch"]),
            expires_at_epoch=cast(int | None, values["expires_at_epoch"]),
        )
        if context.context_root != values["context_root"]:
            return _reject(G02ProofContextCodeV1.CONTEXT_REJECTED, "context_root")
        context.__post_init__()
    except G01ProofContextError:
        return _reject(G02ProofContextCodeV1.CONTEXT_REJECTED, "context")
    except (G02ProofContextError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(G02ProofContextCodeV1.INVALID_FIELD_VALUE, "fields")
    canonical_bytes = payload
    try:
        codec_root = derive_g02_codec_root_v1(canonical_bytes)
    except (G02ProofContextError, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(G02ProofContextCodeV1.CODEC_ROOT_MISMATCH, "payload")
    return G02ProofContextSuccessV1(
        context=context,
        canonical_bytes=canonical_bytes,
        codec_root=codec_root,
    )


__all__ = (
    "FCIS_M6_G02_MAX_CODEC_BYTES_V1",
    "FCIS_M6_G02_PROOF_CONTEXT_CODEC_SCHEMA_V1",
    "G02ProofContextCodeV1",
    "G02ProofContextError",
    "G02ProofContextRejectV1",
    "G02ProofContextResultV1",
    "G02ProofContextSuccessV1",
    "decode_g02_proof_context_v1",
    "derive_g02_codec_root_v1",
    "encode_g02_proof_context_v1",
)
