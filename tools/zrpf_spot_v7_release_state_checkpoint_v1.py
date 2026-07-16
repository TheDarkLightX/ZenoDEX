"""Canonical authority-neutral Spot V7 release-state checkpoints.

This module binds one replayed release-store state to an append-only checkpoint
chain.  It authenticates no external consensus, release, runtime, settlement,
or production authority.  A protocol-specific finality adapter must verify the
exact checkpoint bytes before a later boundary may treat the state as anchored.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Final, NoReturn, final

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes

RELEASE_STATE_CHECKPOINT_SCHEMA_V1: Final = "zenodex.zrpf.spot_v7.release_state_checkpoint.v1"
ZERO_DIGEST_HEX_V1: Final = "00" * 32
MAX_RELEASE_STATE_CHECKPOINT_BYTES_V1: Final = 16 * 1_024
MAX_RELEASE_STATE_CHECKPOINT_DEPTH_V1: Final = 2
MAX_U64_V1: Final = (1 << 64) - 1

_CHECKPOINT_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_release_state_checkpoint",
    version=1,
)
_DIGEST_RE: Final = re.compile(r"^[0-9a-f]{64}$")
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_FIELDS_V1: Final = frozenset(
    {
        "application_id",
        "chain_id",
        "current_candidate_id",
        "current_candidate_sha256",
        "current_release_revision",
        "current_revocation_record_id",
        "current_select_input_id",
        "database_revision",
        "domain_id",
        "last_evaluation_epoch",
        "parent_release_checkpoint_hash",
        "release_checkpoint_hash",
        "release_checkpoint_sequence",
        "release_profile",
        "release_state_root",
        "schema",
        "store_identity_hash",
    }
)


class SpotV7ReleaseStateCheckpointRejectV1(ValueError):
    """Stable fail-closed error at the release-checkpoint boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7ReleaseStateCheckpointRejectV1:
    return SpotV7ReleaseStateCheckpointRejectV1(code, detail)


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseStateCheckpointV1:
    """Canonical local checkpoint carrying no external or operational authority."""

    canonical_bytes: bytes
    schema: str
    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    store_identity_hash: str
    database_revision: int
    last_evaluation_epoch: int
    release_state_root: str
    current_candidate_id: str | None
    current_candidate_sha256: str | None
    current_release_revision: int | None
    current_select_input_id: str | None
    current_revocation_record_id: str | None
    parent_release_checkpoint_hash: str
    release_checkpoint_sequence: int
    release_checkpoint_hash: str

    @property
    def external_finality_authenticated(self) -> bool:
        return False

    @property
    def external_monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def is_genesis(self) -> bool:
        return self.release_checkpoint_sequence == 0

    @property
    def is_revoked(self) -> bool:
        return self.current_revocation_record_id is not None


def build_spot_v7_release_state_checkpoint_v1(
    *,
    application_id: str,
    chain_id: str,
    domain_id: str,
    release_profile: str,
    store_identity_hash: str,
    database_revision: int,
    last_evaluation_epoch: int,
    release_state_root: str,
    current_candidate_id: str | None,
    current_candidate_sha256: str | None,
    current_release_revision: int | None,
    current_select_input_id: str | None,
    current_revocation_record_id: str | None,
    parent_release_checkpoint_hash: str,
    release_checkpoint_sequence: int,
) -> bytes:
    """Build the only accepted bytes for one authority-neutral checkpoint."""

    body: dict[str, object] = {
        "application_id": _require_token(application_id, name="application_id"),
        "chain_id": _require_token(chain_id, name="chain_id"),
        "current_candidate_id": _require_optional_digest(
            current_candidate_id,
            name="current_candidate_id",
        ),
        "current_candidate_sha256": _require_optional_digest(
            current_candidate_sha256,
            name="current_candidate_sha256",
        ),
        "current_release_revision": _require_optional_positive_u64(
            current_release_revision,
            name="current_release_revision",
        ),
        "current_revocation_record_id": _require_optional_digest(
            current_revocation_record_id,
            name="current_revocation_record_id",
        ),
        "current_select_input_id": _require_optional_digest(
            current_select_input_id,
            name="current_select_input_id",
        ),
        "database_revision": _require_u64(database_revision, name="database_revision"),
        "domain_id": _require_token(domain_id, name="domain_id"),
        "last_evaluation_epoch": _require_u64(
            last_evaluation_epoch,
            name="last_evaluation_epoch",
        ),
        "parent_release_checkpoint_hash": _require_digest_allow_zero(
            parent_release_checkpoint_hash,
            name="parent_release_checkpoint_hash",
        ),
        "release_checkpoint_sequence": _require_u64(
            release_checkpoint_sequence,
            name="release_checkpoint_sequence",
        ),
        "release_profile": _require_token(release_profile, name="release_profile"),
        "release_state_root": _require_digest(release_state_root, name="release_state_root"),
        "schema": RELEASE_STATE_CHECKPOINT_SCHEMA_V1,
        "store_identity_hash": _require_digest(
            store_identity_hash,
            name="store_identity_hash",
        ),
    }
    _validate_state_shape(body)
    document = dict(body)
    document["release_checkpoint_hash"] = _checkpoint_hash(body)
    raw = canonical_json_bytes(document) + b"\n"
    if len(raw) > MAX_RELEASE_STATE_CHECKPOINT_BYTES_V1:
        raise _reject("CHECKPOINT_SIZE", "release-state checkpoint is oversized")
    return raw


def parse_exact_spot_v7_release_state_checkpoint_v1(
    raw: bytes,
) -> SpotV7ReleaseStateCheckpointV1:
    """Parse canonical bytes and rederive every local checkpoint invariant."""

    document = _decode_exact_document(raw)
    body = {key: value for key, value in document.items() if key != "release_checkpoint_hash"}
    _validate_state_shape(body)
    expected_hash = _checkpoint_hash(body)
    actual_hash = _require_digest(
        document["release_checkpoint_hash"],
        name="release_checkpoint_hash",
    )
    if actual_hash != expected_hash:
        raise _reject("CHECKPOINT_HASH_MISMATCH", "release checkpoint hash does not match bytes")
    return SpotV7ReleaseStateCheckpointV1(
        canonical_bytes=raw,
        schema=RELEASE_STATE_CHECKPOINT_SCHEMA_V1,
        application_id=_require_token(document["application_id"], name="application_id"),
        chain_id=_require_token(document["chain_id"], name="chain_id"),
        domain_id=_require_token(document["domain_id"], name="domain_id"),
        release_profile=_require_token(document["release_profile"], name="release_profile"),
        store_identity_hash=_require_digest(
            document["store_identity_hash"],
            name="store_identity_hash",
        ),
        database_revision=_require_u64(document["database_revision"], name="database_revision"),
        last_evaluation_epoch=_require_u64(
            document["last_evaluation_epoch"],
            name="last_evaluation_epoch",
        ),
        release_state_root=_require_digest(
            document["release_state_root"],
            name="release_state_root",
        ),
        current_candidate_id=_require_optional_digest(
            document["current_candidate_id"],
            name="current_candidate_id",
        ),
        current_candidate_sha256=_require_optional_digest(
            document["current_candidate_sha256"],
            name="current_candidate_sha256",
        ),
        current_release_revision=_require_optional_positive_u64(
            document["current_release_revision"],
            name="current_release_revision",
        ),
        current_select_input_id=_require_optional_digest(
            document["current_select_input_id"],
            name="current_select_input_id",
        ),
        current_revocation_record_id=_require_optional_digest(
            document["current_revocation_record_id"],
            name="current_revocation_record_id",
        ),
        parent_release_checkpoint_hash=_require_digest_allow_zero(
            document["parent_release_checkpoint_hash"],
            name="parent_release_checkpoint_hash",
        ),
        release_checkpoint_sequence=_require_u64(
            document["release_checkpoint_sequence"],
            name="release_checkpoint_sequence",
        ),
        release_checkpoint_hash=actual_hash,
    )


def validate_spot_v7_release_state_checkpoint_successor_v1(
    parent: SpotV7ReleaseStateCheckpointV1,
    child: SpotV7ReleaseStateCheckpointV1,
) -> SpotV7ReleaseStateCheckpointV1:
    """Validate one exact adjacent transition in the release checkpoint chain."""

    parent = _reparse_exact_checkpoint(parent, name="parent")
    child = _reparse_exact_checkpoint(child, name="child")
    if parent.is_revoked:
        raise _reject("REVOKED_STATE_TERMINAL", "a revoked release checkpoint has no successor")
    for field in (
        "application_id",
        "chain_id",
        "domain_id",
        "release_profile",
        "store_identity_hash",
    ):
        if getattr(parent, field) != getattr(child, field):
            raise _reject("CHECKPOINT_SCOPE_MISMATCH", f"successor changes {field}")
    if parent.release_checkpoint_sequence == MAX_U64_V1:
        raise _reject("CHECKPOINT_SEQUENCE_EXHAUSTED", "checkpoint sequence cannot advance")
    if child.release_checkpoint_sequence != parent.release_checkpoint_sequence + 1:
        raise _reject("CHECKPOINT_SEQUENCE_GAP", "checkpoint sequence must advance exactly once")
    if parent.database_revision == MAX_U64_V1:
        raise _reject("DATABASE_REVISION_EXHAUSTED", "database revision cannot advance")
    if child.database_revision != parent.database_revision + 1:
        raise _reject("DATABASE_REVISION_GAP", "database revision must advance exactly once")
    if child.parent_release_checkpoint_hash != parent.release_checkpoint_hash:
        raise _reject("CHECKPOINT_PARENT_MISMATCH", "successor does not bind the exact parent")
    if child.last_evaluation_epoch < parent.last_evaluation_epoch:
        raise _reject("EVALUATION_EPOCH_REGRESSION", "evaluation epoch cannot regress")
    if child.release_state_root == parent.release_state_root:
        raise _reject("RELEASE_STATE_UNCHANGED", "successor must bind a new release state root")
    if parent.is_genesis:
        _validate_genesis_successor(child)
    elif child.is_revoked:
        _validate_revocation_successor(parent, child)
    else:
        _validate_selection_successor(parent, child)
    return child


def _validate_genesis_successor(child: SpotV7ReleaseStateCheckpointV1) -> None:
    if child.is_revoked:
        raise _reject("GENESIS_REVOCATION_FORBIDDEN", "genesis must first advance by selection")
    if child.current_release_revision != 1:
        raise _reject("INITIAL_RELEASE_REVISION", "first selected release revision must be one")


def _validate_revocation_successor(
    parent: SpotV7ReleaseStateCheckpointV1,
    child: SpotV7ReleaseStateCheckpointV1,
) -> None:
    preserved = (
        "current_candidate_id",
        "current_candidate_sha256",
        "current_release_revision",
        "current_select_input_id",
    )
    for field in preserved:
        if getattr(parent, field) != getattr(child, field):
            raise _reject("REVOCATION_LINEAGE_MISMATCH", f"revocation changes {field}")


def _validate_selection_successor(
    parent: SpotV7ReleaseStateCheckpointV1,
    child: SpotV7ReleaseStateCheckpointV1,
) -> None:
    parent_revision = parent.current_release_revision
    child_revision = child.current_release_revision
    if parent_revision is None or child_revision != parent_revision + 1:
        raise _reject("RELEASE_REVISION_GAP", "release revision must advance exactly once")
    if child.current_candidate_id == parent.current_candidate_id:
        raise _reject("CANDIDATE_REUSE", "successor must select a new candidate")
    if child.current_select_input_id == parent.current_select_input_id:
        raise _reject("SELECT_INPUT_REUSE", "successor must consume a new SELECT input")


def _reparse_exact_checkpoint(
    value: object,
    *,
    name: str,
) -> SpotV7ReleaseStateCheckpointV1:
    if type(value) is not SpotV7ReleaseStateCheckpointV1:
        raise _reject("CHECKPOINT_TYPE", f"{name} must be an exact checkpoint value")
    reparsed = parse_exact_spot_v7_release_state_checkpoint_v1(value.canonical_bytes)
    if reparsed != value:
        raise _reject("CHECKPOINT_VALUE_MISMATCH", f"{name} fields do not match canonical bytes")
    return value


def _decode_exact_document(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes:
        raise _reject("CHECKPOINT_TYPE", "release-state checkpoint must be exact bytes")
    if not raw or len(raw) > MAX_RELEASE_STATE_CHECKPOINT_BYTES_V1:
        raise _reject("CHECKPOINT_SIZE", "release-state checkpoint is empty or oversized")
    _require_bounded_json_depth(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "release-state checkpoint must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7ReleaseStateCheckpointRejectV1:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "release-state checkpoint is invalid JSON") from exc
    if type(value) is not dict or frozenset(value) != _FIELDS_V1:
        actual = frozenset(value) if type(value) is dict else frozenset()
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"checkpoint missing={sorted(_FIELDS_V1 - actual)} extra={sorted(actual - _FIELDS_V1)}",
        )
    if value["schema"] != RELEASE_STATE_CHECKPOINT_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "release-state checkpoint schema is unsupported")
    if canonical_json_bytes(value) + b"\n" != raw:
        raise _reject("NONCANONICAL_JSON", "release-state checkpoint is not canonical JSON")
    return value


def _validate_state_shape(document: dict[str, object]) -> None:
    sequence = _require_u64(
        document["release_checkpoint_sequence"],
        name="release_checkpoint_sequence",
    )
    revision = _require_u64(document["database_revision"], name="database_revision")
    epoch = _require_u64(document["last_evaluation_epoch"], name="last_evaluation_epoch")
    parent_hash = _require_digest_allow_zero(
        document["parent_release_checkpoint_hash"],
        name="parent_release_checkpoint_hash",
    )
    candidate_id = _require_optional_digest(
        document["current_candidate_id"],
        name="current_candidate_id",
    )
    candidate_sha256 = _require_optional_digest(
        document["current_candidate_sha256"],
        name="current_candidate_sha256",
    )
    release_revision = _require_optional_positive_u64(
        document["current_release_revision"],
        name="current_release_revision",
    )
    select_input_id = _require_optional_digest(
        document["current_select_input_id"],
        name="current_select_input_id",
    )
    revocation_id = _require_optional_digest(
        document["current_revocation_record_id"],
        name="current_revocation_record_id",
    )
    _require_digest(document["release_state_root"], name="release_state_root")
    _require_digest(document["store_identity_hash"], name="store_identity_hash")
    _require_token(document["application_id"], name="application_id")
    _require_token(document["chain_id"], name="chain_id")
    _require_token(document["domain_id"], name="domain_id")
    _require_token(document["release_profile"], name="release_profile")
    if sequence != revision:
        raise _reject(
            "CHECKPOINT_REVISION_MISMATCH",
            "one checkpoint is required for every authenticated release-state revision",
        )
    current = (candidate_id, candidate_sha256, release_revision, select_input_id)
    if sequence == 0:
        if revision != 0 or epoch != 0 or parent_hash != ZERO_DIGEST_HEX_V1:
            raise _reject("GENESIS_FRAMING", "genesis revision, epoch, and parent must be zero")
        if any(value is not None for value in (*current, revocation_id)):
            raise _reject("GENESIS_STATE", "genesis cannot contain selected or revoked state")
        return
    if revision == 0 or parent_hash == ZERO_DIGEST_HEX_V1:
        raise _reject("SUCCESSOR_FRAMING", "non-genesis revision and parent must be nonzero")
    if any(value is None for value in current):
        raise _reject("CURRENT_RELEASE_INCOMPLETE", "non-genesis current release is incomplete")


def _checkpoint_hash(body: dict[str, object]) -> str:
    encoded = canonical_json_bytes(body)
    return hashlib.sha256(_CHECKPOINT_HASH_DOMAIN_V1 + encode_bytes(encoded)).hexdigest()


def _require_bounded_json_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in {0x5B, 0x7B}:
            depth += 1
            if depth > MAX_RELEASE_STATE_CHECKPOINT_DEPTH_V1:
                raise _reject("JSON_DEPTH", "release-state checkpoint is too deeply nested")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise _reject("INVALID_JSON", "release-state checkpoint has invalid framing")
    if depth != 0 or in_string or escaped:
        raise _reject("INVALID_JSON", "release-state checkpoint has invalid framing")


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V1:
        raise _reject("U64_REQUIRED", f"{name} must be a u64")
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    output = _require_u64(value, name=name)
    if output == 0:
        raise _reject("POSITIVE_U64_REQUIRED", f"{name} must be positive")
    return output


def _require_optional_positive_u64(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_positive_u64(value, name=name)


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise _reject("TOKEN_REQUIRED", f"{name} must be a bounded ASCII token")
    return value


def _require_digest(value: object, *, name: str) -> str:
    output = _require_digest_allow_zero(value, name=name)
    if output == ZERO_DIGEST_HEX_V1:
        raise _reject("NONZERO_DIGEST_REQUIRED", f"{name} must be nonzero")
    return output


def _require_digest_allow_zero(value: object, *, name: str) -> str:
    if type(value) is not str or _DIGEST_RE.fullmatch(value) is None:
        raise _reject("DIGEST_REQUIRED", f"{name} must be canonical lowercase hex")
    return value


def _require_optional_digest(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_digest(value, name=name)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise _reject("DUPLICATE_JSON_KEY", "release-state checkpoint has a duplicate key")
        output[key] = value
    return output


def _reject_float(value: str) -> NoReturn:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> NoReturn:
    raise _reject("NONFINITE_FORBIDDEN", value)


__all__ = [
    "MAX_RELEASE_STATE_CHECKPOINT_BYTES_V1",
    "RELEASE_STATE_CHECKPOINT_SCHEMA_V1",
    "ZERO_DIGEST_HEX_V1",
    "SpotV7ReleaseStateCheckpointRejectV1",
    "SpotV7ReleaseStateCheckpointV1",
    "build_spot_v7_release_state_checkpoint_v1",
    "parse_exact_spot_v7_release_state_checkpoint_v1",
    "validate_spot_v7_release_state_checkpoint_successor_v1",
]
