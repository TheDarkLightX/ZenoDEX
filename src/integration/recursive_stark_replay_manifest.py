"""Fail-closed local replay bundles for recursive STARK evidence.

This module records artifact-pinned local evidence. It does not promote proofs,
authorize settlement, or establish a reproducible build claim.
"""

from __future__ import annotations

import base64
import binascii
import hashlib
import json
import os
import re
import shutil
import stat
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, BinaryIO

from src.integration.recursive_stark_verifier_adapter import (
    parse_authenticated_recursive_facts,
)
from src.state.canonical import canonical_json_bytes

MANIFEST_SCHEMA_V1 = "zenodex/risc0_recursive_local_replay_bundle/v1"
CHECK_REPORT_SCHEMA_V1 = "zenodex/risc0_recursive_local_replay_bundle_check/v1"
BUILD_REPORT_SCHEMA_V1 = "zenodex/risc0_recursive_local_replay_bundle_build/v1"
ARTIFACT_EXPORT_SCHEMA_V1 = "zenodex/risc0_recursive_embedded_artifacts/v1"
STATUS_V1 = "local_artifact_pinned_replay"
SDK_VERSION_V1 = "3.0.5"
MANIFEST_FILENAME_V1 = "manifest.json"
MANIFEST_HASH_DOMAIN_V1 = b"zenodex:risc0-recursive-local-replay-manifest:v1\x00"
SOURCE_ROOT_DOMAIN_V1 = b"zenodex:risc0-recursive-local-replay-source-root:v1\x00"
INVALIDATED_EVIDENCE_VERSIONS_V1 = ("1.2.6",)
NON_CLAIMS_V1 = (
    "does_not_claim_reproducible_build",
    "does_not_claim_independent_rebuild_equality",
    "does_not_claim_source_or_builder_authenticity",
    "does_not_claim_complete_source_closure",
    "does_not_bind_proof_lock_roots_to_bundled_files",
    "does_not_cryptographically_reverify_proof_artifacts",
    "does_not_authenticate_verifier_stdout_provenance",
    "does_not_claim_production_readiness",
    "does_not_claim_public_replay",
    "does_not_authorize_recursive_proofs_for_settlement",
    "does_not_revive_risc0_1_2_6_evidence",
)

EXPECTED_METHOD_ARTIFACTS_V1 = {
    "aggregate": "aggregate.bin",
    "guest": "guest.bin",
    "perps_np_leaf": "perps_np_leaf.bin",
    "spot_leaf": "spot_leaf.bin",
    "summary_leaf": "summary_leaf.bin",
    "zusd_leaf": "zusd_leaf.bin",
}
EXPECTED_METHOD_NAMES_V1 = tuple(EXPECTED_METHOD_ARTIFACTS_V1)

MAX_MANIFEST_BYTES = 4 * 1024 * 1024
MAX_JSON_ARTIFACT_BYTES = 32 * 1024 * 1024
MAX_METHOD_ARTIFACT_BYTES = 64 * 1024 * 1024
MAX_SOURCE_ARTIFACT_BYTES = 64 * 1024 * 1024
MAX_TOOLCHAIN_ARTIFACT_BYTES = 384 * 1024 * 1024
MAX_RECEIPT_BYTES = 16 * 1024 * 1024
MAX_REPLAY_TRANSCRIPTS = 16
MAX_TOTAL_ARTIFACT_BYTES = 512 * 1024 * 1024
MAX_ARTIFACT_COUNT = 512
MAX_JSON_DEPTH = 64
MAX_JSON_ITEMS = 200_000
MAX_INPUT_NAME_BYTES = 128
MAX_ARTIFACT_ROLE_BYTES = 160

SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
INPUT_NAME_RE = re.compile(r"^[a-z][a-z0-9_.-]{0,127}$")
IMAGE_ID_RE = re.compile(r"^[0-9a-f]{64}$")

MANIFEST_KEYS_V1 = frozenset(
    {
        "artifact_count",
        "artifact_export",
        "artifacts",
        "invalidated_evidence_versions",
        "manifest_hash",
        "non_claims",
        "production_ready",
        "public_claim_allowed",
        "reproducible_build_claim",
        "schema",
        "source_root",
        "source_rows",
        "status",
        "total_size_bytes",
    }
)
ARTIFACT_KEYS_V1 = frozenset({"kind", "path", "role", "sha256", "size_bytes"})
SOURCE_ROW_KEYS_V1 = frozenset({"path", "role", "sha256", "size_bytes"})
ARTIFACT_EXPORT_REF_KEYS_V1 = frozenset(
    {"method_names", "report_role", "schema", "sdk_version"}
)
EXPORT_REPORT_KEYS_V1 = frozenset({"method_count", "methods", "schema", "sdk_version"})
EXPORT_METHOD_KEYS_V1 = frozenset(
    {
        "artifact",
        "generated_image_id_words",
        "image_id",
        "name",
        "program_bytes",
        "program_format",
        "program_sha256",
    }
)

KIND_DIRECTORY_V1 = {
    "artifact_export": "artifact_export",
    "method": "methods",
    "proof": "proof",
    "request": "request",
    "source": "source",
    "toolchain": "toolchain",
    "verification": "verification",
}
KIND_MAX_BYTES_V1 = {
    "artifact_export": MAX_JSON_ARTIFACT_BYTES,
    "method": MAX_METHOD_ARTIFACT_BYTES,
    "proof": MAX_JSON_ARTIFACT_BYTES,
    "request": MAX_JSON_ARTIFACT_BYTES,
    "source": MAX_SOURCE_ARTIFACT_BYTES,
    "toolchain": MAX_TOOLCHAIN_ARTIFACT_BYTES,
    "verification": MAX_JSON_ARTIFACT_BYTES,
}
MAX_INVENTORY_ENTRIES = MAX_ARTIFACT_COUNT + len(set(KIND_DIRECTORY_V1.values())) + 1
REQUIRED_NAMED_KINDS_V1 = ("source", "toolchain", "proof", "request", "verification")
CANONICAL_JSON_KINDS_V1 = frozenset({"artifact_export", "proof", "request", "verification"})

ROOT_PROOF_TYPE_V1 = "risc0.zenodex_recursive_epoch.v1"
ROOT_DOMAIN_SEPARATOR_V1 = "zenodex.risc0.recursive_epoch.v1"
ROOT_PROOF_PROFILE_V1 = "recursive_epoch_v1"
RECEIPT_CODEC_V1 = "risc0_receipt_canonical_serde_json_depth128_v1"
RECURSIVE_PROOF_TYPES_V1 = frozenset(
    {
        ROOT_PROOF_TYPE_V1,
        "risc0.zenodex_recursive_summary_leaf.v1",
        "risc0.zenodex_recursive_spot_leaf.v1",
        "risc0.zenodex_recursive_perps_np_leaf.v1",
        "risc0.zenodex_recursive_zusd_leaf.v1",
    }
)
PROOF_KEYS_V1 = frozenset(
    {"schema", "schema_version", "state_hash", "proof_type", "proof", "meta"}
)
VERIFY_REQUEST_KEYS_V1 = frozenset(
    {
        "schema",
        "schema_version",
        "state_hash",
        "proof",
        "recursive_input",
        "recursive_expectations",
    }
)
RECURSIVE_EXPECTATION_KEYS_V1 = frozenset(
    {
        "risc0_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_hashfn",
        "receipt_verifier_parameters",
        "receipt_control_id",
        "journal_version",
        "proof_type",
        "domain_separator",
        "chain_id",
        "epoch_id",
        "proof_profile",
        "statement_hash",
        "verifier_set_root",
        "allowed_authority_roots_root",
        "child_verification_claims_root",
        "child_journals_root",
        "child_effect_summaries_root",
        "child_count",
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "receipt_root",
        "accepted_receipts_root",
        "rejected_receipts_root",
        "aggregate_asset_delta_root",
        "cross_shard_outbox_root",
        "cross_shard_inbox_root",
        "cross_shard_message_ids_root",
        "carry_queue_pre_root",
        "carry_queue_post_root",
        "conflict_schedule_hash",
        "data_availability_root",
        "public_policy_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
        "toolchain_lock_hash",
    }
)
ROOT_PROOF_META_KEYS_V1 = RECURSIVE_EXPECTATION_KEYS_V1 - {"journal_version"}
ROOT_HASH_META_KEYS_V1 = frozenset(
    {
        key
        for key in ROOT_PROOF_META_KEYS_V1
        if key.endswith("_hash")
        or key.endswith("_root")
        or key in {"risc0_image_id", "receipt_verifier_parameters", "receipt_control_id"}
    }
)


class RecursiveStarkReplayBundleError(ValueError):
    """Stable reject at the local replay-bundle boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class NamedArtifactInput:
    """Explicit file input copied under one bundle-local evidence role."""

    name: str
    path: Path

    def __post_init__(self) -> None:
        _validate_input_name(self.name)


def _reject(code: str, detail: str) -> RecursiveStarkReplayBundleError:
    return RecursiveStarkReplayBundleError(code, detail)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise _reject("DUPLICATE_JSON_KEY", key)
        out[key] = value
    return out


def _reject_float(value: str) -> object:
    raise _reject("NONCANONICAL_JSON_NUMBER", value)


def _validate_json_shape(value: object) -> None:
    stack: list[tuple[object, int]] = [(value, 1)]
    item_count = 0
    while stack:
        current, depth = stack.pop()
        item_count += 1
        if item_count > MAX_JSON_ITEMS:
            raise _reject("JSON_ITEM_LIMIT", str(MAX_JSON_ITEMS))
        if depth > MAX_JSON_DEPTH:
            raise _reject("JSON_DEPTH_LIMIT", str(MAX_JSON_DEPTH))
        if isinstance(current, Mapping):
            for key, child in current.items():
                if not isinstance(key, str):
                    raise _reject("JSON_KEY_TYPE", "object key must be a string")
                stack.append((child, depth + 1))
        elif isinstance(current, list):
            stack.extend((child, depth + 1) for child in current)
        elif isinstance(current, int) and not isinstance(current, bool):
            if current.bit_length() > 256:
                raise _reject("JSON_INTEGER_LIMIT", "integer exceeds 256 bits")
        elif not isinstance(current, (str, bool, type(None))):
            raise _reject("JSON_VALUE_TYPE", type(current).__name__)


def parse_bounded_json(raw: bytes, *, require_canonical: bool) -> object:
    if len(raw) > MAX_JSON_ARTIFACT_BYTES:
        raise _reject("JSON_BYTE_LIMIT", str(len(raw)))
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except RecursiveStarkReplayBundleError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", str(exc)) from exc
    _validate_json_shape(value)
    try:
        canonical = canonical_json_bytes(value)
    except (TypeError, ValueError) as exc:
        raise _reject("NONCANONICAL_JSON_VALUE", str(exc)) from exc
    if len(canonical) > MAX_JSON_ARTIFACT_BYTES:
        raise _reject("JSON_BYTE_LIMIT", str(len(canonical)))
    if require_canonical and raw != canonical:
        raise _reject("NONCANONICAL_JSON_BYTES", "JSON bytes differ from canonical encoding")
    return value


def canonical_relative_path_v1(value: object) -> str:
    if not isinstance(value, str) or not value:
        raise _reject("UNSAFE_PATH", "path must be a non-empty string")
    if "\x00" in value or "\\" in value:
        raise _reject("UNSAFE_PATH", value)
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject("UNSAFE_PATH", "path must be ASCII") from exc
    path = PurePosixPath(value)
    if (
        not path.parts
        or path.is_absolute()
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise _reject("UNSAFE_PATH", value)
    if path.as_posix() != value:
        raise _reject("UNSAFE_PATH", value)
    return value


def _validate_input_name(value: object) -> str:
    if not isinstance(value, str) or INPUT_NAME_RE.fullmatch(value) is None:
        raise _reject("INVALID_INPUT_NAME", str(value))
    if len(value.encode("ascii")) > MAX_INPUT_NAME_BYTES:
        raise _reject("INVALID_INPUT_NAME", "name exceeds byte limit")
    return value


def _validate_artifact_role(value: object) -> str:
    if not isinstance(value, str) or not value:
        raise _reject("ARTIFACT_ROLE", str(value))
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise _reject("ARTIFACT_ROLE", "role must be ASCII") from exc
    if len(encoded) > MAX_ARTIFACT_ROLE_BYTES:
        raise _reject("ARTIFACT_ROLE", "role exceeds byte limit")
    return value


def _absolute_without_resolving(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _assert_no_symlink_components(path: Path, *, stop: Path | None = None) -> None:
    absolute = _absolute_without_resolving(path)
    if stop is None:
        current = Path(absolute.anchor)
        parts = absolute.parts[1:]
    else:
        root = _absolute_without_resolving(stop)
        try:
            relative = absolute.relative_to(root)
        except ValueError as exc:
            raise _reject("PATH_ESCAPE", os.fspath(path)) from exc
        current = root
        if current.is_symlink():
            raise _reject("SYMLINK_FORBIDDEN", os.fspath(current))
        parts = relative.parts
    for part in parts:
        current = current / part
        try:
            mode = os.lstat(current).st_mode
        except OSError as exc:
            raise _reject("ARTIFACT_MISSING", os.fspath(current)) from exc
        if stat.S_ISLNK(mode):
            raise _reject("SYMLINK_FORBIDDEN", os.fspath(current))


def _directory_open_flags() -> int:
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY"):
        raise _reject("NO_NOFOLLOW", "platform lacks descriptor-safe directory flags")
    return os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)


def _open_directory_chain(path: Path) -> int:
    absolute = _absolute_without_resolving(path)
    flags = _directory_open_flags()
    try:
        descriptor = os.open(absolute.anchor, flags)
    except OSError as exc:
        raise _reject("DIRECTORY_OPEN_FAILED", absolute.anchor) from exc
    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current = current / part
        try:
            next_descriptor = os.open(part, flags, dir_fd=descriptor)
        except OSError as exc:
            os.close(descriptor)
            raise _reject("DIRECTORY_COMPONENT_INVALID", os.fspath(current)) from exc
        os.close(descriptor)
        descriptor = next_descriptor
    return descriptor


def _regular_handle_from_descriptor(
    descriptor: int,
    *,
    display_path: str,
    max_bytes: int,
) -> tuple[BinaryIO, os.stat_result]:
    try:
        metadata = os.fstat(descriptor)
    except OSError:
        os.close(descriptor)
        raise
    if not stat.S_ISREG(metadata.st_mode):
        os.close(descriptor)
        raise _reject("REGULAR_FILE_REQUIRED", display_path)
    if metadata.st_size > max_bytes:
        os.close(descriptor)
        raise _reject("ARTIFACT_BYTE_LIMIT", display_path)
    try:
        return os.fdopen(descriptor, "rb", closefd=True), metadata
    except (OSError, ValueError):
        os.close(descriptor)
        raise


def _open_regular_at(
    directory_descriptor: int,
    name: str,
    *,
    display_path: str,
    max_bytes: int,
) -> tuple[BinaryIO, os.stat_result]:
    if not name or name in {".", ".."} or "/" in name or "\\" in name or "\x00" in name:
        raise _reject("UNSAFE_PATH", display_path)
    try:
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
            dir_fd=directory_descriptor,
        )
    except OSError as exc:
        raise _reject("ARTIFACT_OPEN_FAILED", display_path) from exc
    return _regular_handle_from_descriptor(
        descriptor,
        display_path=display_path,
        max_bytes=max_bytes,
    )


def _open_regular(path: Path, *, max_bytes: int) -> tuple[BinaryIO, os.stat_result]:
    absolute = _absolute_without_resolving(path)
    _assert_no_symlink_components(absolute)
    parent_descriptor = _open_directory_chain(absolute.parent)
    try:
        return _open_regular_at(
            parent_descriptor,
            absolute.name,
            display_path=os.fspath(absolute),
            max_bytes=max_bytes,
        )
    finally:
        os.close(parent_descriptor)


def _read_open_handle(
    handle: BinaryIO,
    before: os.stat_result,
    *,
    display_path: str,
    max_bytes: int,
) -> bytes:
    with handle:
        raw = handle.read(max_bytes + 1)
        after = os.fstat(handle.fileno())
    if (
        len(raw) != before.st_size
        or (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino)
        or before.st_mtime_ns != after.st_mtime_ns
    ):
        raise _reject("ARTIFACT_CHANGED_DURING_READ", display_path)
    if not raw:
        raise _reject("EMPTY_ARTIFACT", display_path)
    return raw


def _read_regular(path: Path, *, max_bytes: int) -> bytes:
    display_path = os.fspath(path)
    handle, before = _open_regular(path, max_bytes=max_bytes)
    return _read_open_handle(
        handle,
        before,
        display_path=display_path,
        max_bytes=max_bytes,
    )


def _regular_size(path: Path, *, max_bytes: int) -> int:
    handle, metadata = _open_regular(path, max_bytes=max_bytes)
    handle.close()
    if metadata.st_size <= 0:
        raise _reject("EMPTY_ARTIFACT", os.fspath(path))
    return metadata.st_size


def _read_regular_at(
    directory_descriptor: int,
    name: str,
    *,
    display_path: str,
    max_bytes: int,
) -> bytes:
    handle, before = _open_regular_at(
        directory_descriptor,
        name,
        display_path=display_path,
        max_bytes=max_bytes,
    )
    return _read_open_handle(
        handle,
        before,
        display_path=display_path,
        max_bytes=max_bytes,
    )


def _sha256_bytes(raw: bytes) -> str:
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def _write_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o600)
    with os.fdopen(descriptor, "wb", closefd=True) as handle:
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())


def _artifact_entry(*, role: str, kind: str, path: str, raw: bytes) -> dict[str, Any]:
    return {
        "kind": kind,
        "path": canonical_relative_path_v1(path),
        "role": role,
        "sha256": _sha256_bytes(raw),
        "size_bytes": len(raw),
    }


def _method_image_id_from_words(words: Sequence[object]) -> str:
    if len(words) != 8:
        raise _reject("EXPORT_IMAGE_WORDS", "expected eight u32 words")
    encoded = bytearray()
    for word in words:
        if not isinstance(word, int) or isinstance(word, bool) or not 0 <= word <= 0xFFFF_FFFF:
            raise _reject("EXPORT_IMAGE_WORDS", "word must be u32")
        encoded.extend(word.to_bytes(4, "little"))
    if not any(encoded):
        raise _reject("EXPORT_ZERO_IMAGE_ID", "image ID must be nonzero")
    return encoded.hex()


def validate_artifact_export_report_v1(value: object) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != EXPORT_REPORT_KEYS_V1:
        raise _reject("EXPORT_REPORT_SCHEMA", "top-level keys mismatch")
    if value.get("schema") != ARTIFACT_EXPORT_SCHEMA_V1:
        raise _reject("EXPORT_REPORT_SCHEMA", "schema mismatch")
    if value.get("sdk_version") != SDK_VERSION_V1:
        raise _reject("EXPORT_SDK_VERSION", str(value.get("sdk_version")))
    methods = value.get("methods")
    if not isinstance(methods, list) or value.get("method_count") != len(methods):
        raise _reject("EXPORT_METHOD_COUNT", "method_count mismatch")
    if len(methods) != len(EXPECTED_METHOD_NAMES_V1):
        raise _reject("EXPORT_METHOD_COUNT", str(len(methods)))

    observed_names: list[str] = []
    for index, method in enumerate(methods):
        if not isinstance(method, Mapping) or set(method) != EXPORT_METHOD_KEYS_V1:
            raise _reject("EXPORT_METHOD_SCHEMA", str(index))
        name = method.get("name")
        if not isinstance(name, str):
            raise _reject("EXPORT_METHOD_NAME", str(index))
        observed_names.append(name)
        if method.get("artifact") != EXPECTED_METHOD_ARTIFACTS_V1.get(name):
            raise _reject("EXPORT_METHOD_ARTIFACT", name)
        if method.get("program_format") != "risc0_program_binary_v1compat_v3":
            raise _reject("EXPORT_PROGRAM_FORMAT", name)
        program_bytes = method.get("program_bytes")
        if not isinstance(program_bytes, int) or isinstance(program_bytes, bool) or program_bytes <= 0:
            raise _reject("EXPORT_PROGRAM_BYTES", name)
        if not isinstance(method.get("program_sha256"), str) or BARE_SHA256_RE.fullmatch(
            str(method.get("program_sha256"))
        ) is None:
            raise _reject("EXPORT_PROGRAM_SHA256", name)
        image_id = method.get("image_id")
        if not isinstance(image_id, str) or IMAGE_ID_RE.fullmatch(image_id) is None:
            raise _reject("EXPORT_IMAGE_ID", name)
        words = method.get("generated_image_id_words")
        if not isinstance(words, list) or _method_image_id_from_words(words) != image_id:
            raise _reject("EXPORT_IMAGE_ENCODING", name)
    if tuple(observed_names) != EXPECTED_METHOD_NAMES_V1:
        raise _reject("EXPORT_METHOD_ORDER", ",".join(observed_names))
    return value


def _validated_export_methods(
    export_report: Mapping[str, Any],
) -> list[Mapping[str, Any]]:
    methods = export_report.get("methods")
    if not isinstance(methods, list):
        raise _reject("EXPORT_METHOD_COUNT", "methods must be a list")
    validated: list[Mapping[str, Any]] = []
    for index, method in enumerate(methods):
        if not isinstance(method, Mapping):
            raise _reject("EXPORT_METHOD_SCHEMA", str(index))
        validated.append(method)
    return validated


def recursive_stark_source_root_v1(source_rows: Sequence[Mapping[str, Any]]) -> str:
    payload = {"schema": f"{MANIFEST_SCHEMA_V1}.source_root", "source_rows": list(source_rows)}
    return "sha256:" + hashlib.sha256(
        SOURCE_ROOT_DOMAIN_V1 + canonical_json_bytes(payload)
    ).hexdigest()


def recursive_stark_replay_manifest_hash_v1(manifest: Mapping[str, Any]) -> str:
    body = {str(key): value for key, value in manifest.items() if key != "manifest_hash"}
    return "sha256:" + hashlib.sha256(
        MANIFEST_HASH_DOMAIN_V1 + canonical_json_bytes(body)
    ).hexdigest()


def _sorted_artifacts(artifacts: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        (dict(item) for item in artifacts),
        key=lambda item: (str(item.get("kind")), str(item.get("role")), str(item.get("path"))),
    )


def _copy_named_inputs(
    *,
    kind: str,
    inputs: Sequence[NamedArtifactInput],
    output_root: Path,
) -> tuple[list[dict[str, Any]], dict[str, Mapping[str, Any]]]:
    if not inputs:
        raise _reject("MISSING_ARTIFACT_KIND", kind)
    seen_names: set[str] = set()
    entries: list[dict[str, Any]] = []
    parsed_json: dict[str, Mapping[str, Any]] = {}
    for item in inputs:
        if item.name in seen_names:
            raise _reject("DUPLICATE_ROLE", f"{kind}.{item.name}")
        seen_names.add(item.name)
        raw = _read_regular(item.path, max_bytes=KIND_MAX_BYTES_V1[kind])
        if kind in CANONICAL_JSON_KINDS_V1:
            value = parse_bounded_json(raw, require_canonical=False)
            if not isinstance(value, Mapping):
                raise _reject("JSON_OBJECT_REQUIRED", f"{kind}.{item.name}")
            parsed_json[f"{kind}.{item.name}"] = value
            raw = canonical_json_bytes(value)
        relative = f"{KIND_DIRECTORY_V1[kind]}/{item.name}"
        _write_new(output_root / relative, raw)
        entries.append(_artifact_entry(role=f"{kind}.{item.name}", kind=kind, path=relative, raw=raw))
    return entries, parsed_json


def _require_bare_sha256(value: object, *, code: str, field: str) -> str:
    if not isinstance(value, str) or BARE_SHA256_RE.fullmatch(value) is None:
        raise _reject(code, field)
    return value


def _is_exact_int(value: object, *, minimum: int, maximum: int) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and minimum <= value <= maximum


def _validate_proof_artifact(value: Mapping[str, Any], *, role: str) -> Mapping[str, Any]:
    if set(value) != PROOF_KEYS_V1 or value.get("schema") != "tau_state_proof":
        raise _reject("PROOF_SCHEMA", role)
    if not _is_exact_int(value.get("schema_version"), minimum=1, maximum=1) or value.get(
        "proof_type"
    ) not in RECURSIVE_PROOF_TYPES_V1:
        raise _reject("PROOF_SCHEMA", role)
    state_hash = _require_bare_sha256(value.get("state_hash"), code="PROOF_STATE_HASH", field=role)
    receipt = value.get("proof")
    if not isinstance(receipt, str) or not receipt:
        raise _reject("PROOF_RECEIPT", role)
    try:
        decoded = base64.b64decode(receipt.encode("ascii"), validate=True)
    except (UnicodeEncodeError, binascii.Error, ValueError) as exc:
        raise _reject("PROOF_RECEIPT", role) from exc
    if (
        not decoded
        or len(decoded) > MAX_RECEIPT_BYTES
        or base64.b64encode(decoded).decode("ascii") != receipt
    ):
        raise _reject("PROOF_RECEIPT", role)
    meta = value.get("meta")
    if not isinstance(meta, Mapping):
        raise _reject("PROOF_META_SCHEMA", role)
    if value.get("proof_type") != ROOT_PROOF_TYPE_V1:
        return value
    if set(meta) != ROOT_PROOF_META_KEYS_V1:
        raise _reject("ROOT_PROOF_META_SCHEMA", role)
    if meta.get("receipt_codec") != RECEIPT_CODEC_V1 or meta.get("receipt_kind") != "succinct":
        raise _reject("ROOT_PROOF_PROFILE", role)
    if (
        meta.get("domain_separator") != ROOT_DOMAIN_SEPARATOR_V1
        or meta.get("proof_profile") != ROOT_PROOF_PROFILE_V1
        or meta.get("receipt_hashfn") != "poseidon2"
    ):
        raise _reject("ROOT_PROOF_PROFILE", role)
    if meta.get("proof_type") != ROOT_PROOF_TYPE_V1 or meta.get("post_state_root") != state_hash:
        raise _reject("ROOT_PROOF_BINDING", role)
    for key in ROOT_HASH_META_KEYS_V1:
        _require_bare_sha256(meta.get(key), code="ROOT_PROOF_META_HASH", field=f"{role}.{key}")
    for key in ("chain_id", "domain_separator", "proof_profile", "receipt_hashfn"):
        if not isinstance(meta.get(key), str) or not meta.get(key):
            raise _reject("ROOT_PROOF_META_VALUE", f"{role}.{key}")
    if not _is_exact_int(meta.get("epoch_id"), minimum=0, maximum=0xFFFF_FFFF_FFFF_FFFF):
        raise _reject("ROOT_PROOF_META_VALUE", f"{role}.epoch_id")
    if not _is_exact_int(meta.get("child_count"), minimum=1, maximum=0xFFFF_FFFF):
        raise _reject("ROOT_PROOF_META_VALUE", f"{role}.child_count")
    return value


def _validate_verify_request(
    value: Mapping[str, Any],
    *,
    role: str,
    root_proofs: Sequence[Mapping[str, Any]],
    aggregate_image_id: str,
) -> Mapping[str, Any]:
    if set(value) != VERIFY_REQUEST_KEYS_V1 or not _is_exact_int(
        value.get("schema_version"), minimum=1, maximum=1
    ):
        raise _reject("VERIFY_REQUEST_SCHEMA", role)
    state_hash = _require_bare_sha256(
        value.get("state_hash"), code="VERIFY_REQUEST_STATE_HASH", field=role
    )
    proof = value.get("proof")
    if not isinstance(proof, Mapping):
        raise _reject("VERIFY_REQUEST_PROOF", role)
    _validate_proof_artifact(proof, role=f"{role}.proof")
    if proof.get("proof_type") != ROOT_PROOF_TYPE_V1 or not any(proof == item for item in root_proofs):
        raise _reject("VERIFY_REQUEST_PROOF_UNBOUND", role)
    expectations = value.get("recursive_expectations")
    if not isinstance(expectations, Mapping) or set(expectations) != RECURSIVE_EXPECTATION_KEYS_V1:
        raise _reject("VERIFY_EXPECTATIONS_SCHEMA", role)
    recursive_input = value.get("recursive_input")
    if not isinstance(recursive_input, Mapping):
        raise _reject("VERIFY_RECURSIVE_INPUT_SCHEMA", role)
    meta = proof.get("meta")
    if not isinstance(meta, Mapping):
        raise _reject("ROOT_PROOF_META_SCHEMA", role)
    if proof.get("state_hash") != state_hash or expectations.get("post_state_root") != state_hash:
        raise _reject("VERIFY_REQUEST_STATE_BINDING", role)
    if not _is_exact_int(expectations.get("journal_version"), minimum=1, maximum=1):
        raise _reject("VERIFY_EXPECTATIONS_SCHEMA", f"{role}.journal_version")
    for key in ROOT_PROOF_META_KEYS_V1:
        if expectations.get(key) != meta.get(key):
            raise _reject("VERIFY_EXPECTATIONS_PROOF_MISMATCH", f"{role}.{key}")
    if expectations.get("risc0_image_id") != aggregate_image_id:
        raise _reject("VERIFY_EXPORT_IMAGE_MISMATCH", role)
    return expectations


def _aggregate_image_id(export_report: Mapping[str, Any]) -> str:
    for method in _validated_export_methods(export_report):
        if method.get("name") == "aggregate":
            return _require_bare_sha256(
                method.get("image_id"), code="EXPORT_IMAGE_ID", field="aggregate"
            )
    raise _reject("EXPORT_METHOD_NAME", "aggregate")


def _validate_replay_transcript_bindings(
    parsed_json_by_role: Mapping[str, Mapping[str, Any]],
    export_report: Mapping[str, Any],
) -> int:
    aggregate_image_id = _aggregate_image_id(export_report)
    proofs = [
        _validate_proof_artifact(value, role=role)
        for role, value in parsed_json_by_role.items()
        if role.startswith("proof.")
    ]
    root_proofs = [item for item in proofs if item.get("proof_type") == ROOT_PROOF_TYPE_V1]
    verify_requests: list[Mapping[str, Any]] = []
    for role, value in parsed_json_by_role.items():
        if not role.startswith("request."):
            continue
        schema = value.get("schema")
        if schema == "tau_state_proof_verify":
            verify_requests.append(
                _validate_verify_request(
                    value,
                    role=role,
                    root_proofs=root_proofs,
                    aggregate_image_id=aggregate_image_id,
                )
            )
        elif schema != "tau_state_proof_request" or not _is_exact_int(
            value.get("schema_version"), minimum=1, maximum=1
        ):
            raise _reject("REQUEST_SCHEMA", role)
    if len(verify_requests) > MAX_REPLAY_TRANSCRIPTS:
        raise _reject("VERIFY_REQUEST_COUNT_LIMIT", str(len(verify_requests)))

    accepted = 0
    for role, response in parsed_json_by_role.items():
        if not role.startswith("verification."):
            continue
        if response.get("ok") is False:
            if set(response) != {"ok", "error"} or not isinstance(response.get("error"), str):
                raise _reject("VERIFICATION_SCHEMA", role)
            continue
        if response.get("ok") is not True:
            raise _reject("VERIFICATION_SCHEMA", role)
        if accepted >= MAX_REPLAY_TRANSCRIPTS:
            raise _reject("VERIFICATION_COUNT_LIMIT", str(accepted + 1))
        bound = False
        for expectations in verify_requests:
            try:
                parse_authenticated_recursive_facts(
                    response,
                    trusted_expectations=expectations,
                )
            except (TypeError, ValueError):
                continue
            facts = response.get("verified_recursive_facts")
            if isinstance(facts, Mapping) and facts.get("aggregate_image_id") == aggregate_image_id:
                bound = True
                break
        if not bound:
            raise _reject("VERIFICATION_TRANSCRIPT_UNBOUND", role)
        accepted += 1
    if accepted == 0:
        raise _reject("ACCEPTED_VERIFICATION_REQUIRED", "no bound verification has ok=true")
    return accepted


def _manifest_body(
    *,
    artifacts: Sequence[Mapping[str, Any]],
    source_rows: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    artifact_rows = _sorted_artifacts(artifacts)
    return {
        "artifact_count": len(artifact_rows),
        "artifact_export": {
            "method_names": list(EXPECTED_METHOD_NAMES_V1),
            "report_role": "artifact_export.report",
            "schema": ARTIFACT_EXPORT_SCHEMA_V1,
            "sdk_version": SDK_VERSION_V1,
        },
        "artifacts": artifact_rows,
        "invalidated_evidence_versions": list(INVALIDATED_EVIDENCE_VERSIONS_V1),
        "non_claims": list(NON_CLAIMS_V1),
        "production_ready": False,
        "public_claim_allowed": False,
        "reproducible_build_claim": False,
        "schema": MANIFEST_SCHEMA_V1,
        "source_root": recursive_stark_source_root_v1(source_rows),
        "source_rows": list(source_rows),
        "status": STATUS_V1,
        "total_size_bytes": sum(int(item["size_bytes"]) for item in artifact_rows),
    }


def build_recursive_stark_replay_bundle_v1(
    *,
    artifact_export_report_path: Path,
    artifact_directory: Path,
    source_files: Sequence[NamedArtifactInput],
    toolchain_files: Sequence[NamedArtifactInput],
    proof_files: Sequence[NamedArtifactInput],
    request_files: Sequence[NamedArtifactInput],
    verification_files: Sequence[NamedArtifactInput],
    output_directory: Path,
) -> dict[str, Any]:
    """Build one hash-bound local replay bundle in a new directory."""

    output_directory = _absolute_without_resolving(output_directory)
    parent = output_directory.parent
    if output_directory.exists() or output_directory.is_symlink():
        raise _reject("OUTPUT_EXISTS", os.fspath(output_directory))
    if not parent.is_dir() or parent.is_symlink():
        raise _reject("OUTPUT_PARENT_INVALID", os.fspath(parent))
    _assert_no_symlink_components(parent)

    named_inputs = {
        "source": source_files,
        "toolchain": toolchain_files,
        "proof": proof_files,
        "request": request_files,
        "verification": verification_files,
    }
    for kind in REQUIRED_NAMED_KINDS_V1:
        if not named_inputs[kind]:
            raise _reject("MISSING_ARTIFACT_KIND", kind)
        names = [item.name for item in named_inputs[kind]]
        if len(names) != len(set(names)):
            raise _reject("DUPLICATE_ROLE", kind)
    planned_count = 1 + len(EXPECTED_METHOD_NAMES_V1) + sum(
        len(named_inputs[kind]) for kind in REQUIRED_NAMED_KINDS_V1
    )
    if planned_count > MAX_ARTIFACT_COUNT:
        raise _reject("ARTIFACT_COUNT_LIMIT", str(planned_count))

    export_raw = _read_regular(
        artifact_export_report_path,
        max_bytes=MAX_JSON_ARTIFACT_BYTES,
    )
    export_value = parse_bounded_json(export_raw, require_canonical=False)
    export_report = validate_artifact_export_report_v1(export_value)
    export_canonical = canonical_json_bytes(export_report)

    planned_bytes = len(export_canonical)
    for method in _validated_export_methods(export_report):
        planned_bytes += _regular_size(
            artifact_directory / str(method["artifact"]),
            max_bytes=MAX_METHOD_ARTIFACT_BYTES,
        )
    for kind in REQUIRED_NAMED_KINDS_V1:
        planned_bytes += sum(
            _regular_size(item.path, max_bytes=KIND_MAX_BYTES_V1[kind])
            for item in named_inputs[kind]
        )
    if planned_bytes > MAX_TOTAL_ARTIFACT_BYTES:
        raise _reject("TOTAL_ARTIFACT_BYTE_LIMIT", str(planned_bytes))

    temp_path = Path(tempfile.mkdtemp(prefix=f".{output_directory.name}.tmp-", dir=parent))
    published = False
    try:
        artifacts: list[dict[str, Any]] = []
        export_relative = "artifact_export/report.json"
        _write_new(temp_path / export_relative, export_canonical)
        artifacts.append(
            _artifact_entry(
                role="artifact_export.report",
                kind="artifact_export",
                path=export_relative,
                raw=export_canonical,
            )
        )

        for method in _validated_export_methods(export_report):
            name = str(method["name"])
            filename = str(method["artifact"])
            raw = _read_regular(
                artifact_directory / filename,
                max_bytes=MAX_METHOD_ARTIFACT_BYTES,
            )
            if len(raw) != method["program_bytes"]:
                raise _reject("METHOD_SIZE_MISMATCH", name)
            if hashlib.sha256(raw).hexdigest() != method["program_sha256"]:
                raise _reject("METHOD_SHA256_MISMATCH", name)
            relative = f"methods/{filename}"
            _write_new(temp_path / relative, raw)
            artifacts.append(
                _artifact_entry(role=f"method.{name}", kind="method", path=relative, raw=raw)
            )

        parsed_by_kind: dict[str, dict[str, Mapping[str, Any]]] = {}
        for kind in REQUIRED_NAMED_KINDS_V1:
            rows, parsed = _copy_named_inputs(
                kind=kind,
                inputs=named_inputs[kind],
                output_root=temp_path,
            )
            artifacts.extend(rows)
            parsed_by_kind[kind] = parsed
        parsed_records = {
            role: value
            for records in parsed_by_kind.values()
            for role, value in records.items()
        }
        _validate_replay_transcript_bindings(parsed_records, export_report)

        source_rows = [
            {key: item[key] for key in ("path", "role", "sha256", "size_bytes")}
            for item in _sorted_artifacts(artifacts)
            if item["kind"] == "source"
        ]
        body = _manifest_body(artifacts=artifacts, source_rows=source_rows)
        manifest = {**body, "manifest_hash": recursive_stark_replay_manifest_hash_v1(body)}
        manifest_raw = canonical_json_bytes(manifest)
        _write_new(temp_path / MANIFEST_FILENAME_V1, manifest_raw)

        manifest_sha256 = _sha256_bytes(manifest_raw)
        local_check = check_recursive_stark_replay_bundle_v1(
            temp_path,
            expected_manifest_sha256=manifest_sha256,
        )
        if local_check["ok"] is not True:
            raise _reject("BUILT_BUNDLE_REJECTED", ";".join(local_check["errors"]))
        if local_check.get("manifest_sha256") != manifest_sha256:
            raise _reject("BUILT_BUNDLE_DIGEST_MISMATCH", "self-check digest mismatch")
        os.replace(temp_path, output_directory)
        published = True
    finally:
        if not published and temp_path.is_dir() and not temp_path.is_symlink():
            shutil.rmtree(temp_path)

    return {
        "schema": BUILD_REPORT_SCHEMA_V1,
        "ok": True,
        "status": STATUS_V1,
        "manifest_hash": manifest["manifest_hash"],
        "manifest_sha256": manifest_sha256,
        "artifact_count": manifest["artifact_count"],
        "source_root": manifest["source_root"],
        "production_ready": False,
        "public_claim_allowed": False,
        "reproducible_build_claim": False,
    }


def _validate_artifact_row(value: object, *, index: int) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != ARTIFACT_KEYS_V1:
        raise _reject("ARTIFACT_ROW_SCHEMA", str(index))
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in KIND_DIRECTORY_V1:
        raise _reject("ARTIFACT_KIND", str(kind))
    role = _validate_artifact_role(value.get("role"))
    relative = canonical_relative_path_v1(value.get("path"))
    if PurePosixPath(relative).parts[0] != KIND_DIRECTORY_V1[str(kind)]:
        raise _reject("ARTIFACT_KIND_PATH", relative)
    if kind == "artifact_export":
        if role != "artifact_export.report" or relative != "artifact_export/report.json":
            raise _reject("ARTIFACT_ROLE_PATH", str(role))
    elif kind == "method":
        if not role.startswith("method."):
            raise _reject("ARTIFACT_ROLE_PATH", str(role))
        method_name = role.removeprefix("method.")
        if relative != f"methods/{EXPECTED_METHOD_ARTIFACTS_V1.get(method_name, '')}":
            raise _reject("ARTIFACT_ROLE_PATH", str(role))
    else:
        prefix = f"{kind}."
        if not role.startswith(prefix):
            raise _reject("ARTIFACT_ROLE_PATH", str(role))
        input_name = _validate_input_name(role.removeprefix(prefix))
        if relative != f"{KIND_DIRECTORY_V1[str(kind)]}/{input_name}":
            raise _reject("ARTIFACT_ROLE_PATH", str(role))
    size_bytes = value.get("size_bytes")
    if not isinstance(size_bytes, int) or isinstance(size_bytes, bool) or size_bytes <= 0:
        raise _reject("ARTIFACT_SIZE", relative)
    sha256 = value.get("sha256")
    if not isinstance(sha256, str) or SHA256_RE.fullmatch(sha256) is None:
        raise _reject("ARTIFACT_SHA256", relative)
    return dict(value)


def _inventory_files(root: Path, *, root_descriptor: int) -> list[str]:
    files: list[str] = []
    expected_directories = set(KIND_DIRECTORY_V1.values())
    visited = 0

    def scan(descriptor: int, display: str) -> list[tuple[str, int]]:
        nonlocal visited
        duplicate = os.dup(descriptor)
        try:
            with os.scandir(duplicate) as iterator:
                entries: list[tuple[str, int]] = []
                for entry in iterator:
                    visited += 1
                    if visited > MAX_INVENTORY_ENTRIES:
                        raise _reject("INVENTORY_ENTRY_LIMIT", str(visited))
                    entries.append((entry.name, entry.stat(follow_symlinks=False).st_mode))
        except OSError as exc:
            raise _reject("INVENTORY_SCAN_FAILED", display) from exc
        finally:
            os.close(duplicate)
        return sorted(entries)

    directory_descriptors: dict[str, int] = {}
    try:
        observed_directories: set[str] = set()
        for name, mode in scan(root_descriptor, os.fspath(root)):
            if stat.S_ISLNK(mode):
                raise _reject("SYMLINK_FORBIDDEN", name)
            if stat.S_ISDIR(mode):
                if name not in expected_directories:
                    raise _reject("INVENTORY_MISMATCH", f"undeclared_directory={name}")
                observed_directories.add(name)
            elif stat.S_ISREG(mode) and name == MANIFEST_FILENAME_V1:
                files.append(MANIFEST_FILENAME_V1)
            else:
                raise _reject("INVENTORY_MISMATCH", f"undeclared_root_entry={name}")
        if observed_directories != expected_directories:
            missing = sorted(expected_directories - observed_directories)
            raise _reject("INVENTORY_MISMATCH", f"missing_directories={missing}")
        for directory in sorted(expected_directories):
            try:
                directory_descriptor = os.open(
                    directory,
                    _directory_open_flags(),
                    dir_fd=root_descriptor,
                )
            except OSError as exc:
                raise _reject("DIRECTORY_COMPONENT_INVALID", directory) from exc
            directory_descriptors[directory] = directory_descriptor
            for name, mode in scan(directory_descriptor, directory):
                relative = canonical_relative_path_v1(f"{directory}/{name}")
                if stat.S_ISLNK(mode):
                    raise _reject("SYMLINK_FORBIDDEN", relative)
                if not stat.S_ISREG(mode):
                    raise _reject("INVENTORY_MISMATCH", f"nested_entry={relative}")
                files.append(relative)
        return sorted(files)
    finally:
        for descriptor in directory_descriptors.values():
            os.close(descriptor)


def _load_bundle_manifest(bundle_descriptor: int) -> tuple[Mapping[str, Any], bytes]:
    raw = _read_regular_at(
        bundle_descriptor,
        MANIFEST_FILENAME_V1,
        display_path=MANIFEST_FILENAME_V1,
        max_bytes=MAX_MANIFEST_BYTES,
    )
    value = parse_bounded_json(raw, require_canonical=True)
    if not isinstance(value, Mapping):
        raise _reject("MANIFEST_SCHEMA", "manifest must be an object")
    return value, raw


def _validate_manifest_envelope(manifest: Mapping[str, Any]) -> None:
    if set(manifest) != MANIFEST_KEYS_V1 or manifest.get("schema") != MANIFEST_SCHEMA_V1:
        raise _reject("MANIFEST_SCHEMA", "top-level schema or keys mismatch")
    if manifest.get("status") != STATUS_V1:
        raise _reject("STATUS_MISMATCH", str(manifest.get("status")))
    for key in ("production_ready", "public_claim_allowed", "reproducible_build_claim"):
        if manifest.get(key) is not False:
            raise _reject("CLAIM_ESCALATION", key)
    if manifest.get("non_claims") != list(NON_CLAIMS_V1):
        raise _reject("NON_CLAIMS_MISMATCH", "non_claims must match local evidence scope")
    if manifest.get("invalidated_evidence_versions") != list(INVALIDATED_EVIDENCE_VERSIONS_V1):
        raise _reject("INVALIDATED_EVIDENCE_MISMATCH", "RISC0 1.2.6 must remain invalid")
    if manifest.get("manifest_hash") != recursive_stark_replay_manifest_hash_v1(manifest):
        raise _reject("MANIFEST_HASH_MISMATCH", "manifest body hash mismatch")
    expected_export_ref = {
        "method_names": list(EXPECTED_METHOD_NAMES_V1),
        "report_role": "artifact_export.report",
        "schema": ARTIFACT_EXPORT_SCHEMA_V1,
        "sdk_version": SDK_VERSION_V1,
    }
    export_ref = manifest.get("artifact_export")
    if not isinstance(export_ref, Mapping) or set(export_ref) != ARTIFACT_EXPORT_REF_KEYS_V1:
        raise _reject("EXPORT_REF_SCHEMA", "artifact_export keys mismatch")
    if dict(export_ref) != expected_export_ref:
        raise _reject("EXPORT_REF_MISMATCH", "artifact_export reference mismatch")


def _validate_source_rows(
    manifest: Mapping[str, Any], artifacts: Sequence[Mapping[str, Any]]
) -> None:
    raw_rows = manifest.get("source_rows")
    if not isinstance(raw_rows, list):
        raise _reject("SOURCE_ROWS_SCHEMA", "source_rows must be a list")
    rows: list[dict[str, Any]] = []
    for index, row in enumerate(raw_rows):
        if not isinstance(row, Mapping) or set(row) != SOURCE_ROW_KEYS_V1:
            raise _reject("SOURCE_ROW_SCHEMA", str(index))
        rows.append(dict(row))
    expected = [
        {key: item[key] for key in ("path", "role", "sha256", "size_bytes")}
        for item in artifacts
        if item["kind"] == "source"
    ]
    if rows != expected:
        raise _reject("SOURCE_ROWS_MISMATCH", "source rows differ from source artifacts")
    if manifest.get("source_root") != recursive_stark_source_root_v1(rows):
        raise _reject("SOURCE_ROOT_MISMATCH", "source root mismatch")


def _validate_artifact_inventory(
    *,
    bundle_root: Path,
    bundle_descriptor: int,
    manifest: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], Mapping[str, Any]]:
    raw_artifacts = manifest.get("artifacts")
    if not isinstance(raw_artifacts, list) or not raw_artifacts:
        raise _reject("ARTIFACTS_SCHEMA", "artifacts must be a non-empty list")
    if len(raw_artifacts) > MAX_ARTIFACT_COUNT:
        raise _reject("ARTIFACT_COUNT_LIMIT", str(len(raw_artifacts)))
    for index, item in enumerate(raw_artifacts):
        if not isinstance(item, Mapping) or set(item) != ARTIFACT_KEYS_V1:
            raise _reject("ARTIFACT_ROW_SCHEMA", str(index))
    raw_roles = [_validate_artifact_role(item.get("role")) for item in raw_artifacts]
    raw_paths = [canonical_relative_path_v1(item.get("path")) for item in raw_artifacts]
    if len(raw_roles) != len(set(raw_roles)):
        raise _reject("DUPLICATE_ROLE", "artifact roles must be unique")
    if len(raw_paths) != len(set(raw_paths)):
        raise _reject("DUPLICATE_PATH", "artifact paths must be unique")
    artifacts = [_validate_artifact_row(item, index=index) for index, item in enumerate(raw_artifacts)]
    if artifacts != _sorted_artifacts(artifacts):
        raise _reject("ARTIFACT_ORDER", "artifact rows must be canonically ordered")
    roles = [str(item["role"]) for item in artifacts]
    paths = [str(item["path"]) for item in artifacts]
    if len(roles) != len(set(roles)):
        raise _reject("DUPLICATE_ROLE", "artifact roles must be unique")
    if len(paths) != len(set(paths)):
        raise _reject("DUPLICATE_PATH", "artifact paths must be unique")
    if manifest.get("artifact_count") != len(artifacts):
        raise _reject("ARTIFACT_COUNT_MISMATCH", str(manifest.get("artifact_count")))
    total = sum(int(item["size_bytes"]) for item in artifacts)
    if total > MAX_TOTAL_ARTIFACT_BYTES:
        raise _reject("TOTAL_ARTIFACT_BYTE_LIMIT", str(total))
    if manifest.get("total_size_bytes") != total:
        raise _reject("TOTAL_SIZE_MISMATCH", str(manifest.get("total_size_bytes")))

    actual_files = _inventory_files(bundle_root, root_descriptor=bundle_descriptor)
    expected_files = sorted([MANIFEST_FILENAME_V1, *paths])
    if actual_files != expected_files:
        missing = sorted(set(expected_files) - set(actual_files))
        undeclared = sorted(set(actual_files) - set(expected_files))
        raise _reject("INVENTORY_MISMATCH", f"missing={missing};undeclared={undeclared}")

    parsed_json_by_role: dict[str, Mapping[str, Any]] = {}
    kind_counts = {kind: 0 for kind in KIND_DIRECTORY_V1}
    for item in artifacts:
        relative = str(item["path"])
        parts = PurePosixPath(relative).parts
        try:
            directory_descriptor = os.open(
                parts[0],
                _directory_open_flags(),
                dir_fd=bundle_descriptor,
            )
        except OSError as exc:
            raise _reject("DIRECTORY_COMPONENT_INVALID", parts[0]) from exc
        try:
            raw = _read_regular_at(
                directory_descriptor,
                parts[1],
                display_path=relative,
                max_bytes=KIND_MAX_BYTES_V1[str(item["kind"])],
            )
        finally:
            os.close(directory_descriptor)
        if len(raw) != item["size_bytes"] or _sha256_bytes(raw) != item["sha256"]:
            raise _reject("ARTIFACT_BINDING_MISMATCH", relative)
        kind = str(item["kind"])
        kind_counts[kind] += 1
        if kind in CANONICAL_JSON_KINDS_V1:
            value = parse_bounded_json(raw, require_canonical=True)
            if not isinstance(value, Mapping):
                raise _reject("JSON_OBJECT_REQUIRED", relative)
            parsed_json_by_role[str(item["role"])] = value
    if kind_counts["artifact_export"] != 1 or kind_counts["method"] != len(
        EXPECTED_METHOD_NAMES_V1
    ):
        raise _reject("ARTIFACT_KIND_COUNT", str(kind_counts))
    for kind in REQUIRED_NAMED_KINDS_V1:
        if kind_counts[kind] < 1:
            raise _reject("MISSING_ARTIFACT_KIND", kind)
    export_report = parsed_json_by_role.get("artifact_export.report")
    if export_report is None:
        raise _reject("EXPORT_REPORT_MISSING", "artifact_export.report")
    validated_export = validate_artifact_export_report_v1(export_report)
    _validate_replay_transcript_bindings(parsed_json_by_role, validated_export)
    return artifacts, validated_export


def _validate_export_method_bindings(
    artifacts: Sequence[Mapping[str, Any]], export_report: Mapping[str, Any]
) -> None:
    artifacts_by_role = {str(item["role"]): item for item in artifacts}
    for method in _validated_export_methods(export_report):
        name = str(method["name"])
        row = artifacts_by_role.get(f"method.{name}")
        if row is None:
            raise _reject("METHOD_ARTIFACT_MISSING", name)
        if row["path"] != f"methods/{method['artifact']}":
            raise _reject("METHOD_PATH_MISMATCH", name)
        if row["size_bytes"] != method["program_bytes"]:
            raise _reject("METHOD_SIZE_MISMATCH", name)
        if row["sha256"] != f"sha256:{method['program_sha256']}":
            raise _reject("METHOD_SHA256_MISMATCH", name)


def _validate_expected_manifest_sha256(value: object, actual: str) -> bool:
    if value is None:
        return False
    if not isinstance(value, str) or SHA256_RE.fullmatch(value) is None:
        raise _reject("EXPECTED_MANIFEST_SHA256_FORMAT", str(value))
    if value != actual:
        raise _reject("EXPECTED_MANIFEST_SHA256_MISMATCH", f"expected={value};actual={actual}")
    return True


def check_recursive_stark_replay_bundle_v1(
    bundle_directory: Path,
    *,
    expected_manifest_sha256: str | None = None,
) -> dict[str, Any]:
    """Check a bundle and return a stable machine-readable report."""

    bundle_root = _absolute_without_resolving(bundle_directory)
    bundle_descriptor: int | None = None
    try:
        if not bundle_root.is_dir() or bundle_root.is_symlink():
            raise _reject("BUNDLE_DIRECTORY_INVALID", os.fspath(bundle_root))
        _assert_no_symlink_components(bundle_root)
        bundle_descriptor = _open_directory_chain(bundle_root)
        manifest, manifest_raw = _load_bundle_manifest(bundle_descriptor)
        manifest_sha256 = _sha256_bytes(manifest_raw)
        expected_manifest_sha256_matched = _validate_expected_manifest_sha256(
            expected_manifest_sha256,
            manifest_sha256,
        )
        _validate_manifest_envelope(manifest)
        artifacts, export_report = _validate_artifact_inventory(
            bundle_root=bundle_root,
            bundle_descriptor=bundle_descriptor,
            manifest=manifest,
        )
        _validate_source_rows(manifest, artifacts)
        _validate_export_method_bindings(artifacts, export_report)
    except (RecursiveStarkReplayBundleError, OSError) as exc:
        if isinstance(exc, RecursiveStarkReplayBundleError):
            code = exc.code
            detail = exc.detail
        else:
            code = "FILESYSTEM_ERROR"
            detail = exc.__class__.__name__
        return {
            "schema": CHECK_REPORT_SCHEMA_V1,
            "ok": False,
            "status": "rejected",
            "error_codes": [code],
            "errors": [f"{code}: {detail}"],
            "production_ready": False,
            "public_claim_allowed": False,
        }
    finally:
        if bundle_descriptor is not None:
            os.close(bundle_descriptor)
    return {
        "schema": CHECK_REPORT_SCHEMA_V1,
        "ok": True,
        "status": STATUS_V1,
        "error_codes": [],
        "errors": [],
        "manifest_hash": manifest["manifest_hash"],
        "manifest_sha256": manifest_sha256,
        "artifact_count": manifest["artifact_count"],
        "source_root": manifest["source_root"],
        "expected_manifest_sha256_matched": expected_manifest_sha256_matched,
        "production_ready": False,
        "public_claim_allowed": False,
        "reproducible_build_claim": False,
    }
