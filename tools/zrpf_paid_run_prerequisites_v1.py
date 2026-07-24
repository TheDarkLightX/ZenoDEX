"""Exact authority-neutral prerequisites shared by bounded paid-run tools."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn

if __package__:
    from tools import check_zrpf_stage_execution_profile_v1 as execution_profile
else:
    import check_zrpf_stage_execution_profile_v1 as execution_profile  # type: ignore[no-redef]

BUILD_SCHEMA = "zenodex/zrpf_cuda_r0vm_build_attestation/v1"
BUILD_STATUS = "cuda_r0vm_build_attested_without_release_authority"
PREFLIGHT_SCHEMA = "zenodex/zrpf_h100_preflight/v1"
PREFLIGHT_STATUS = "single_h100_preflight_observed_without_runtime_authority"
CUDA_COMPUTE_PROFILE = "risc0_ipc_cuda_single_visible_device_build_request_v1"
PROOF_PROFILE = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
RISC0_REPOSITORY = "https://github.com/risc0/risc0"
RISC0_TAG = "v3.0.5"
RISC0_COMMIT = "8eb06ab020a92dc5b63ba6dd0836d432aba6d890"
RUST_TOOLCHAIN = "1.89.0"
R0VM_PACKAGE = "risc0-r0vm"
R0VM_FEATURES = ["cuda", "disable-dev-mode"]
H100_MODEL_ID = "nvidia_h100_80gb_cc90_v1"
H100_MIN_MEMORY_BYTES = 80_000_000_000
MAX_INPUT_BYTES = 2 * 1024 * 1024
MAX_PREFLIGHT_VALIDITY_SECONDS = 900
MAX_U64 = (1 << 64) - 1
ZERO_SHA256 = "0" * 64

BUILD_ID_DOMAIN = b"zenodex/zrpf-cuda-r0vm-build-attestation-id/v1\0"
PREFLIGHT_ID_DOMAIN = b"zenodex/zrpf-h100-preflight-id/v1\0"
SEGMENT_SHAPE_DOMAIN = b"zenodex/zrpf-segment-shape/v1\0"

AUTHORITY_FIELDS = [
    "proof_authority",
    "release_authority",
    "settlement_authority",
    "production_authority",
]
AUTHORITY_FALSE = {field: False for field in AUTHORITY_FIELDS}
BUILD_FIELDS = [
    "schema",
    "status",
    "build_attestation_id",
    "source_repository",
    "source_tag",
    "source_commit",
    "rust_toolchain",
    "cargo_lock_sha256",
    "dependency_source_root",
    "builder_image_sha256",
    "cuda_toolkit_version",
    "nvcc_version",
    "nvcc_flags",
    "host_target",
    "linker_identity",
    "package",
    "features",
    "risc0_skip_build_kernels",
    "output_r0vm",
    "runtime_dependency_root",
    "source_archive_root",
    "authority",
]
PREFLIGHT_FIELDS = [
    "schema",
    "status",
    "h100_preflight_id",
    "observed_at_epoch_seconds",
    "valid_until_epoch_seconds",
    "gpu",
    "r0vm",
    "runtime_image_sha256",
    "visible_device_count",
    "visible_device_ordinal",
    "cuda_visible_devices",
    "authority",
]
GPU_FIELDS = [
    "model_id",
    "uuid",
    "name",
    "compute_capability_major",
    "compute_capability_minor",
    "memory_total_bytes",
    "driver_version",
]
ARTIFACT_FIELDS = ["sha256", "size_bytes"]
EXECUTION_SHAPE_FIELDS = [
    "segment_limit_po2",
    "segment_shape_sha256",
    "segment_count",
    "total_user_cycles",
    "total_padded_cycle_capacity",
]


class PrerequisiteError(ValueError):
    """Stable fail-closed prerequisite rejection."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code


@dataclass(frozen=True, slots=True)
class LoadedRecord:
    raw: bytes
    sha256: str
    document: dict[str, object]


@dataclass(frozen=True, slots=True)
class ValidatedPrerequisites:
    profile: LoadedRecord
    build: LoadedRecord
    preflight: LoadedRecord
    execution_shape: dict[str, object]


def validate_prerequisites(
    execution_profile_path: Path,
    cuda_build_attestation_path: Path,
    h100_preflight_path: Path,
    *,
    expected_stage: str,
    trusted_current_epoch_seconds: int,
) -> ValidatedPrerequisites:
    """Validate exact CUDA/H100/profile inputs without minting authority."""

    current_epoch = require_u64(trusted_current_epoch_seconds, "trusted current epoch seconds")
    profile = load_canonical_record(execution_profile_path, "execution profile")
    build = load_canonical_record(cuda_build_attestation_path, "CUDA r0vm build attestation")
    preflight = load_canonical_record(h100_preflight_path, "H100 preflight")
    try:
        execution_profile._validate_document(  # noqa: SLF001
            profile.document,
            profile.raw,
            expected_stage,
            CUDA_COMPUTE_PROFILE,
        )
    except execution_profile.ProfileCheckError as exc:
        raise PrerequisiteError(
            "execution_profile_invalid", f"execution profile rejected: {exc}"
        ) from exc
    validate_build_document(build.document)
    validate_preflight_document(preflight.document, current_epoch)
    if (
        build.document["output_r0vm"] != profile.document["r0vm"]
        or preflight.document["r0vm"] != profile.document["r0vm"]
    ):
        raise PrerequisiteError("r0vm_binding_mismatch", "r0vm identity substitution")
    if profile.document["proof_profile_id"] != PROOF_PROFILE:
        raise PrerequisiteError(
            "proof_profile_mismatch", "proof profile is not governed Succinct V1"
        )
    return ValidatedPrerequisites(
        profile=profile,
        build=build,
        preflight=preflight,
        execution_shape=execution_shape(profile.document),
    )


def validate_build_document(document: dict[str, object]) -> None:
    require_ordered_fields(document, BUILD_FIELDS, "CUDA build attestation")
    if document["schema"] != BUILD_SCHEMA or document["status"] != BUILD_STATUS:
        raise PrerequisiteError("cuda_build_invalid", "CUDA build schema or status mismatch")
    exact_values = {
        "source_repository": RISC0_REPOSITORY,
        "source_tag": RISC0_TAG,
        "source_commit": RISC0_COMMIT,
        "rust_toolchain": RUST_TOOLCHAIN,
        "package": R0VM_PACKAGE,
        "features": R0VM_FEATURES,
    }
    for field, expected in exact_values.items():
        if document[field] != expected:
            raise PrerequisiteError("cuda_build_invalid", f"CUDA build {field} mismatch")
    if document["risc0_skip_build_kernels"] is not False:
        raise PrerequisiteError(
            "cuda_build_invalid", "CUDA build kernel-skip flag must be exact false"
        )
    for field in (
        "cargo_lock_sha256",
        "dependency_source_root",
        "builder_image_sha256",
        "runtime_dependency_root",
        "source_archive_root",
    ):
        require_sha256(document[field], f"CUDA build {field}", nonzero=True)
    for field in (
        "cuda_toolkit_version",
        "nvcc_version",
        "host_target",
        "linker_identity",
    ):
        require_bounded_text(document[field], f"CUDA build {field}")
    flags = require_string_list(document["nvcc_flags"], "NVCC flags", maximum=32)
    if flags != ["--generate-code", "arch=compute_90,code=sm_90"]:
        raise PrerequisiteError("cuda_build_invalid", "CUDA build does not exactly target sm_90")
    require_artifact(document["output_r0vm"], "CUDA output r0vm")
    require_false_authority(document["authority"], "CUDA build authority")
    require_sha256(document["build_attestation_id"], "CUDA build attestation ID", nonzero=True)
    if document["build_attestation_id"] != derive_build_attestation_id(document):
        raise PrerequisiteError("cuda_build_id_mismatch", "CUDA build attestation ID mismatch")


def validate_preflight_document(document: dict[str, object], current_epoch: int) -> None:
    require_ordered_fields(document, PREFLIGHT_FIELDS, "H100 preflight")
    if document["schema"] != PREFLIGHT_SCHEMA or document["status"] != PREFLIGHT_STATUS:
        raise PrerequisiteError(
            "h100_preflight_invalid", "H100 preflight schema or status mismatch"
        )
    observed = require_u64(document["observed_at_epoch_seconds"], "H100 observed epoch")
    valid_until = require_u64(document["valid_until_epoch_seconds"], "H100 valid-until epoch")
    if observed > current_epoch or current_epoch > valid_until:
        raise PrerequisiteError("h100_preflight_stale", "H100 preflight is not current")
    if valid_until - observed > MAX_PREFLIGHT_VALIDITY_SECONDS:
        raise PrerequisiteError("h100_preflight_invalid", "H100 preflight validity exceeds bound")
    gpu = require_gpu(document["gpu"])
    if (
        gpu["model_id"] != H100_MODEL_ID
        or gpu["compute_capability_major"] != 9
        or gpu["compute_capability_minor"] != 0
        or require_positive_u64(gpu["memory_total_bytes"], "GPU memory") < H100_MIN_MEMORY_BYTES
    ):
        raise PrerequisiteError("h100_preflight_invalid", "H100 hardware profile mismatch")
    require_artifact(document["r0vm"], "H100 preflight r0vm")
    require_sha256(document["runtime_image_sha256"], "runtime image", nonzero=True)
    if (
        require_positive_u64(document["visible_device_count"], "visible device count") != 1
        or require_u64(document["visible_device_ordinal"], "visible device ordinal") != 0
        or document["cuda_visible_devices"] != "0"
    ):
        raise PrerequisiteError("h100_preflight_invalid", "single visible GPU policy mismatch")
    require_false_authority(document["authority"], "H100 preflight authority")
    require_sha256(document["h100_preflight_id"], "H100 preflight ID", nonzero=True)
    if document["h100_preflight_id"] != derive_h100_preflight_id(document):
        raise PrerequisiteError("h100_preflight_id_mismatch", "H100 preflight ID mismatch")


def canonical_bytes(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def derive_build_attestation_id(document: dict[str, object]) -> str:
    return derive_record_id(document, "build_attestation_id", BUILD_ID_DOMAIN)


def derive_h100_preflight_id(document: dict[str, object]) -> str:
    return derive_record_id(document, "h100_preflight_id", PREFLIGHT_ID_DOMAIN)


def derive_segment_shape_sha256(segments: object) -> str:
    payload = canonical_bytes(segments)
    return hashlib.sha256(
        SEGMENT_SHAPE_DOMAIN + len(payload).to_bytes(8, "big") + payload
    ).hexdigest()


def execution_shape(profile: dict[str, object]) -> dict[str, object]:
    return {
        "segment_limit_po2": profile["segment_limit_po2"],
        "segment_shape_sha256": derive_segment_shape_sha256(profile["segments"]),
        "segment_count": profile["segment_count"],
        "total_user_cycles": profile["total_user_cycles"],
        "total_padded_cycle_capacity": profile["total_padded_cycle_capacity"],
    }


def load_canonical_record(path: Path, label: str) -> LoadedRecord:
    raw = stable_read(path, label, MAX_INPUT_BYTES)
    document = strict_json(raw, label)
    if canonical_bytes(document) != raw:
        raise PrerequisiteError("noncanonical_json", f"{label} JSON is not canonical")
    return LoadedRecord(raw=raw, sha256=hashlib.sha256(raw).hexdigest(), document=document)


def strict_json(raw: bytes, label: str) -> dict[str, object]:
    try:
        text = raw.decode("utf-8", errors="strict")
        value = json.loads(
            text,
            object_pairs_hook=pairs_without_duplicates,
            parse_float=reject_noninteger,
            parse_constant=reject_noninteger,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, PrerequisiteError) as exc:
        raise PrerequisiteError("json_decode_failed", f"{label} JSON decode failed") from exc
    return require_object(value, label)


def pairs_without_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise PrerequisiteError("duplicate_json_key", "duplicate JSON object key")
        result[key] = value
    return result


def reject_noninteger(value: str) -> NoReturn:
    raise PrerequisiteError("noninteger_json_number", f"non-integer JSON number: {value}")


def stable_read(path: Path, label: str, maximum: int) -> bytes:
    try:
        before = path.lstat()
    except OSError as exc:
        raise PrerequisiteError("required_input_unreadable", f"{label} metadata failed") from exc
    if (
        not stat.S_ISREG(before.st_mode)
        or stat.S_ISLNK(before.st_mode)
        or not 0 < before.st_size <= maximum
    ):
        raise PrerequisiteError("required_input_invalid", f"{label} is not a bounded regular file")
    chunks: list[bytes] = []
    total = 0
    try:
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            if not same_file_version(before, opened):
                raise PrerequisiteError("input_race", f"{label} changed while opened")
            while True:
                chunk = handle.read(min(1024 * 1024, maximum - total + 1))
                if not chunk:
                    break
                total += len(chunk)
                if total > maximum:
                    raise PrerequisiteError("required_input_invalid", f"{label} exceeds byte bound")
                chunks.append(chunk)
            after = os.fstat(handle.fileno())
    except OSError as exc:
        raise PrerequisiteError("required_input_unreadable", f"{label} read failed") from exc
    if not same_file_version(opened, after) or total != opened.st_size:
        raise PrerequisiteError("input_race", f"{label} changed while read")
    return b"".join(chunks)


def same_file_version(left: os.stat_result, right: os.stat_result) -> bool:
    return (
        left.st_dev,
        left.st_ino,
        left.st_mode,
        left.st_size,
        left.st_mtime_ns,
        left.st_ctime_ns,
    ) == (
        right.st_dev,
        right.st_ino,
        right.st_mode,
        right.st_size,
        right.st_mtime_ns,
        right.st_ctime_ns,
    )


def derive_record_id(document: dict[str, object], field: str, domain: bytes) -> str:
    candidate = copy.deepcopy(document)
    if field not in candidate:
        raise PrerequisiteError("record_id_field_missing", f"{field} is missing")
    candidate[field] = ZERO_SHA256
    payload = canonical_bytes(candidate)
    return hashlib.sha256(domain + len(payload).to_bytes(8, "big") + payload).hexdigest()


def require_ordered_fields(row: dict[str, object], fields: list[str], label: str) -> None:
    if list(row) != fields:
        raise PrerequisiteError(
            "field_inventory_mismatch", f"{label} field order or inventory mismatch"
        )


def require_object(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        raise PrerequisiteError("type_mismatch", f"{label} must be an object")
    return value


def require_artifact(value: object, label: str) -> dict[str, object]:
    row = require_object(value, label)
    require_ordered_fields(row, ARTIFACT_FIELDS, label)
    require_sha256(row["sha256"], f"{label} SHA-256", nonzero=True)
    require_positive_u64(row["size_bytes"], f"{label} size")
    return row


def require_gpu(value: object) -> dict[str, object]:
    row = require_object(value, "GPU")
    require_ordered_fields(row, GPU_FIELDS, "GPU")
    require_identifier(row["model_id"], "GPU model ID")
    uuid = require_bounded_text(row["uuid"], "GPU UUID")
    if re.fullmatch(r"GPU-[A-Za-z0-9-]{8,96}", uuid) is None:
        raise PrerequisiteError("h100_preflight_invalid", "GPU UUID is not canonical")
    require_bounded_text(row["name"], "GPU name")
    require_u64(row["compute_capability_major"], "compute capability major")
    require_u64(row["compute_capability_minor"], "compute capability minor")
    require_positive_u64(row["memory_total_bytes"], "GPU memory")
    require_bounded_text(row["driver_version"], "GPU driver version")
    return row


def require_false_authority(value: object, label: str) -> None:
    row = require_object(value, label)
    require_ordered_fields(row, AUTHORITY_FIELDS, label)
    if row != AUTHORITY_FALSE or any(type(row[field]) is not bool for field in AUTHORITY_FIELDS):
        raise PrerequisiteError("authority_promotion_rejected", f"{label} must remain false")


def require_identifier(value: object, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[a-z0-9_./-]{1,128}", value) is None:
        raise PrerequisiteError("identifier_invalid", f"{label} is not a canonical identifier")
    return value


def require_bounded_text(value: object, label: str) -> str:
    if type(value) is not str or not 1 <= len(value.encode("utf-8")) <= 256:
        raise PrerequisiteError("text_invalid", f"{label} is not bounded text")
    return value


def require_string_list(value: object, label: str, *, maximum: int) -> list[str]:
    if type(value) is not list or not 1 <= len(value) <= maximum:
        raise PrerequisiteError("list_invalid", f"{label} is empty or oversized")
    return [
        require_bounded_text(item, f"{label} item {ordinal}") for ordinal, item in enumerate(value)
    ]


def require_sha256(value: object, label: str, *, nonzero: bool) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise PrerequisiteError("digest_invalid", f"{label} is not lowercase SHA-256")
    if nonzero and value == ZERO_SHA256:
        raise PrerequisiteError("digest_invalid", f"{label} is zero")
    return value


def require_u64(value: object, label: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise PrerequisiteError("integer_out_of_range", f"{label} is outside u64")
    return value


def require_positive_u64(value: object, label: str) -> int:
    result = require_u64(value, label)
    if result == 0:
        raise PrerequisiteError("integer_out_of_range", f"{label} must be positive")
    return result
