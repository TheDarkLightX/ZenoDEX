#!/usr/bin/env python3
"""Run one authority-false V6 settlement benchmark on Apple Silicon.

The task supplies immutable Linux-built RISC0 guest programs and the completed
local L2 receipt.  This worker builds only the native host harness, verifies all
task bytes before use, and records a bounded candidate result.  It never grants
release, settlement, ledger, or production authority.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import platform
import resource
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Mapping, Sequence

TASK_SCHEMA = "zenodex/zrpf_v6_darwin_settlement_benchmark_task/v1"
PREBUILT_METHODS_SCHEMA = "zenodex/zrpf_spot_v6_prebuilt_methods/v1"
REPORT_SCHEMA = "zenodex/zrpf_v6_darwin_settlement_benchmark_report/v1"
SETTLEMENT_REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1"
HOST_RUST_TOOLCHAIN = "1.94.1"
EXPECTED_RUSTC_VERSION = "rustc 1.94.1 (e408947bf 2026-03-25)"
EXPECTED_CARGO_VERSION = "cargo 1.94.1 (29ea6fb6a 2026-03-24)"
EXPECTED_R0VM_VERSION = "risc0-r0vm 3.0.5"
EXPECTED_CARGO_RISCZERO_VERSION = "cargo-risczero 3.0.5"
TASK_INPUT_KEYS = ("source_envelope", "l2_receipt")
PROGRAM_ROLES = ("level_two", "settlement")
PROGRAM_ARTIFACTS = {
    "level_two": "spot_value_aggregate_l2_v6.bin",
    "settlement": "source_opened_spot_settlement_v6.bin",
}
ARTIFACT_NAMES = (
    "settlement_receipt.json",
    "settlement_admission_journal.bin",
    "settlement_mutation_receipt.json",
    "settlement_guest_input.bin",
    "settlement_replay.bin",
    "settlement_da_certificate.bin",
)
AUTHORITY_CLAIMS = (
    "cross_host_reproducible_build",
    "proof_generation_reproducible",
    "proof_authority",
    "release_authority",
    "settlement_authority",
    "production_authority",
)
NONCLAIMS = (
    "this Darwin benchmark is candidate performance evidence only",
    "the prebuilt Linux guest programs are not rebuilt or promoted by this worker",
    "the generated receipt grants no ledger, settlement, release, or production authority",
    "the native host process is not a Firecracker or production sandbox",
)
EXECUTABLE_ARTIFACT_LIMIT = 256 * 1024 * 1024
MAX_TASK_BYTES = 256 * 1024
MAX_INPUT_BYTES = 16 * 1024 * 1024
MAX_PROGRAM_BYTES = 16 * 1024 * 1024
MAX_SUPPORTING_ARTIFACT_BYTES = 16 * 1024 * 1024
GUEST_BUILD_RECORD_PATH = "provenance/guest-build-record.json"
LOCAL_CHAIN_PATHS = (
    "local-chain/manifest.json",
    "local-chain/leaf.receipt.json",
    "local-chain/leaf.report.json",
    "local-chain/l1.receipt.json",
    "local-chain/l1.report.json",
    "local-chain/l2.report.json",
    "local-chain/linux-cpu-timing-summary.json",
)
EXACT_TASK_KEYS = {
    "schema",
    "task_id",
    "worker_source",
    "guest_build_record",
    "local_chain_artifacts",
    "workspace",
    "toolchain",
    "limits",
    "inputs",
    "programs",
    "expected_output_inventory",
    "claims",
    "nonclaims",
}
WORKER_GOVERNED_TREE_ROOTS = (
    "tools/run_zrpf_source_opened_spot_v6_darwin_settlement_benchmark.py",
    # The host harness reaches local path dependencies through zrpf_protocol
    # and state_proof_risc0.  Pinning the complete ZK tree avoids an incomplete
    # hand-maintained transitive-path allowlist.
    "zk",
)
EXECUTABLE_ROLES = ("harness", "r0vm")
TOOL_OBSERVATION_FIELDS = (
    "host_target",
    "rustc_version",
    "cargo_version",
    "r0vm_version",
    "cargo_risczero_version",
)
SETTLEMENT_REPORT_KEYS = {
    "action_count",
    "admission_journal_bytes",
    "admission_journal_sha256",
    "consumed_object_count",
    "data_availability_certificate_bytes",
    "data_availability_certificate_sha256",
    "guest_input_bytes",
    "guest_input_sha256",
    "image_id",
    "l2_receipt_sha256",
    "mutation_receipt_sha256",
    "mutation_rejected",
    "nonclaims",
    "ok",
    "receipt_bytes",
    "receipt_sha256",
    "replay_bytes",
    "replay_sha256",
    "schema",
    "settlement_claim_binding",
    "settlement_program_id",
    "settlement_program_manifest_root",
    "source_envelope_sha256",
    "status",
    "succinct_receipt_profile_id",
}
SETTLEMENT_NONCLAIMS = (
    "the accepted source receipt does not establish an end-user signature scheme",
    "this local receipt grants no release, governance, Tau-finality, or production authority",
)
SETTLEMENT_STATUS = "source_opened_spot_settlement_v6_succinct_receipt_verified"
SETTLEMENT_PROFILE = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
WORKER_REPORT_KEYS = {
    "artifacts",
    "cargo_build_stderr_sha256",
    "children_max_rss_observation_bytes",
    "elapsed_milliseconds",
    "executable_identities",
    "firecracker_executed",
    "nonclaims",
    "ok",
    "sandbox_authority",
    "schema",
    "settlement_report_bytes",
    "settlement_report_sha256",
    "status",
    "task_id",
    "task_manifest_sha256",
    "tool_observations",
    *AUTHORITY_CLAIMS,
}


class WorkerError(RuntimeError):
    """A stable fail-closed benchmark rejection."""


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str
    size_bytes: int
    absolute_path: Path
    image_id: str | None = None


@dataclass(frozen=True)
class Task:
    document: dict[str, object]
    task_id: str
    manifest_path: Path
    root: Path
    inputs: Mapping[str, Artifact]
    programs: Mapping[str, Artifact]
    guest_build_record: Artifact
    local_chain_artifacts: Mapping[str, Artifact]


def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise WorkerError(f"duplicate JSON key rejected: {key}")
        result[key] = value
    return result


def _canonical_json(value: object) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _reject_json_constant(value: str) -> None:
    raise WorkerError(f"non-finite JSON number rejected: {value}")


def _decode_json_object(raw: bytes, label: str) -> dict[str, object]:
    try:
        value = json.loads(
            raw,
            object_pairs_hook=_reject_duplicate_pairs,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise WorkerError(f"{label} JSON rejected: {error}") from error
    if not isinstance(value, dict):
        raise WorkerError(f"{label} must be a JSON object")
    return value


def _decode_exact_json(raw: bytes, label: str) -> dict[str, object]:
    value = _decode_json_object(raw, label)
    if raw != _canonical_json(value):
        raise WorkerError(f"{label} must use canonical JSON bytes")
    return value


def _stable_read(
    path: Path, *, label: str, maximum_bytes: int, allow_empty: bool = False
) -> bytes:
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise WorkerError(f"{label} cannot be opened safely: {error}") from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise WorkerError(f"{label} must be a regular file")
        minimum_size = 0 if allow_empty else 1
        if before.st_size < minimum_size or before.st_size > maximum_bytes:
            raise WorkerError(f"{label} has an unsupported size")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise WorkerError(f"{label} changed while being read")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise WorkerError(f"{label} exceeded its recorded size")
        after = os.fstat(descriptor)
        identity_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if identity_before != identity_after:
            raise WorkerError(f"{label} changed while being read")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _require_exact_keys(value: Mapping[str, object], expected: set[str], label: str) -> None:
    if set(value) != expected:
        raise WorkerError(f"{label} fields differ from the governed schema")


def _require_object(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise WorkerError(f"{label} must be an object")
    return value


def _require_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise WorkerError(f"{label} must be a nonempty string")
    return value


def _require_int(value: object, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise WorkerError(f"{label} must be an integer")
    if value < minimum or value > maximum:
        raise WorkerError(f"{label} is outside the governed bounds")
    return value


def _recorded_int(value: Mapping[str, object], field: str) -> int:
    candidate = value[field]
    if isinstance(candidate, bool) or not isinstance(candidate, int):
        raise WorkerError(f"recorded integer became invalid: {field}")
    return candidate


def _canonical_darwin_host_target(machine: str) -> str:
    if machine in {"arm64", "aarch64"}:
        return "aarch64-apple-darwin"
    raise WorkerError("this live worker requires Apple Silicon Darwin")


def _is_apple_silicon_darwin() -> bool:
    return sys.platform == "darwin" and platform.machine() in {"arm64", "aarch64"}


def _require_hex(value: object, label: str, length: int) -> str:
    text = _require_string(value, label)
    if len(text) != length or any(character not in "0123456789abcdef" for character in text):
        raise WorkerError(f"{label} must be {length} lowercase hexadecimal characters")
    return text


def _safe_relative_path(value: object, expected: str, label: str) -> str:
    text = _require_string(value, label)
    path = Path(text)
    if text != expected or path.is_absolute() or ".." in path.parts:
        raise WorkerError(f"{label} differs from the governed relative path")
    return text


def _artifact_from_record(
    root: Path,
    value: object,
    *,
    expected_path: str,
    label: str,
    maximum_bytes: int,
    image_id_required: bool = False,
) -> Artifact:
    record = _require_object(value, label)
    expected_keys = {"path", "sha256", "size_bytes"}
    if image_id_required:
        expected_keys |= {"role", "image_id"}
    _require_exact_keys(record, expected_keys, label)
    path_text = _safe_relative_path(record["path"], expected_path, f"{label}.path")
    sha256 = _require_hex(record["sha256"], f"{label}.sha256", 64)
    size_bytes = _require_int(record["size_bytes"], f"{label}.size_bytes", 1, maximum_bytes)
    image_id: str | None = None
    if image_id_required:
        image_id = _require_hex(record["image_id"], f"{label}.image_id", 64)
        if image_id == "0" * 64:
            raise WorkerError(f"{label}.image_id cannot be the zero sentinel")
    absolute = root.joinpath(*Path(path_text).parts)
    raw = _stable_read(absolute, label=label, maximum_bytes=maximum_bytes)
    if len(raw) != size_bytes:
        raise WorkerError(f"{label} size differs from its task record")
    if hashlib.sha256(raw).hexdigest() != sha256:
        raise WorkerError(f"{label} SHA-256 differs from its task record")
    return Artifact(path_text, sha256, size_bytes, absolute, image_id)


def derive_task_id(document: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(document))
    candidate["task_id"] = "0" * 64
    return hashlib.sha256(
        b"zenodex/zrpf_v6_darwin_settlement_benchmark_task_id/v1\0" + _canonical_json(candidate)
    ).hexdigest()


def _run_git(repo: Path, arguments: Sequence[str]) -> subprocess.CompletedProcess[bytes]:
    environment = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": str(repo),
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_NO_REPLACE_OBJECTS": "1",
        "LC_ALL": "C",
    }
    return subprocess.run(
        ["git", "--no-pager", *arguments],
        cwd=repo,
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )


def _worker_tree_listing(repo: Path, commit: str) -> tuple[str, int]:
    result = _run_git(
        repo,
        ["ls-tree", "-r", "-z", commit, "--", *WORKER_GOVERNED_TREE_ROOTS],
    )
    if result.returncode or not result.stdout or len(result.stdout) > 16 * 1024 * 1024:
        raise WorkerError("worker governed source tree listing is unavailable")
    entries = [entry for entry in result.stdout.split(b"\0") if entry]
    if len(entries) > 16_384:
        raise WorkerError("worker governed source tree has too many entries")
    for entry in entries:
        if b"\t" not in entry or not entry.startswith(b"100"):
            raise WorkerError("worker governed source tree contains an unsupported entry")
    digest = hashlib.sha256(
        b"zenodex/zrpf_v6_darwin_worker_repository_source_tree/v1\0" + result.stdout
    ).hexdigest()
    return digest, len(entries)


def _verify_worker_checkout(document: Mapping[str, object], repo: Path) -> None:
    source = _require_object(document["worker_source"], "worker_source")
    commit = _require_hex(source["commit"], "worker_source.commit", 40)
    tree = _require_hex(source["tree"], "worker_source.tree", 40)
    observed_tree = _run_git(repo, ["show", "-s", "--format=%T", commit])
    if observed_tree.returncode or observed_tree.stdout.strip().decode() != tree:
        raise WorkerError("worker source commit/tree is unavailable or mismatched")
    observed_listing_sha256, observed_file_count = _worker_tree_listing(repo, commit)
    if observed_listing_sha256 != source["governed_tree_listing_sha256"]:
        raise WorkerError("worker governed source tree digest mismatch")
    if observed_file_count != source["governed_file_count"]:
        raise WorkerError("worker governed source tree file count mismatch")
    diff = _run_git(repo, ["diff", "--quiet", commit, "--", *WORKER_GOVERNED_TREE_ROOTS])
    if diff.returncode != 0:
        raise WorkerError("worker-governed source differs from the pinned source commit")
    status = _run_git(
        repo,
        [
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--",
            *WORKER_GOVERNED_TREE_ROOTS,
        ],
    )
    if status.returncode or status.stdout:
        raise WorkerError("worker-governed source has local modifications")


def load_task(manifest_path: Path, *, verify_checkout: bool = True) -> Task:
    manifest_path = manifest_path.resolve(strict=True)
    raw = _stable_read(manifest_path, label="task manifest", maximum_bytes=MAX_TASK_BYTES)
    document = _decode_exact_json(raw, "task manifest")
    _require_exact_keys(document, EXACT_TASK_KEYS, "task manifest")
    if document["schema"] != TASK_SCHEMA:
        raise WorkerError("task schema mismatch")
    task_id = _require_hex(document["task_id"], "task_id", 64)
    if task_id != derive_task_id(document):
        raise WorkerError("task_id does not bind the canonical task")

    source = _require_object(document["worker_source"], "worker_source")
    _require_exact_keys(
        source,
        {"commit", "tree", "governed_tree_listing_sha256", "governed_file_count"},
        "worker_source",
    )
    _require_hex(source["commit"], "worker_source.commit", 40)
    _require_hex(source["tree"], "worker_source.tree", 40)
    _require_hex(
        source["governed_tree_listing_sha256"],
        "worker_source.governed_tree_listing_sha256",
        64,
    )
    _require_int(
        source["governed_file_count"], "worker_source.governed_file_count", 1, 16_384
    )

    workspace = _require_object(document["workspace"], "workspace")
    _require_exact_keys(
        workspace,
        {"cargo_lock_sha256", "manifest_path", "package", "features"},
        "workspace",
    )
    _require_hex(workspace["cargo_lock_sha256"], "workspace.cargo_lock_sha256", 64)
    if workspace["manifest_path"] != "zk/zrpf_risc0/Cargo.toml":
        raise WorkerError("workspace manifest path mismatch")
    if workspace["package"] != "zenodex-zrpf-risc0-harness":
        raise WorkerError("workspace package mismatch")
    if workspace["features"] != ["spot-v6-methods"]:
        raise WorkerError("workspace feature set mismatch")

    toolchain = _require_object(document["toolchain"], "toolchain")
    _require_exact_keys(
        toolchain,
        {
            "host_target",
            "risc0_zkvm_version",
            "r0vm_version",
            "cargo_risczero_version",
            "rustc_version",
            "cargo_version",
        },
        "toolchain",
    )
    if toolchain["host_target"] != "aarch64-apple-darwin":
        raise WorkerError("task is not pinned to Apple Silicon Darwin")
    if toolchain["risc0_zkvm_version"] != "3.0.5":
        raise WorkerError("RISC0 zkVM task version mismatch")
    for field in ("r0vm_version", "cargo_risczero_version", "rustc_version", "cargo_version"):
        _require_string(toolchain[field], f"toolchain.{field}")
    if toolchain["rustc_version"] != EXPECTED_RUSTC_VERSION:
        raise WorkerError("host rustc task version mismatch")
    if toolchain["cargo_version"] != EXPECTED_CARGO_VERSION:
        raise WorkerError("host Cargo task version mismatch")
    if toolchain["r0vm_version"] != EXPECTED_R0VM_VERSION:
        raise WorkerError("host r0vm task version mismatch")
    if toolchain["cargo_risczero_version"] != EXPECTED_CARGO_RISCZERO_VERSION:
        raise WorkerError("host cargo-risczero task version mismatch")

    limits = _require_object(document["limits"], "limits")
    limit_bounds = {
        "build_timeout_seconds": (60, 14_400),
        "stage_timeout_seconds": (60, 172_800),
        "max_virtual_address_space_bytes": (1024**3, 256 * 1024**3),
        "max_output_capture_bytes": (1024, 4 * 1024**2),
        "max_stage_artifact_bytes": (1024, 256 * 1024**2),
        "max_total_candidate_artifact_bytes": (1024, 1024**3),
        "max_open_files": (32, 65_536),
        "max_processes": (32, 65_536),
    }
    _require_exact_keys(limits, set(limit_bounds), "limits")
    for field, bounds in limit_bounds.items():
        _require_int(limits[field], f"limits.{field}", *bounds)

    root = manifest_path.parent
    input_records = _require_object(document["inputs"], "inputs")
    _require_exact_keys(input_records, set(TASK_INPUT_KEYS), "inputs")
    inputs = {
        "source_envelope": _artifact_from_record(
            root,
            input_records["source_envelope"],
            expected_path="inputs/leaf_source_envelope.bin",
            label="source_envelope",
            maximum_bytes=MAX_INPUT_BYTES,
        ),
        "l2_receipt": _artifact_from_record(
            root,
            input_records["l2_receipt"],
            expected_path="inputs/l2_receipt.json",
            label="l2_receipt",
            maximum_bytes=MAX_INPUT_BYTES,
        ),
    }

    program_records = document["programs"]
    if not isinstance(program_records, list) or len(program_records) != len(PROGRAM_ROLES):
        raise WorkerError("programs must contain the exact two governed roles")
    programs: dict[str, Artifact] = {}
    for record, expected_role in zip(program_records, PROGRAM_ROLES, strict=True):
        record_object = _require_object(record, f"programs.{expected_role}")
        if record_object.get("role") != expected_role:
            raise WorkerError("program role order mismatch")
        artifact = _artifact_from_record(
            root,
            record_object,
            expected_path=f"programs/{PROGRAM_ARTIFACTS[expected_role]}",
            label=f"programs.{expected_role}",
            maximum_bytes=MAX_PROGRAM_BYTES,
            image_id_required=True,
        )
        if not _stable_read(
            artifact.absolute_path,
            label=f"programs.{expected_role}",
            maximum_bytes=MAX_PROGRAM_BYTES,
        ).startswith(b"R0BF"):
            raise WorkerError(f"programs.{expected_role} lacks R0BF framing")
        programs[expected_role] = artifact

    guest_build_record = _artifact_from_record(
        root,
        document["guest_build_record"],
        expected_path=GUEST_BUILD_RECORD_PATH,
        label="guest_build_record",
        maximum_bytes=MAX_SUPPORTING_ARTIFACT_BYTES,
    )
    guest_record = _decode_json_object(
        _stable_read(
            guest_build_record.absolute_path,
            label="guest_build_record",
            maximum_bytes=MAX_SUPPORTING_ARTIFACT_BYTES,
        ),
        "guest_build_record",
    )
    if guest_record.get("schema") != "zenodex/zrpf_source_opened_spot_v6_build_record/v3":
        raise WorkerError("guest build record schema mismatch")
    guest_programs = guest_record.get("programs")
    if not isinstance(guest_programs, list):
        raise WorkerError("guest build record program inventory mismatch")
    guest_program_by_stage = {
        row.get("stage"): row for row in guest_programs if isinstance(row, dict)
    }
    for role, stage in (("level_two", "spot_value_aggregate_l2_v6"), ("settlement", "source_opened_spot_settlement_v6")):
        row = _require_object(guest_program_by_stage.get(stage), f"guest build record {stage}")
        artifact = programs[role]
        if (
            row.get("program_binary_sha256") != artifact.sha256
            or row.get("program_binary_bytes") != artifact.size_bytes
            or row.get("image_id_hex") != artifact.image_id
        ):
            raise WorkerError(f"guest build record does not bind programs.{role}")

    local_chain_records = document["local_chain_artifacts"]
    if not isinstance(local_chain_records, list) or len(local_chain_records) != len(
        LOCAL_CHAIN_PATHS
    ):
        raise WorkerError("local chain artifact inventory mismatch")
    local_chain_artifacts: dict[str, Artifact] = {}
    for record, expected_path in zip(local_chain_records, LOCAL_CHAIN_PATHS, strict=True):
        local_chain_artifacts[expected_path] = _artifact_from_record(
            root,
            record,
            expected_path=expected_path,
            label=f"local chain artifact {expected_path}",
            maximum_bytes=MAX_SUPPORTING_ARTIFACT_BYTES,
        )
    local_chain_manifest = _decode_exact_json(
        _stable_read(
            local_chain_artifacts["local-chain/manifest.json"].absolute_path,
            label="local chain manifest",
            maximum_bytes=MAX_SUPPORTING_ARTIFACT_BYTES,
        ),
        "local chain manifest",
    )
    if local_chain_manifest.get("schema") != "zenodex/zrpf_v6_local_candidate_chain_manifest/v1":
        raise WorkerError("local chain manifest schema mismatch")
    completed_tip = _require_object(
        local_chain_manifest.get("completed_chain_tip"), "local chain completed tip"
    )
    if (
        completed_tip.get("stage") != "level_two"
        or completed_tip.get("image_id") != programs["level_two"].image_id
        or completed_tip.get("receipt_sha256") != inputs["l2_receipt"].sha256
    ):
        raise WorkerError("local chain completed tip does not bind the task L2 receipt")
    manifest_inventory = local_chain_manifest.get("artifacts")
    expected_manifest_paths = (
        "inputs/leaf_source_envelope.bin",
        "local-chain/leaf.receipt.json",
        "local-chain/leaf.report.json",
        "local-chain/l1.receipt.json",
        "local-chain/l1.report.json",
        "inputs/l2_receipt.json",
        "local-chain/l2.report.json",
        "local-chain/linux-cpu-timing-summary.json",
    )
    if not isinstance(manifest_inventory, list) or len(manifest_inventory) != len(
        expected_manifest_paths
    ):
        raise WorkerError("local chain manifest artifact inventory mismatch")
    available_artifacts = {
        inputs["source_envelope"].path: inputs["source_envelope"],
        inputs["l2_receipt"].path: inputs["l2_receipt"],
        **local_chain_artifacts,
    }
    for row, expected_path in zip(manifest_inventory, expected_manifest_paths, strict=True):
        record = _require_object(row, f"local chain manifest artifact {expected_path}")
        artifact = available_artifacts[expected_path]
        if (
            record.get("path") != expected_path
            or record.get("sha256") != artifact.sha256
            or record.get("size_bytes") != artifact.size_bytes
        ):
            raise WorkerError(f"local chain manifest artifact mismatch: {expected_path}")

    if document["expected_output_inventory"] != list(ARTIFACT_NAMES):
        raise WorkerError("expected output inventory mismatch")
    claims = _require_object(document["claims"], "claims")
    _require_exact_keys(claims, set(AUTHORITY_CLAIMS), "claims")
    if any(type(claims[field]) is not bool or claims[field] for field in AUTHORITY_CLAIMS):
        raise WorkerError("every task authority claim must be exactly false")
    if document["nonclaims"] != list(NONCLAIMS):
        raise WorkerError("task nonclaims mismatch")

    if verify_checkout:
        if not _is_apple_silicon_darwin():
            raise WorkerError("this live worker requires Apple Silicon Darwin")
        repo = _find_repo_root(Path.cwd())
        _verify_worker_checkout(document, repo)
        cargo_lock = repo / "zk/zrpf_risc0/Cargo.lock"
        cargo_lock_raw = _stable_read(
            cargo_lock, label="workspace Cargo.lock", maximum_bytes=16 * 1024**2
        )
        if hashlib.sha256(cargo_lock_raw).hexdigest() != workspace["cargo_lock_sha256"]:
            raise WorkerError("workspace Cargo.lock SHA-256 mismatch")
    return Task(
        document,
        task_id,
        manifest_path,
        root,
        inputs,
        programs,
        guest_build_record,
        local_chain_artifacts,
    )


def _find_repo_root(start: Path) -> Path:
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=start,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=10,
    )
    if result.returncode:
        raise WorkerError("worker must run inside a Git checkout")
    return Path(result.stdout.decode().strip()).resolve(strict=True)


def _write_new(path: Path, raw: bytes, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, mode)
    except OSError as error:
        raise WorkerError(f"refuse to replace output {path}: {error}") from error
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise WorkerError(f"short write for {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def write_prebuilt_methods_manifest(task: Task, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, object]] = []
    for role in PROGRAM_ROLES:
        artifact = task.programs[role]
        filename = PROGRAM_ARTIFACTS[role]
        copied = output.parent / filename
        raw = _stable_read(
            artifact.absolute_path,
            label=f"programs.{role}",
            maximum_bytes=MAX_PROGRAM_BYTES,
        )
        _write_new(copied, raw)
        rows.append(
            {
                "file": filename,
                "image_id": artifact.image_id,
                "role": role,
                "sha256": artifact.sha256,
                "size_bytes": artifact.size_bytes,
            }
        )
    value = {
        "profile": "settlement_only_v1",
        "programs": rows,
        "schema": PREBUILT_METHODS_SCHEMA,
    }
    _write_new(output, _canonical_json(value))


def _artifact_inventory(artifacts: Mapping[str, bytes]) -> list[dict[str, object]]:
    if tuple(artifacts) != ARTIFACT_NAMES:
        raise WorkerError("candidate artifact inventory order mismatch")
    return [
        {
            "path": f"artifacts/{name}",
            "sha256": hashlib.sha256(artifacts[name]).hexdigest(),
            "size_bytes": len(artifacts[name]),
        }
        for name in ARTIFACT_NAMES
    ]


def candidate_worker_report(
    *,
    task: Task,
    artifacts: Mapping[str, bytes],
    settlement_report: bytes,
    elapsed_milliseconds: int,
    children_max_rss_observation_bytes: int,
    cargo_build_stderr_sha256: str,
    executable_identities: Mapping[str, Mapping[str, object]],
    tool_observations: Mapping[str, str],
) -> dict[str, object]:
    if set(executable_identities) != set(EXECUTABLE_ROLES):
        raise WorkerError("executable identity inventory mismatch")
    if set(tool_observations) != set(TOOL_OBSERVATION_FIELDS):
        raise WorkerError("tool observation inventory mismatch")
    report: dict[str, object] = {
        "schema": REPORT_SCHEMA,
        "status": "darwin_m3_settlement_benchmark_authority_false",
        "ok": True,
        "task_id": task.task_id,
        "task_manifest_sha256": hashlib.sha256(
            _stable_read(task.manifest_path, label="task manifest", maximum_bytes=MAX_TASK_BYTES)
        ).hexdigest(),
        "artifacts": _artifact_inventory(artifacts),
        "settlement_report_sha256": hashlib.sha256(settlement_report).hexdigest(),
        "settlement_report_bytes": len(settlement_report),
        "elapsed_milliseconds": elapsed_milliseconds,
        # Darwin reports RUSAGE_CHILDREN.ru_maxrss in bytes.  This is the
        # process-family high-water observation across build and proving, not
        # an enforced resident-memory ceiling or a per-process measurement.
        "children_max_rss_observation_bytes": children_max_rss_observation_bytes,
        "cargo_build_stderr_sha256": cargo_build_stderr_sha256,
        "executable_identities": dict(executable_identities),
        "tool_observations": dict(tool_observations),
        "firecracker_executed": False,
        "sandbox_authority": False,
        "nonclaims": list(NONCLAIMS),
    }
    report.update({field: False for field in AUTHORITY_CLAIMS})
    return report


def persist_candidate_bundle_for_test(
    *,
    task: Task,
    output_directory: Path,
    artifacts: Mapping[str, bytes],
    settlement_report: bytes,
    elapsed_milliseconds: int,
    children_max_rss_observation_bytes: int,
    cargo_build_stderr_sha256: str,
    executable_identities: Mapping[str, Mapping[str, object]],
    tool_observations: Mapping[str, str],
) -> None:
    if output_directory.exists():
        raise WorkerError("candidate output directory already exists")
    output_directory.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(
        tempfile.mkdtemp(prefix=f".{output_directory.name}.staging-", dir=output_directory.parent)
    )
    try:
        for name in ARTIFACT_NAMES:
            raw = artifacts[name]
            if not raw:
                raise WorkerError(f"candidate artifact is empty: {name}")
            _write_new(staging / "artifacts" / name, raw)
        _write_new(staging / "settlement.report.json", settlement_report)
        report = candidate_worker_report(
            task=task,
            artifacts=artifacts,
            settlement_report=settlement_report,
            elapsed_milliseconds=elapsed_milliseconds,
            children_max_rss_observation_bytes=children_max_rss_observation_bytes,
            cargo_build_stderr_sha256=cargo_build_stderr_sha256,
            executable_identities=executable_identities,
            tool_observations=tool_observations,
        )
        _write_new(staging / "worker.report.json", _canonical_json(report))
        if output_directory.exists():
            raise WorkerError("candidate output directory appeared during staging")
        os.rename(staging, output_directory)
    except BaseException:
        if staging.exists():
            shutil.rmtree(staging)
        raise


def validate_candidate_bundle(
    output_directory: Path,
    task: Task,
    *,
    semantic_validator: Callable[..., bool],
) -> dict[str, object]:
    expected_root_entries = {"artifacts", "settlement.report.json", "worker.report.json"}
    try:
        observed_root_entries = {entry.name for entry in output_directory.iterdir()}
    except OSError as error:
        raise WorkerError(f"candidate output directory cannot be listed: {error}") from error
    if observed_root_entries != expected_root_entries:
        raise WorkerError("candidate output root inventory mismatch")
    try:
        observed_artifacts = {entry.name for entry in (output_directory / "artifacts").iterdir()}
    except OSError as error:
        raise WorkerError(f"candidate artifact directory cannot be listed: {error}") from error
    if observed_artifacts != set(ARTIFACT_NAMES):
        raise WorkerError("candidate artifact directory inventory mismatch")
    report_raw = _stable_read(
        output_directory / "worker.report.json",
        label="worker report",
        maximum_bytes=MAX_TASK_BYTES,
    )
    report = _decode_exact_json(report_raw, "worker report")
    _require_exact_keys(report, WORKER_REPORT_KEYS, "worker report")
    if report.get("schema") != REPORT_SCHEMA or report.get("task_id") != task.task_id:
        raise WorkerError("worker report identity mismatch")
    task_manifest_sha256 = hashlib.sha256(
        _stable_read(task.manifest_path, label="task manifest", maximum_bytes=MAX_TASK_BYTES)
    ).hexdigest()
    if report.get("task_manifest_sha256") != task_manifest_sha256:
        raise WorkerError("worker report task-manifest binding mismatch")
    if report.get("ok") is not True:
        raise WorkerError("worker report did not accept the candidate benchmark")
    if report.get("status") != "darwin_m3_settlement_benchmark_authority_false":
        raise WorkerError("worker report status mismatch")
    if report.get("nonclaims") != list(NONCLAIMS):
        raise WorkerError("worker report nonclaims mismatch")
    _require_hex(
        report.get("cargo_build_stderr_sha256"),
        "worker report cargo_build_stderr_sha256",
        64,
    )
    _require_int(
        report.get("elapsed_milliseconds"),
        "worker report elapsed_milliseconds",
        0,
        _recorded_int(_require_object(task.document["limits"], "limits"), "stage_timeout_seconds")
        * 1_000,
    )
    _require_int(
        report.get("children_max_rss_observation_bytes"),
        "worker report children_max_rss_observation_bytes",
        0,
        1 << 63,
    )
    observed_tools = _require_object(report.get("tool_observations"), "tool observations")
    _require_exact_keys(observed_tools, set(TOOL_OBSERVATION_FIELDS), "tool observations")
    expected_tools = _require_object(task.document["toolchain"], "toolchain")
    for field in TOOL_OBSERVATION_FIELDS:
        if observed_tools[field] != expected_tools[field]:
            raise WorkerError(f"worker report tool observation mismatch: {field}")
    executable_identities = _require_object(
        report.get("executable_identities"), "executable identities"
    )
    _require_exact_keys(executable_identities, set(EXECUTABLE_ROLES), "executable identities")
    for role in EXECUTABLE_ROLES:
        identity = _require_object(executable_identities[role], f"executable identity {role}")
        _require_exact_keys(identity, {"sha256", "size_bytes"}, f"executable identity {role}")
        _require_hex(identity["sha256"], f"executable identity {role}.sha256", 64)
        _require_int(
            identity["size_bytes"],
            f"executable identity {role}.size_bytes",
            1,
            EXECUTABLE_ARTIFACT_LIMIT,
        )
    for field in AUTHORITY_CLAIMS:
        if report.get(field) is not False:
            raise WorkerError(f"worker report attempted to promote {field}")
    if (
        report.get("sandbox_authority") is not False
        or report.get("firecracker_executed") is not False
    ):
        raise WorkerError("worker report attempted to promote runtime isolation")
    inventory = report.get("artifacts")
    if not isinstance(inventory, list) or len(inventory) != len(ARTIFACT_NAMES):
        raise WorkerError("worker artifact inventory mismatch")
    artifact_bytes: dict[str, bytes] = {}
    for row, name in zip(inventory, ARTIFACT_NAMES, strict=True):
        record = _require_object(row, f"worker artifact {name}")
        _require_exact_keys(record, {"path", "sha256", "size_bytes"}, f"worker artifact {name}")
        if record["path"] != f"artifacts/{name}":
            raise WorkerError("worker artifact path mismatch")
        raw = _stable_read(
            output_directory / "artifacts" / name,
            label=f"candidate artifact {name}",
            maximum_bytes=int(task.document["limits"]["max_stage_artifact_bytes"]),  # type: ignore[index]
        )
        if len(raw) != record["size_bytes"]:
            raise WorkerError(f"candidate artifact size/SHA-256 mismatch: {name}")
        if hashlib.sha256(raw).hexdigest() != record["sha256"]:
            raise WorkerError(f"candidate artifact SHA-256 mismatch: {name}")
        artifact_bytes[name] = raw
    settlement_report = _stable_read(
        output_directory / "settlement.report.json",
        label="settlement report",
        maximum_bytes=int(task.document["limits"]["max_output_capture_bytes"]),  # type: ignore[index]
    )
    if hashlib.sha256(settlement_report).hexdigest() != report.get("settlement_report_sha256"):
        raise WorkerError("settlement report SHA-256 mismatch")
    if len(settlement_report) != report.get("settlement_report_bytes"):
        raise WorkerError("settlement report size mismatch")
    if not semantic_validator(task, artifact_bytes, settlement_report, report):
        raise WorkerError("candidate semantic validation rejected")
    return report


def _command_observation(command: Sequence[str], *, cwd: Path) -> str:
    result = subprocess.run(
        list(command),
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=30,
        env={"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "LC_ALL": "C"},
    )
    if result.returncode:
        raise WorkerError(f"tool observation failed: {' '.join(command)}")
    output = result.stdout.decode("utf-8", errors="strict").strip()
    if not output or len(output) > 512:
        raise WorkerError(f"tool observation has unsupported output: {' '.join(command)}")
    return output


def _tool_observations(repo: Path, task: Task) -> tuple[dict[str, str], Path]:
    r0vm_path_text = shutil.which("r0vm")
    if r0vm_path_text is None:
        raise WorkerError("r0vm is unavailable on PATH")
    r0vm_path = Path(r0vm_path_text).resolve(strict=True)
    observations = {
        "host_target": _canonical_darwin_host_target(platform.machine()),
        "rustc_version": _command_observation(
            ["rustc", f"+{HOST_RUST_TOOLCHAIN}", "--version"], cwd=repo
        ),
        "cargo_version": _command_observation(
            ["cargo", f"+{HOST_RUST_TOOLCHAIN}", "--version"], cwd=repo
        ),
        "r0vm_version": _command_observation([str(r0vm_path), "--version"], cwd=repo),
        "cargo_risczero_version": _command_observation(
            ["cargo", f"+{HOST_RUST_TOOLCHAIN}", "risczero", "--version"], cwd=repo
        ),
    }
    expected = _require_object(task.document["toolchain"], "toolchain")
    for field in TOOL_OBSERVATION_FIELDS:
        if observations[field] != expected[field]:
            raise WorkerError(f"observed {field} differs from the task")
    return observations, r0vm_path


def _limit_child(limits: Mapping[str, object]) -> None:
    resource.setrlimit(
        resource.RLIMIT_NOFILE,
        (
            _recorded_int(limits, "max_open_files"),
            _recorded_int(limits, "max_open_files"),
        ),
    )
    if hasattr(resource, "RLIMIT_NPROC"):
        resource.setrlimit(
            resource.RLIMIT_NPROC,
            (
                _recorded_int(limits, "max_processes"),
                _recorded_int(limits, "max_processes"),
            ),
        )
    if hasattr(resource, "RLIMIT_CORE"):
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    if hasattr(resource, "RLIMIT_AS"):
        address_space_limit = _recorded_int(limits, "max_virtual_address_space_bytes")
        resource.setrlimit(resource.RLIMIT_AS, (address_space_limit, address_space_limit))
    if hasattr(resource, "RLIMIT_FSIZE"):
        file_limit = _recorded_int(limits, "max_stage_artifact_bytes")
        resource.setrlimit(resource.RLIMIT_FSIZE, (file_limit, file_limit))
    os.umask(0o077)


def _kill_residual_process_group(process_group_id: int) -> bool:
    try:
        os.killpg(process_group_id, signal.SIGKILL)
    except ProcessLookupError:
        return False
    except OSError as error:
        raise WorkerError(f"cannot terminate residual process group: {error}") from error
    deadline = time.monotonic() + 5
    while True:
        try:
            os.killpg(process_group_id, 0)
        except ProcessLookupError:
            return True
        except OSError as error:
            raise WorkerError(f"cannot inspect residual process group: {error}") from error
        if time.monotonic() >= deadline:
            raise WorkerError("residual process group did not terminate")
        time.sleep(0.01)


def _run_bounded(
    command: Sequence[str],
    *,
    cwd: Path,
    environment: Mapping[str, str],
    timeout_seconds: int,
    capture_limit: int,
    limits: Mapping[str, object],
    capture_root: Path,
    label: str,
    require_stdout: bool,
) -> tuple[bytes, bytes, int]:
    stdout_path = capture_root / f"{label}.stdout"
    stderr_path = capture_root / f"{label}.stderr"
    with stdout_path.open("xb") as stdout_file, stderr_path.open("xb") as stderr_file:
        process = subprocess.Popen(
            list(command),
            cwd=cwd,
            env=dict(environment),
            stdin=subprocess.DEVNULL,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=True,
            preexec_fn=lambda: _limit_child(limits),
        )
        try:
            return_code = process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired as error:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=30)
            _kill_residual_process_group(process.pid)
            raise WorkerError(f"{label} exceeded its governed timeout") from error
        residual_group_killed = _kill_residual_process_group(process.pid)
        observed_max_rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    stdout = _stable_read(
        stdout_path,
        label=f"{label} stdout",
        maximum_bytes=capture_limit,
        allow_empty=not require_stdout,
    )
    stderr = _stable_read(
        stderr_path,
        label=f"{label} stderr",
        maximum_bytes=capture_limit,
        allow_empty=True,
    )
    if return_code != 0:
        excerpt = stderr[-2048:].decode("utf-8", errors="replace")
        raise WorkerError(f"{label} failed with exit {return_code}: {excerpt}")
    if residual_group_killed:
        raise WorkerError(f"{label} left a residual process in its process group")
    # Darwin defines ru_maxrss in bytes.  This live worker rejects other hosts,
    # so no Linux KiB conversion is performed on the authority-false report.
    return stdout, stderr, max(0, observed_max_rss)


def _semantic_candidate_validator(
    task: Task,
    artifacts: Mapping[str, bytes],
    settlement_report: bytes,
    _worker_report: Mapping[str, object],
) -> bool:
    try:
        report = _decode_exact_json(settlement_report, "settlement report")
        _require_exact_keys(report, SETTLEMENT_REPORT_KEYS, "settlement report")
        expected_image = task.programs["settlement"].image_id
        if report["schema"] != SETTLEMENT_REPORT_SCHEMA:
            raise WorkerError("settlement report schema mismatch")
        if report["status"] != SETTLEMENT_STATUS or report["ok"] is not True:
            raise WorkerError("settlement report did not accept the proof")
        if report["image_id"] != expected_image or report["settlement_program_id"] != expected_image:
            raise WorkerError("settlement report program identity mismatch")
        if report["l2_receipt_sha256"] != task.inputs["l2_receipt"].sha256:
            raise WorkerError("settlement report L2 receipt mismatch")
        if report["source_envelope_sha256"] != task.inputs["source_envelope"].sha256:
            raise WorkerError("settlement report source-envelope mismatch")
        if report["mutation_rejected"] is not True:
            raise WorkerError("settlement report mutation was not rejected")
        if report["succinct_receipt_profile_id"] != SETTLEMENT_PROFILE:
            raise WorkerError("settlement report receipt profile mismatch")
        if report["nonclaims"] != list(SETTLEMENT_NONCLAIMS):
            raise WorkerError("settlement report nonclaims mismatch")
        for field in (
            "settlement_claim_binding",
            "settlement_program_manifest_root",
        ):
            if _require_hex(report[field], f"settlement report {field}", 64) == "0" * 64:
                raise WorkerError(f"settlement report {field} cannot be the zero sentinel")
        for field in ("action_count", "consumed_object_count"):
            _require_int(report[field], f"settlement report {field}", 1, 1)
        bindings = (
            ("settlement_receipt.json", "receipt_sha256", "receipt_bytes"),
            (
                "settlement_admission_journal.bin",
                "admission_journal_sha256",
                "admission_journal_bytes",
            ),
            ("settlement_mutation_receipt.json", "mutation_receipt_sha256", None),
            ("settlement_guest_input.bin", "guest_input_sha256", "guest_input_bytes"),
            ("settlement_replay.bin", "replay_sha256", "replay_bytes"),
            (
                "settlement_da_certificate.bin",
                "data_availability_certificate_sha256",
                "data_availability_certificate_bytes",
            ),
        )
        for artifact_name, hash_field, size_field in bindings:
            raw = artifacts[artifact_name]
            if report[hash_field] != hashlib.sha256(raw).hexdigest():
                raise WorkerError(f"settlement report artifact hash mismatch: {artifact_name}")
            if size_field is not None and report[size_field] != len(raw):
                raise WorkerError(f"settlement report artifact size mismatch: {artifact_name}")
    except WorkerError:
        return False
    return True


def run_live(task_path: Path, output_directory: Path) -> dict[str, object]:
    task = load_task(task_path, verify_checkout=True)
    repo = _find_repo_root(Path.cwd())
    observations, r0vm_path = _tool_observations(repo, task)
    limits = _require_object(task.document["limits"], "limits")
    if output_directory.exists():
        raise WorkerError("output directory already exists")
    with tempfile.TemporaryDirectory(prefix="zrpf-v6-mac-benchmark-") as temporary:
        temporary_root = Path(temporary)
        methods_root = temporary_root / "prebuilt-methods"
        methods_manifest = methods_root / "methods.json"
        write_prebuilt_methods_manifest(task, methods_manifest)
        target = temporary_root / "target"
        captures = temporary_root / "captures"
        captures.mkdir(mode=0o700)
        home = temporary_root / "home"
        home.mkdir(mode=0o700)
        environment = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": os.environ.get("HOME", str(home)),
            "LANG": "C",
            "LC_ALL": "C",
            "TZ": "UTC",
            "CARGO_TARGET_DIR": str(target),
            "CARGO_BUILD_JOBS": "4",
            "RISC0_PROVER": "ipc",
            "RISC0_SERVER_PATH": str(r0vm_path),
            "ZRPF_SPOT_V6_PREBUILT_METHODS_MANIFEST": str(methods_manifest),
        }
        build_command = (
            "cargo",
            f"+{HOST_RUST_TOOLCHAIN}",
            "build",
            "--quiet",
            "--locked",
            "--offline",
            "--release",
            "--manifest-path",
            str(repo / "zk/zrpf_risc0/Cargo.toml"),
            "-p",
            "zenodex-zrpf-risc0-harness",
            "--no-default-features",
            "--features",
            "spot-v6-methods",
            "--bin",
            "prove_source_opened_spot_settlement_v6",
        )
        build_stdout, build_stderr, _build_max_rss = _run_bounded(
            build_command,
            cwd=repo,
            environment=environment,
            timeout_seconds=_recorded_int(limits, "build_timeout_seconds"),
            capture_limit=_recorded_int(limits, "max_output_capture_bytes"),
            limits=limits,
            capture_root=captures,
            label="build",
            require_stdout=False,
        )
        if build_stdout:
            raise WorkerError("quiet Cargo build emitted unexpected stdout")
        harness = target / "release/prove_source_opened_spot_settlement_v6"
        harness_raw = _stable_read(
            harness, label="built host harness", maximum_bytes=EXECUTABLE_ARTIFACT_LIMIT
        )
        r0vm_raw = _stable_read(
            r0vm_path, label="r0vm executable", maximum_bytes=EXECUTABLE_ARTIFACT_LIMIT
        )
        stage = temporary_root / "stage"
        stage.mkdir(mode=0o700)
        command = [str(harness)]
        option_map = {
            "--receipt-out": "settlement_receipt.json",
            "--journal-out": "settlement_admission_journal.bin",
            "--mutation-out": "settlement_mutation_receipt.json",
            "--guest-input-out": "settlement_guest_input.bin",
            "--replay-out": "settlement_replay.bin",
            "--da-certificate-out": "settlement_da_certificate.bin",
        }
        for option, name in option_map.items():
            command.extend((option, str(stage / name)))
        command.extend(("--source-envelope", str(task.inputs["source_envelope"].absolute_path)))
        command.extend(("--l2-receipt", str(task.inputs["l2_receipt"].absolute_path)))
        started = time.monotonic_ns()
        stdout, stderr, children_max_rss_observation_bytes = _run_bounded(
            command,
            cwd=repo,
            environment=environment,
            timeout_seconds=_recorded_int(limits, "stage_timeout_seconds"),
            capture_limit=_recorded_int(limits, "max_output_capture_bytes"),
            limits=limits,
            capture_root=captures,
            label="settlement",
            require_stdout=True,
        )
        elapsed_milliseconds = (time.monotonic_ns() - started) // 1_000_000
        if stderr:
            raise WorkerError("settlement harness emitted unexpected stderr")
        settlement_report = stdout
        artifacts: dict[str, bytes] = {}
        total_bytes = 0
        for name in ARTIFACT_NAMES:
            raw = _stable_read(
                stage / name,
                label=f"settlement artifact {name}",
                maximum_bytes=_recorded_int(limits, "max_stage_artifact_bytes"),
            )
            total_bytes += len(raw)
            artifacts[name] = raw
        if total_bytes > _recorded_int(limits, "max_total_candidate_artifact_bytes"):
            raise WorkerError("candidate artifact set exceeds its governed total size")
        if not _semantic_candidate_validator(task, artifacts, settlement_report, {}):
            raise WorkerError("settlement output failed semantic binding validation")
        executable_identities = {
            "harness": {
                "sha256": hashlib.sha256(harness_raw).hexdigest(),
                "size_bytes": len(harness_raw),
            },
            "r0vm": {
                "sha256": hashlib.sha256(r0vm_raw).hexdigest(),
                "size_bytes": len(r0vm_raw),
            },
        }
        persist_candidate_bundle_for_test(
            task=task,
            output_directory=output_directory,
            artifacts=artifacts,
            settlement_report=settlement_report,
            elapsed_milliseconds=elapsed_milliseconds,
            children_max_rss_observation_bytes=children_max_rss_observation_bytes,
            cargo_build_stderr_sha256=hashlib.sha256(build_stderr).hexdigest(),
            executable_identities=executable_identities,
            tool_observations=observations,
        )
    return validate_candidate_bundle(
        output_directory,
        task,
        semantic_validator=_semantic_candidate_validator,
    )


def _parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="validate an existing output bundle")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parse_args(argv)
    try:
        if arguments.check:
            task = load_task(arguments.task, verify_checkout=False)
            report = validate_candidate_bundle(
                arguments.output,
                task,
                semantic_validator=_semantic_candidate_validator,
            )
        else:
            report = run_live(arguments.task, arguments.output)
    except (OSError, subprocess.SubprocessError, WorkerError) as error:
        print(json.dumps({"ok": False, "error": str(error)}, sort_keys=True), file=sys.stderr)
        return 1
    print(_canonical_json(report).decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
