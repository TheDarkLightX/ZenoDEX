#!/usr/bin/env python3
"""Materialize one checked Spot V6 identity rebuild into declared outputs.

This adapter closes the remote handoff's multi-output identity stage. It emits
candidate artifacts only. The rebuilt programs, reports, and task capture grant
no proof, release, settlement, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import stat
import sys
from pathlib import Path, PurePosixPath
from typing import Mapping, Sequence

if __package__ in {None, ""}:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import execute_zrpf_source_opened_spot_v6_identity_rebuild as executor  # noqa: E402
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner  # noqa: E402
from tools.zrpf_remote_reproof_handoff_v2_catalog import IDENTITY_RUN_ROOT  # noqa: E402
from tools.zrpf_v6_identity_docker_runner import (  # noqa: E402
    RISC0_EXTENSION_DIRECTORY,
    DockerBuildRunner,
)
from tools.zrpf_v6_identity_executor_types import (  # noqa: E402
    BuildRunner,
    ExecutionError,
    IncompleteContainerCleanupError,
)

MAX_OUTPUT_BYTES = 64 * 1024 * 1024
MAX_JSON_OUTPUT_BYTES = 4 * 1024 * 1024

PROGRAM_OUTPUT_ROLES = (
    "source_program",
    "v2_adapter_program",
    "v6_leaf_program",
    "v6_l1_program",
    "v6_l2_program",
    "v6_settlement_program",
)
OUTPUT_ROLES = (
    "identity_plan",
    "identity_observations",
    "identity_candidate_report",
    "source_program",
    "source_cli",
    "v2_adapter_program",
    "v6_leaf_program",
    "v6_l1_program",
    "v6_l2_program",
    "v6_settlement_program",
)


class IdentityStageError(ValueError):
    """Stable fail-closed identity-stage rejection."""


def execute_identity_stage(
    *,
    source_commit: str,
    identity_run_root: Path,
    output_paths: Mapping[str, Path],
    runner: BuildRunner,
    repo_root: Path = planner.REPO_ROOT,
) -> None:
    """Run one source-pinned identity rebuild and copy its checked outputs."""

    repository = _canonical_repository(repo_root)
    _validate_source_commit(source_commit)
    run_root = _validate_absent_run_root(identity_run_root, repository)
    outputs = _validate_output_paths(output_paths, repository)
    _require_disjoint_run_and_outputs(run_root, outputs)
    try:
        plan = planner.build_plan(source_commit, run_root.as_posix(), repo_root=repository)
    except planner.RebuildPlanError as exc:
        raise IdentityStageError("source commit or identity plan rejected") from exc
    try:
        observations = executor.execute_plan(
            plan,
            runner=runner,
            repo_root=repository,
        )
        report = planner.check_observations(plan, observations, repo_root=repository)
        payloads = _collect_checked_payloads(plan, observations, report, run_root)
        _write_outputs(outputs, payloads)
        _remove_completed_run_root(run_root)
    except IncompleteContainerCleanupError:
        # The identity executor retains the CID and lease needed for recovery.
        raise
    except (ExecutionError, planner.RebuildPlanError, OSError) as exc:
        raise IdentityStageError("identity rebuild stage rejected") from exc


def require_exact_runtime_r0vm(risc0_home: Path, packet_r0vm: Path) -> None:
    """Bind the external RISC0 runtime tree to the packet's exact r0vm bytes."""

    runtime = risc0_home / "extensions" / RISC0_EXTENSION_DIRECTORY / "r0vm"
    runtime_raw = _stable_read(runtime, "runtime r0vm", MAX_OUTPUT_BYTES)
    packet_raw = _stable_read(packet_r0vm, "packet r0vm", MAX_OUTPUT_BYTES)
    if runtime_raw != packet_raw:
        raise IdentityStageError("runtime r0vm differs from packet snapshot")
    expected = planner.TOOLCHAIN["r0vm_sha256"]
    if hashlib.sha256(runtime_raw).hexdigest() != expected:
        raise IdentityStageError("runtime r0vm differs from governed toolchain")


def _collect_checked_payloads(
    plan: dict[str, object],
    observations: dict[str, object],
    report: dict[str, object],
    run_root: Path,
) -> dict[str, bytes]:
    payloads = {
        "identity_plan": planner.canonical_bytes(plan),
        "identity_observations": planner.canonical_bytes(observations),
        "identity_candidate_report": planner.canonical_bytes(report),
    }
    stages = _object_list(observations.get("stages"), "identity observations stages")
    plan_stages = _object_list(plan.get("stages"), "identity plan stages")
    if len(stages) != len(PROGRAM_OUTPUT_ROLES) or len(plan_stages) != len(stages):
        raise IdentityStageError("identity stage inventory mismatch")
    for role, planned, observed in zip(
        PROGRAM_OUTPUT_ROLES,
        plan_stages,
        stages,
        strict=True,
    ):
        program = _object(observed.get("program"), "identity observed program")
        source = _run_output_path(run_root, planned, "artifact_file")
        raw = _stable_read(source, role, MAX_OUTPUT_BYTES)
        _require_file_binding(raw, program, "program_binary_sha256", "program_binary_bytes", role)
        payloads[role] = raw

    companion = _object(stages[0].get("companion_host_binary"), "source CLI observation")
    source_cli_plan = _object(plan_stages[0].get("companion_host_binary"), "source CLI plan")
    destination = _bounded_string(source_cli_plan.get("destination"), "source CLI destination")
    source_cli = (
        run_root / _bounded_relative_output(plan_stages[0]) / PurePosixPath(destination).name
    )
    source_cli_raw = _stable_read(source_cli, "source CLI", MAX_OUTPUT_BYTES)
    _require_file_binding(
        source_cli_raw,
        companion,
        "binary_sha256",
        "binary_bytes",
        "source CLI",
    )
    payloads["source_cli"] = source_cli_raw
    if set(payloads) != set(OUTPUT_ROLES):
        raise IdentityStageError("identity payload inventory mismatch")
    return payloads


def _run_output_path(run_root: Path, stage: Mapping[str, object], file_field: str) -> Path:
    relative = _bounded_relative_output(stage)
    filename = _bounded_string(stage.get(file_field), "identity artifact filename")
    if PurePosixPath(filename).name != filename:
        raise IdentityStageError("identity artifact filename is not canonical")
    return run_root / relative / filename


def _bounded_relative_output(stage: Mapping[str, object]) -> PurePosixPath:
    value = _bounded_string(stage.get("output_directory"), "identity output directory")
    pure = PurePosixPath(value)
    if pure.is_absolute() or ".." in pure.parts or pure.as_posix() != value:
        raise IdentityStageError("identity output directory is not canonical")
    return pure


def _require_file_binding(
    raw: bytes,
    record: Mapping[str, object],
    digest_field: str,
    size_field: str,
    label: str,
) -> None:
    digest = record.get(digest_field)
    size = record.get(size_field)
    if (
        type(digest) is not str
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or type(size) is not int
        or size != len(raw)
        or hashlib.sha256(raw).hexdigest() != digest
    ):
        raise IdentityStageError(f"{label} differs from checked observations")


def _validate_output_paths(output_paths: Mapping[str, Path], repository: Path) -> dict[str, Path]:
    if set(output_paths) != set(OUTPUT_ROLES):
        raise IdentityStageError("identity output role inventory mismatch")
    normalized: dict[str, Path] = {}
    identities: set[str] = set()
    for role in OUTPUT_ROLES:
        path = output_paths[role]
        if (
            not isinstance(path, Path)
            or not path.is_absolute()
            or path.exists()
            or path.is_symlink()
        ):
            raise IdentityStageError(f"{role} output must begin absent and absolute")
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        try:
            parent = path.parent.resolve(strict=True)
        except OSError as exc:
            raise IdentityStageError(f"{role} output parent is unavailable") from exc
        candidate = parent / path.name
        if candidate != path or candidate == repository or repository in candidate.parents:
            raise IdentityStageError(f"{role} output path is not canonical and external")
        key = candidate.as_posix()
        if key in identities:
            raise IdentityStageError("identity output paths must be unique")
        identities.add(key)
        normalized[role] = candidate
    return normalized


def _validate_absent_run_root(path: Path, repository: Path) -> Path:
    if not isinstance(path, Path) or not path.is_absolute() or path.exists() or path.is_symlink():
        raise IdentityStageError("identity run root must begin absent and be absolute")
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise IdentityStageError("identity run-root parent is unavailable") from exc
    candidate = parent / path.name
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise IdentityStageError("identity run root must be canonical and external")
    return candidate


def _require_disjoint_run_and_outputs(run_root: Path, output_paths: Mapping[str, Path]) -> None:
    if any(run_root == path or run_root in path.parents for path in output_paths.values()):
        raise IdentityStageError("identity outputs must be outside the disposable run root")


def _canonical_repository(path: Path) -> Path:
    try:
        root = path.resolve(strict=True)
    except OSError as exc:
        raise IdentityStageError("identity repository is unavailable") from exc
    if root != path or not root.is_dir():
        raise IdentityStageError("identity repository must be one canonical directory")
    return root


def _validate_source_commit(value: str) -> None:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise IdentityStageError("source commit must be 40 lowercase hexadecimal characters")


def _write_outputs(paths: Mapping[str, Path], payloads: Mapping[str, bytes]) -> None:
    for role in OUTPUT_ROLES:
        maximum = MAX_JSON_OUTPUT_BYTES if role.startswith("identity_") else MAX_OUTPUT_BYTES
        raw = payloads[role]
        if not 0 < len(raw) <= maximum:
            raise IdentityStageError(f"{role} output exceeds its bound")
        _write_new(paths[role], raw, role)


def _write_new(path: Path, raw: bytes, label: str) -> None:
    descriptor: int | None = None
    parent_descriptor: int | None = None
    try:
        parent_descriptor = os.open(
            path.parent,
            os.O_RDONLY
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_NOFOLLOW", 0)
            | getattr(os, "O_CLOEXEC", 0),
        )
        descriptor = os.open(
            path.name,
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_NOFOLLOW", 0)
            | getattr(os, "O_CLOEXEC", 0),
            0o600,
            dir_fd=parent_descriptor,
        )
        offset = 0
        while offset < len(raw):
            written = os.write(descriptor, raw[offset:])
            if written <= 0:
                raise IdentityStageError(f"{label} output write made no progress")
            offset += written
        os.fsync(descriptor)
        os.fsync(parent_descriptor)
    except FileExistsError as exc:
        raise IdentityStageError(f"{label} output must begin absent") from exc
    except OSError as exc:
        raise IdentityStageError(f"{label} output write failed") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if parent_descriptor is not None:
            os.close(parent_descriptor)


def _stable_read(path: Path, label: str, maximum: int) -> bytes:
    descriptor: int | None = None
    try:
        descriptor = os.open(
            path,
            os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0),
        )
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or not 0 < before.st_size <= maximum
        ):
            raise IdentityStageError(f"{label} must be one bounded regular file")
        raw = bytearray()
        while len(raw) <= maximum:
            chunk = os.read(descriptor, min(1 << 20, maximum + 1 - len(raw)))
            if not chunk:
                break
            raw.extend(chunk)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise IdentityStageError(f"{label} could not be read") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    identity = lambda value: (  # noqa: E731 - compact stable identity tuple
        value.st_dev,
        value.st_ino,
        value.st_mode,
        value.st_nlink,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(raw) != before.st_size:
        raise IdentityStageError(f"{label} changed during read")
    return bytes(raw)


def _remove_completed_run_root(path: Path) -> None:
    try:
        shutil.rmtree(path)
    except OSError as exc:
        raise IdentityStageError("completed identity run-root cleanup failed") from exc
    if path.exists() or path.is_symlink():
        raise IdentityStageError("completed identity run root remains after cleanup")


def _object(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        raise IdentityStageError(f"{label} must be an object")
    return value


def _object_list(value: object, label: str) -> list[dict[str, object]]:
    if type(value) is not list or any(type(item) is not dict for item in value):
        raise IdentityStageError(f"{label} must be an object list")
    return value


def _bounded_string(value: object, label: str) -> str:
    if type(value) is not str or not 0 < len(value) <= 1024 or "\x00" in value:
        raise IdentityStageError(f"{label} must be one bounded string")
    return value


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--packet-r0vm", type=Path, required=True)
    parser.add_argument("--risc0-home", type=Path, required=True)
    parser.add_argument("--cargo-registry-dir", type=Path, required=True)
    parser.add_argument("--docker", type=Path, required=True)
    for role in OUTPUT_ROLES:
        parser.add_argument(f"--{role.replace('_', '-')}-out", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        require_exact_runtime_r0vm(args.risc0_home, args.packet_r0vm)
        runner = DockerBuildRunner(
            risc0_home=args.risc0_home,
            cargo_registry_directory=args.cargo_registry_dir,
            docker=args.docker,
        )
        outputs = {role: getattr(args, f"{role}_out") for role in OUTPUT_ROLES}
        execute_identity_stage(
            source_commit=args.source_commit,
            identity_run_root=Path(IDENTITY_RUN_ROOT),
            output_paths=outputs,
            runner=runner,
        )
    except (
        IdentityStageError,
        ExecutionError,
        IncompleteContainerCleanupError,
        planner.RebuildPlanError,
        OSError,
    ) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
