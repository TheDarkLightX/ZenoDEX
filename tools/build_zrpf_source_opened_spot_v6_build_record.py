#!/usr/bin/env python3
"""Build one deterministic source-opened Spot V6 program-build record.

The builder accepts only explicit source, artifact, tool, and date inputs.  It
derives retained identities, then delegates candidate validation to the V3
checker before atomically publishing any bytes. The builder cannot update or
satisfy the checker's immutable governed-record anchor. The resulting record
contains explicitly publisher-reported historical build observations. It does
not independently establish build execution, proof generation, reproducibility,
release authority, settlement authority, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from typing import Any, Sequence

try:
    from tools import check_zrpf_source_opened_spot_v6_build_record as checker
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    import check_zrpf_source_opened_spot_v6_build_record as checker  # type: ignore[no-redef]


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = checker.DEFAULT_RECORD
BUILD_REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record_build/v2"
RUSTC_VERSION = checker.OFFICIAL_RUSTC_VERSION
CARGO_VERSION = checker.OFFICIAL_CARGO_VERSION
R0VM_VERSION = checker.OFFICIAL_R0VM_VERSION
CARGO_RISCZERO_VERSION = checker.OFFICIAL_CARGO_RISCZERO_VERSION
RISC0_ZKVM_VERSION = checker.OFFICIAL_RISC0_ZKVM_VERSION
RISC0_TARGET = checker.OFFICIAL_RISC0_TARGET
MAX_TOOL_BYTES = checker.MAX_R0VM_BYTES


class BuildRecordBuildError(ValueError):
    """Stable fail-closed build-record construction rejection."""


@dataclass(frozen=True)
class BuildResult:
    """Candidate bytes and the non-governing checker report that validated them."""

    document: dict[str, Any]
    raw: bytes
    record_sha256: str
    checker_report: dict[str, Any]


def build_record(
    *,
    source_commit: str,
    artifact_directory: Path,
    r0vm_path: Path,
    cargo_risczero_path: Path,
    recorded_at: str,
    repo_root: Path = REPO_ROOT,
) -> BuildResult:
    """Derive and validate one exact V6 candidate program-build record.

    Unrelated worktree changes are outside this record. Every selected source
    byte in the checker's bounded closure must equal ``source_commit``.
    The four program binaries and both tools are captured through sealed memfd
    snapshots before their identities are used.
    """

    _require_source_commit(source_commit)
    _require_recorded_date(recorded_at)
    repository = _canonical_directory(repo_root, "repository root")
    artifacts = _canonical_directory(artifact_directory, "artifact directory")
    r0vm = _canonical_executable(r0vm_path, "r0vm")
    cargo_risczero = _canonical_executable(
        cargo_risczero_path,
        "cargo-risczero",
    )
    _require_exact_artifact_inventory(artifacts)

    source_observation, cargo_lock_sha256 = _source_observation(
        repository,
        source_commit,
    )
    toolchain, programs = _toolchain_and_program_records(
        artifacts,
        r0vm,
        cargo_risczero,
        cargo_lock_sha256,
    )
    document = _record_document(
        recorded_at,
        source_observation,
        toolchain,
        programs,
    )
    raw = checker.canonical_bytes(document)
    record_sha256 = hashlib.sha256(raw).hexdigest()

    # The checker reopens every external input and recomputes all four image
    # IDs. No output write is reachable until this separate pass succeeds.
    report = checker.validate_candidate_record(
        document,
        raw,
        repo_root=repository,
        artifact_directory=artifacts,
        r0vm_path=r0vm,
    )
    _require_candidate_checker_report(report, record_sha256)
    return BuildResult(document, raw, record_sha256, report)


def _source_observation(
    repository: Path,
    source_commit: str,
) -> tuple[dict[str, Any], str]:
    repository_tree = _git_tree(repository, source_commit)
    committed = checker.compute_git_source_closure(repository, source_commit)
    if checker.compute_source_closure(repository) != committed:
        raise BuildRecordBuildError(
            "current selected source closure differs from source commit"
        )
    source_root_sha256, source_file_count, source_bytes = committed
    cargo_lock_sha256 = checker._verified_cargo_lock_sha256(
        repository,
        source_commit,
    )
    return (
        {
            "repository_commit": source_commit,
            "repository_tree": repository_tree,
            "source_root_sha256": source_root_sha256,
            "source_file_count": source_file_count,
            "source_bytes": source_bytes,
        },
        cargo_lock_sha256,
    )


def _toolchain_and_program_records(
    artifacts: Path,
    r0vm: Path,
    cargo_risczero: Path,
    cargo_lock_sha256: str,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    r0vm_descriptor, r0vm_sha256 = _capture_versioned_tool(
        r0vm,
        label="r0vm",
        arguments=("--version",),
        expected_version=R0VM_VERSION,
        expected_sha256=checker.OFFICIAL_R0VM_SHA256,
    )
    cargo_descriptor: int | None = None
    try:
        cargo_descriptor, cargo_sha256 = _capture_versioned_tool(
            cargo_risczero,
            label="cargo-risczero",
            arguments=("risczero", "--version"),
            expected_version=CARGO_RISCZERO_VERSION,
            expected_sha256=checker.OFFICIAL_CARGO_RISCZERO_SHA256,
        )
        programs = _program_records(artifacts, r0vm_descriptor)
    finally:
        os.close(r0vm_descriptor)
        if cargo_descriptor is not None:
            os.close(cargo_descriptor)
    return (
        {
            "rustc": RUSTC_VERSION,
            "cargo": CARGO_VERSION,
            "r0vm": f"{R0VM_VERSION} sha256:{r0vm_sha256}",
            "cargo_risczero": f"{CARGO_RISCZERO_VERSION} sha256:{cargo_sha256}",
            "risc0_zkvm": RISC0_ZKVM_VERSION,
            "cargo_lock_sha256": cargo_lock_sha256,
            "target": RISC0_TARGET,
            "build_jobs": checker.OFFICIAL_BUILD_JOBS,
            "offline": True,
            "locked": True,
        },
        programs,
    )


def _record_document(
    recorded_at: str,
    source_observation: dict[str, Any],
    toolchain: dict[str, Any],
    programs: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": checker.RECORD_SCHEMA,
        "recorded_at": recorded_at,
        "source_observation": source_observation,
        "toolchain": toolchain,
        "programs": programs,
        "publisher_reported_observations": {
            "commands_reported_executed": {
                field: True
                for field in sorted(checker.PUBLISHER_REPORTED_COMMAND_FIELDS)
            },
            "same_host_current_v6_images_built": True,
        },
        "claims": {
            **{field: True for field in sorted(checker.TRUE_CLAIMS)},
            **{field: False for field in sorted(checker.FALSE_CLAIMS)},
        },
    }


def build_and_write_record(
    *,
    source_commit: str,
    artifact_directory: Path,
    r0vm_path: Path,
    cargo_risczero_path: Path,
    recorded_at: str,
    output: Path = DEFAULT_OUTPUT,
    replace: bool = False,
    repo_root: Path = REPO_ROOT,
) -> BuildResult:
    """Build, revalidate, and atomically publish one record."""

    result = build_record(
        source_commit=source_commit,
        artifact_directory=artifact_directory,
        r0vm_path=r0vm_path,
        cargo_risczero_path=cargo_risczero_path,
        recorded_at=recorded_at,
        repo_root=repo_root,
    )
    _reject_output_aliases(
        output,
        artifact_directory=artifact_directory,
        r0vm_path=r0vm_path,
        cargo_risczero_path=cargo_risczero_path,
    )
    _atomic_write(output, result.raw, replace=replace)
    return result


def _require_source_commit(value: str) -> None:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise BuildRecordBuildError(
            "source commit must be exactly 40 lowercase hexadecimal characters"
        )


def _require_recorded_date(value: str) -> None:
    if type(value) is not str:
        raise BuildRecordBuildError("recorded date must be a canonical ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError as exc:
        raise BuildRecordBuildError(
            "recorded date must be a canonical ISO date"
        ) from exc
    if parsed.isoformat() != value:
        raise BuildRecordBuildError("recorded date must be a canonical ISO date")


def _canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise BuildRecordBuildError(
            f"{label} must be an absolute canonical non-symlink directory"
        )
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise BuildRecordBuildError(f"{label} is unavailable") from exc
    if resolved != path or not resolved.is_dir():
        raise BuildRecordBuildError(
            f"{label} must be an absolute canonical non-symlink directory"
        )
    return resolved


def _canonical_executable(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise BuildRecordBuildError(
            f"{label} must be an absolute canonical non-symlink executable"
        )
    try:
        resolved = path.resolve(strict=True)
        facts = path.stat(follow_symlinks=False)
    except OSError as exc:
        raise BuildRecordBuildError(f"{label} executable is unavailable") from exc
    if (
        resolved != path
        or not stat.S_ISREG(facts.st_mode)
        or facts.st_mode & 0o111 == 0
    ):
        raise BuildRecordBuildError(
            f"{label} must be an absolute canonical non-symlink executable"
        )
    return resolved


def _require_exact_artifact_inventory(directory: Path) -> None:
    expected = {spec[2] for spec in checker.PROGRAM_SPECS}
    entries: list[os.DirEntry[str]] = []
    try:
        with os.scandir(directory) as iterator:
            for entry in iterator:
                entries.append(entry)
                if len(entries) > len(expected):
                    raise BuildRecordBuildError(
                        "artifact directory must contain exactly the four "
                        "governed program binaries"
                    )
    except OSError as exc:
        raise BuildRecordBuildError("artifact directory inventory failed") from exc
    observed = {entry.name for entry in entries}
    if observed != expected or len(entries) != len(expected):
        raise BuildRecordBuildError(
            "artifact directory must contain exactly the four governed program binaries"
        )
    for entry in entries:
        try:
            facts = entry.stat(follow_symlinks=False)
        except OSError as exc:
            raise BuildRecordBuildError(
                f"artifact inventory entry is unavailable: {entry.name}"
            ) from exc
        if entry.is_symlink() or not stat.S_ISREG(facts.st_mode):
            raise BuildRecordBuildError(
                f"artifact inventory entry is not a regular file: {entry.name}"
            )


def _git_tree(repository: Path, source_commit: str) -> str:
    completed = checker._run_git_bounded(
        repository,
        ["rev-parse", "--verify", f"{source_commit}^{{tree}}"],
        "source commit tree lookup",
    )
    if (
        completed.returncode != 0
        or completed.stderr
        or len(completed.stdout) != 41
        or not completed.stdout.endswith(b"\n")
    ):
        raise BuildRecordBuildError("source commit Git tree lookup failed")
    try:
        tree = completed.stdout[:-1].decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise BuildRecordBuildError("source commit Git tree is malformed") from exc
    if re.fullmatch(r"[0-9a-f]{40}", tree) is None:
        raise BuildRecordBuildError("source commit Git tree is malformed")
    checker._validate_git_tree(repository, source_commit, tree)
    return tree


def _capture_versioned_tool(
    path: Path,
    *,
    label: str,
    arguments: tuple[str, ...],
    expected_version: str,
    expected_sha256: str,
) -> tuple[int, str]:
    descriptor, _size, digest, _prefix = checker._sealed_file_snapshot(
        path,
        label=f"{label} executable",
        maximum_bytes=MAX_TOOL_BYTES,
        executable=True,
    )
    retained = False
    try:
        observed = _run_sealed_tool(descriptor, arguments, label)
        if observed != expected_version:
            raise BuildRecordBuildError(
                f"{label} version must be exactly {expected_version}"
            )
        if digest != expected_sha256:
            raise BuildRecordBuildError(
                f"{label} executable identity differs from checker-owned policy"
            )
        retained = True
        return descriptor, digest
    finally:
        if not retained:
            os.close(descriptor)


def _run_sealed_tool(
    descriptor: int,
    arguments: tuple[str, ...],
    label: str,
) -> str:
    environment = {
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    try:
        completed = subprocess.run(
            [f"/proc/self/fd/{descriptor}", *arguments],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            pass_fds=(descriptor,),
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise BuildRecordBuildError(f"{label} version query failed") from exc
    if (
        completed.returncode != 0
        or completed.stderr
        or not completed.stdout.endswith(b"\n")
        or completed.stdout.count(b"\n") != 1
    ):
        raise BuildRecordBuildError(f"{label} version query failed")
    try:
        return completed.stdout[:-1].decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise BuildRecordBuildError(f"{label} version is not ASCII") from exc


def _program_records(directory: Path, r0vm_descriptor: int) -> list[dict[str, Any]]:
    programs: list[dict[str, Any]] = []
    for (
        stage,
        package,
        artifact_file,
        expected_image_id,
        child_stage,
        child_image_id,
    ) in checker.PROGRAM_SPECS:
        path = checker._resolve_artifact(directory, artifact_file)
        descriptor, size, digest = checker._open_stable_program_binary(path)
        try:
            image_id = checker._compute_program_image_id(
                r0vm_descriptor,
                descriptor,
            )
        finally:
            os.close(descriptor)
        if image_id != expected_image_id:
            raise BuildRecordBuildError(
                f"program image ID differs from governed policy: {artifact_file}"
            )
        programs.append(
            {
                "stage": stage,
                "package": package,
                "artifact_file": artifact_file,
                "program_binary_bytes": size,
                "program_binary_sha256": digest,
                "image_id_hex": image_id,
                "image_id_words_le": checker._image_words_le(image_id),
                "verified_child_stage": child_stage,
                "verified_child_image_id": child_image_id,
            }
        )
    return programs


def _require_candidate_checker_report(
    report: dict[str, Any],
    record_sha256: str,
) -> None:
    expected = {
        "ok": True,
        "record_sha256": record_sha256,
        "candidate_record_validated": True,
        "governed_record_anchor_checked": False,
        "external_artifact_files_checked": len(checker.PROGRAM_SPECS),
        "program_image_ids_recomputed": len(checker.PROGRAM_SPECS),
        "local_path_dependency_crates_checked": len(
            checker.GOVERNED_LOCAL_PATH_CRATE_DIRECTORIES
        ),
        "source_closure_final_recheck": True,
        "live_governed_artifact_set_observed": False,
        "global_worktree_cleanliness_verified": False,
        "historical_build_commands_independently_verified": False,
        "source_to_program_binary_provenance_verified": False,
        "proofs_generated": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    if any(report.get(field) != value for field, value in expected.items()):
        raise BuildRecordBuildError(
            "V3 checker did not validate the exact non-governing candidate record"
        )


def _reject_output_aliases(
    output: Path,
    *,
    artifact_directory: Path,
    r0vm_path: Path,
    cargo_risczero_path: Path,
) -> None:
    if not output.is_absolute():
        raise BuildRecordBuildError("output path must be absolute")
    try:
        parent = output.parent.resolve(strict=True)
    except OSError as exc:
        raise BuildRecordBuildError("output parent directory is unavailable") from exc
    candidate = parent / output.name
    inputs = {
        r0vm_path.resolve(strict=True),
        cargo_risczero_path.resolve(strict=True),
    }
    artifact_root = artifact_directory.resolve(strict=True)
    inputs.update(artifact_root / spec[2] for spec in checker.PROGRAM_SPECS)
    if candidate in inputs:
        raise BuildRecordBuildError("output path aliases a governed input")


def _atomic_write(path: Path, raw: bytes, *, replace: bool) -> None:
    directory_descriptor = _open_output_parent(path)
    temporary_name = (
        f".{path.name}.tmp-{os.getpid()}-{hashlib.sha256(raw).hexdigest()[:16]}"
    )
    temporary_descriptor: int | None = None
    temporary_exists = False
    try:
        temporary_descriptor = os.open(
            temporary_name,
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_NOFOLLOW", 0),
            0o600,
            dir_fd=directory_descriptor,
        )
        temporary_exists = True
        _write_temporary_record(temporary_descriptor, raw)
        os.close(temporary_descriptor)
        temporary_descriptor = None
        _publish_temporary_record(
            directory_descriptor,
            temporary_name,
            path.name,
            replace=replace,
        )
        temporary_exists = False
        os.fsync(directory_descriptor)
    except OSError as exc:
        raise BuildRecordBuildError("atomic output replacement failed") from exc
    finally:
        if temporary_descriptor is not None:
            os.close(temporary_descriptor)
        if temporary_exists:
            try:
                os.unlink(temporary_name, dir_fd=directory_descriptor)
            except FileNotFoundError:
                pass
        os.close(directory_descriptor)


def _open_output_parent(path: Path) -> int:
    if not path.is_absolute() or path.name in {"", ".", ".."}:
        raise BuildRecordBuildError("output path must be absolute and canonical")
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise BuildRecordBuildError("output parent directory is unavailable") from exc
    if parent != path.parent or not parent.is_dir() or parent.is_symlink():
        raise BuildRecordBuildError("output parent must be a canonical directory")
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        return os.open(parent, flags)
    except OSError as exc:
        raise BuildRecordBuildError("output parent could not be opened") from exc


def _write_temporary_record(descriptor: int, raw: bytes) -> None:
    pending = memoryview(raw)
    while pending:
        written = os.write(descriptor, pending)
        if written <= 0:
            raise BuildRecordBuildError("atomic output write failed")
        pending = pending[written:]
    os.fchmod(descriptor, 0o644)
    os.fsync(descriptor)


def _publish_temporary_record(
    directory_descriptor: int,
    temporary_name: str,
    output_name: str,
    *,
    replace: bool,
) -> None:
    if replace:
        _require_regular_existing_output(directory_descriptor, output_name)
        os.replace(
            temporary_name,
            output_name,
            src_dir_fd=directory_descriptor,
            dst_dir_fd=directory_descriptor,
        )
        return
    try:
        os.link(
            temporary_name,
            output_name,
            src_dir_fd=directory_descriptor,
            dst_dir_fd=directory_descriptor,
            follow_symlinks=False,
        )
    except FileExistsError as exc:
        raise BuildRecordBuildError(
            "output already exists; pass --replace to replace it"
        ) from exc
    os.unlink(temporary_name, dir_fd=directory_descriptor)


def _require_regular_existing_output(
    directory_descriptor: int,
    output_name: str,
) -> None:
    try:
        existing = os.stat(
            output_name,
            dir_fd=directory_descriptor,
            follow_symlinks=False,
        )
    except FileNotFoundError:
        return
    if not stat.S_ISREG(existing.st_mode):
        raise BuildRecordBuildError("existing output is not a regular file")


def _success_report(result: BuildResult) -> dict[str, Any]:
    return {
        "ok": True,
        "schema": BUILD_REPORT_SCHEMA,
        "record_sha256": result.record_sha256,
        "programs_recorded": len(result.document["programs"]),
        "program_image_ids_recomputed": result.checker_report[
            "program_image_ids_recomputed"
        ],
        "candidate_record_validated": True,
        "governed_record_anchor_checked": False,
        "live_governed_artifact_set_observed": False,
        "global_worktree_cleanliness_verified": False,
        "historical_build_commands_independently_verified": False,
        "source_to_program_binary_provenance_verified": False,
        "proofs_generated": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--artifact-directory", required=True, type=Path)
    parser.add_argument("--r0vm", required=True, type=Path)
    parser.add_argument("--cargo-risczero", required=True, type=Path)
    parser.add_argument("--recorded-at", required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--replace", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        result = build_and_write_record(
            source_commit=arguments.source_commit,
            artifact_directory=arguments.artifact_directory,
            r0vm_path=arguments.r0vm,
            cargo_risczero_path=arguments.cargo_risczero,
            recorded_at=arguments.recorded_at,
            output=arguments.output,
            replace=arguments.replace,
        )
    except (BuildRecordBuildError, checker.BuildRecordError, OSError) as exc:
        report = {
            "ok": False,
            "schema": BUILD_REPORT_SCHEMA,
            "errors": [str(exc)],
            "candidate_record_validated": False,
            "governed_record_anchor_checked": False,
            "live_governed_artifact_set_observed": False,
            "global_worktree_cleanliness_verified": False,
            "historical_build_commands_independently_verified": False,
            "source_to_program_binary_provenance_verified": False,
            "proofs_generated": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        }
        if arguments.json:
            print(json.dumps(report, sort_keys=True, separators=(",", ":")))
        else:
            print(f"rejected: {exc}", file=sys.stderr)
        return 1
    report = _success_report(result)
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(f"accepted {result.record_sha256}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
