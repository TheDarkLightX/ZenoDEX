#!/usr/bin/env python3
"""Build and materialize the exact remote ZRPF prover-worker artifacts.

This adapter emits source-bound candidate artifacts. It does not grant proof,
release, settlement, ledger, or production authority.
"""

from __future__ import annotations

import argparse
import copy
import fcntl
import hashlib
import io
import json
import os
import re
import shutil
import stat
import sys
import tarfile
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import check_zrpf_source_opened_spot_v6_build_record as image_checker  # noqa: E402
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner  # noqa: E402
from tools import zrpf_v6_v7_post_pin_governance as governance  # noqa: E402
from tools.run_zrpf_remote_identity_rebuild_stage_v2 import (  # noqa: E402
    require_exact_runtime_r0vm,
)
from tools.zrpf_v6_identity_docker_runner import DockerBuildRunner  # noqa: E402
from tools.zrpf_v6_identity_executor_types import (  # noqa: E402
    ArchiveMember,
    BuildKind,
    BuildRequest,
    BuildResult,
    BuildRunner,
    ExecutionError,
    IncompleteContainerCleanupError,
)

BUILD_RUN_ROOT = "/external/zrpf-remote-reproof-handoff-v2/worker-build/run"
REPORT_SCHEMA = "zenodex/zrpf_remote_worker_prover_build_report/v2"
REPORT_STATUS = "source_bound_worker_prover_build_candidate_checked"
REPORT_DOMAIN = b"zenodex.zrpf.remote_worker_prover_build_report.v2\0"
MAX_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_UNPACKED_BYTES = 256 * 1024 * 1024
MAX_GOVERNANCE_BYTES = 4 * 1024 * 1024
ZERO_SHA256 = "0" * 64

AUTHORITY_FIELDS = (
    "ledger_authority",
    "production_authority",
    "proof_authority",
    "release_authority",
    "settlement_authority",
)
GOVERNANCE_NON_CLAIMS = governance.NON_CLAIMS
GOVERNANCE_FIELDS = {
    "schema",
    "status",
    "c0_commit",
    "c1_commit",
    "c2_commit",
    "governance_commit",
    "plan_sha256",
    "observations_sha256",
    "candidate_report_sha256",
    "materialization_manifest_sha256",
    "v6_settlement_image_id",
    "v6_settlement_image_id_words",
    "v7_child_policy_tree",
    "v7_child_policy_sha256",
    "validated_facts",
    "authority",
    "non_claims",
}
GOVERNANCE_VALIDATED_FACTS = {
    "governance_checkout_is_clean_and_exact": True,
    "c1_is_literal_direct_child_of_c0": True,
    "c1_matches_exact_v6_materialization": True,
    "c2_is_literal_direct_child_of_c1": True,
    "c2_contains_only_exact_v7_child_pin": True,
    "governance_commit_is_literal_direct_child_of_c2": True,
    "governance_commit_adds_only_fixed_canonical_evidence": True,
    "manifest_recomposes_from_committed_evidence": True,
    "v6_settlement_image_id_is_nonzero_and_exact": True,
    "committed_v7_policy_matches_manifest_and_c2_tree": True,
}
WORKER_VALIDATED_FACTS = {
    "every_host_artifact_has_elf_magic": True,
    "governance_result_matches_external_source_expectation": True,
    "v7_program_has_r0bf_magic": True,
    "v7_program_image_id_matches_external_expectation": True,
}
NON_CLAIMS = (
    "candidate_binaries_and_program_bytes_do_not_establish_proof_validity",
    "the_build_runner_does_not_establish_complete_build_input_closure",
    "the_build_runner_does_not_resist_a_malicious_same_uid_host_process",
    "the_worker_build_report_is_an_unkeyed_candidate_commitment",
    "no_cross_host_reproducibility_or_historical_execution_provenance",
    "no_data_availability_finality_ledger_release_settlement_or_production_authority",
)

BINARY_OUTPUT_ROLES = (
    "v2_adapter_prover",
    "v6_leaf_prover",
    "v6_l1_prover",
    "v6_l2_prover",
    "v6_settlement_prover",
    "v6_host_verifier",
    "mutation_verifier",
    "v7_prover",
)
BUILD_OUTPUT_ROLES = (*BINARY_OUTPUT_ROLES[:6], "mutation_verifier", "v7_program", "v7_prover")
OUTPUT_ROLES = (*BUILD_OUTPUT_ROLES, "worker_build_report")


@dataclass(frozen=True, slots=True)
class MemberSpec:
    role: str
    name: str
    source: str
    executable: bool


V6_TARGET = "/build/zrpf-worker-v6/target"
V7_TARGET = "/build/zrpf-worker-v7/target"
V6_MEMBERS = (
    MemberSpec(
        "v2_adapter_prover",
        "01-prove-v2-leaf-adapter",
        f"{V6_TARGET}/release/prove_v2_leaf_adapter",
        True,
    ),
    MemberSpec(
        "v6_leaf_prover",
        "02-prove-spot-value-leaf-v6",
        f"{V6_TARGET}/release/prove_spot_value_leaf_v6",
        True,
    ),
    MemberSpec(
        "v6_l1_prover",
        "03-prove-spot-value-aggregate-l1-v6",
        f"{V6_TARGET}/release/prove_spot_value_aggregate_l1_v6",
        True,
    ),
    MemberSpec(
        "v6_l2_prover",
        "04-prove-spot-value-aggregate-l2-v6",
        f"{V6_TARGET}/release/prove_spot_value_aggregate_l2_v6",
        True,
    ),
    MemberSpec(
        "v6_settlement_prover",
        "05-prove-source-opened-spot-settlement-v6",
        f"{V6_TARGET}/release/prove_source_opened_spot_settlement_v6",
        True,
    ),
    MemberSpec(
        "v6_host_verifier",
        "06-source-opened-spot-settlement-verifier-v6",
        f"{V6_TARGET}/release/source-opened-spot-settlement-verifier-v6",
        True,
    ),
)
V7_MEMBERS = (
    MemberSpec(
        "mutation_verifier",
        "07-verify-spot-v7-remote-mutations",
        f"{V7_TARGET}/release/verify-spot-v7-remote-mutations",
        True,
    ),
    MemberSpec(
        "v7_program",
        "08-spot-settlement-v7-program",
        (
            f"{V7_TARGET}/riscv-guest/"
            "zenodex-zrpf-risc0-spot-settlement-v7-methods/"
            "zenodex-zrpf-risc0-spot-settlement-v7-guest/"
            "riscv32im-risc0-zkvm-elf/release/"
            "zenodex-zrpf-risc0-spot-settlement-v7-guest.bin"
        ),
        False,
    ),
    MemberSpec(
        "v7_prover",
        "09-prove-spot-settlement-v7",
        f"{V7_TARGET}/release/prove_spot_settlement_v7",
        True,
    ),
)


class WorkerBuildError(ValueError):
    """Stable fail-closed remote worker-build rejection."""


def execute_worker_build_stage(
    *,
    source_commit: str,
    governance_path: Path,
    build_run_root: Path,
    output_paths: Mapping[str, Path],
    runner: BuildRunner,
    image_id_computer: Callable[[bytes], str],
    governance_checker: Callable[
        [Path], Mapping[str, object]
    ] = governance.check_post_pin_governance,
    repo_root: Path = planner.REPO_ROOT,
) -> None:
    """Build two bounded archives and publish their exact checked members."""

    repository = _canonical_repository(repo_root)
    _require_commit(source_commit)
    governance_raw = _stable_read(governance_path, "governance result", MAX_GOVERNANCE_BYTES)
    governed = _validate_governance_result(governance_raw, source_commit)
    try:
        expected_governance = dict(governance_checker(repository))
    except (governance.GovernanceError, ExecutionError, OSError) as exc:
        raise WorkerBuildError("live governance validation rejected") from exc
    if governed != expected_governance or governed.get("governance_commit") != source_commit:
        raise WorkerBuildError("governance result differs from the exact worker source")
    run_root = _validate_run_root(build_run_root, repository)
    outputs = _validate_output_paths(output_paths, repository)
    _require_disjoint(run_root, outputs)
    _create_private_directory(run_root)
    try:
        requests = _build_requests(source_commit, run_root, repository)
        payloads: dict[str, bytes] = {}
        for request, members in zip(requests, (V6_MEMBERS, V7_MEMBERS), strict=True):
            result = runner.run(request)
            archive_path = request.output_directory / request.artifact_file
            raw_archive = _stable_read(archive_path, request.stage_id, MAX_ARCHIVE_BYTES)
            _require_build_result(result, raw_archive, request.stage_id)
            payloads.update(_decode_archive(raw_archive, members))
        if tuple(payloads) != BUILD_OUTPUT_ROLES:
            raise WorkerBuildError("worker build output inventory mismatch")
        v7_image_id = image_id_computer(payloads["v7_program"])
        _require_image_id(v7_image_id)
        runner_posture = _checked_runner_posture(runner.security_posture())
        report = _build_report(
            source_commit,
            governance_raw,
            payloads,
            runner_posture,
            v7_image_id,
        )
        report_raw = planner.canonical_bytes(report)
        if (
            validate_worker_build_report(
                report_raw,
                payloads,
                governance_raw,
                expected_source_commit=source_commit,
                expected_v7_image_id=v7_image_id,
            )
            != v7_image_id
        ):
            raise WorkerBuildError("worker build report did not self-validate")
        _remove_completed_run_root(run_root)
        _write_outputs(outputs, {**payloads, "worker_build_report": report_raw})
    except IncompleteContainerCleanupError:
        raise
    except (ExecutionError, OSError, tarfile.TarError) as exc:
        raise WorkerBuildError("worker prover build stage rejected") from exc


def derive_worker_build_report_id(report: Mapping[str, object]) -> str:
    candidate = copy.deepcopy(dict(report))
    candidate["report_id"] = ZERO_SHA256
    return hashlib.sha256(REPORT_DOMAIN + planner.canonical_bytes(candidate)).hexdigest()


def validate_worker_build_report(
    raw: bytes,
    output_bytes: Mapping[str, bytes],
    governance_raw: bytes,
    *,
    expected_source_commit: str,
    expected_v7_image_id: str,
) -> str:
    """Strictly bind one candidate report to every published build artifact."""

    report = _load_canonical_object(raw, "worker build report")
    expected_fields = {
        "authority",
        "governance_sha256",
        "non_claims",
        "outputs",
        "report_id",
        "runner_posture",
        "schema",
        "source_commit",
        "status",
        "v7_image_id",
        "validated_facts",
    }
    if set(report) != expected_fields:
        raise WorkerBuildError("worker build report field inventory mismatch")
    if (
        report.get("schema") != REPORT_SCHEMA
        or report.get("status") != REPORT_STATUS
        or report.get("report_id") != derive_worker_build_report_id(report)
        or hashlib.sha256(governance_raw).hexdigest() != report.get("governance_sha256")
    ):
        raise WorkerBuildError("worker build report identity mismatch")
    _require_commit(expected_source_commit)
    _require_image_id(expected_v7_image_id)
    governed = _validate_governance_result(governance_raw, expected_source_commit)
    if (
        report.get("source_commit") != expected_source_commit
        or governed.get("governance_commit") != expected_source_commit
    ):
        raise WorkerBuildError("worker build source and governance binding mismatch")
    _require_false_authority(report.get("authority"))
    if report.get("non_claims") != list(NON_CLAIMS):
        raise WorkerBuildError("worker build report non-claims mismatch")
    if set(output_bytes) != set(BUILD_OUTPUT_ROLES):
        raise WorkerBuildError("worker build output byte inventory mismatch")
    if any(
        not output_bytes[role].startswith(b"\x7fELF") for role in BINARY_OUTPUT_ROLES
    ) or not output_bytes["v7_program"].startswith(b"R0BF"):
        raise WorkerBuildError("worker build output magic mismatch")
    expected_outputs = _output_rows(output_bytes)
    if report.get("outputs") != expected_outputs:
        raise WorkerBuildError("worker build output bindings mismatch")
    _checked_runner_posture(report.get("runner_posture"))
    _require_exact_boolean_facts(
        report.get("validated_facts"),
        WORKER_VALIDATED_FACTS,
        "worker build validated facts",
    )
    image_id = report.get("v7_image_id")
    if image_id != expected_v7_image_id:
        raise WorkerBuildError("worker build V7 image ID expectation mismatch")
    return image_id


def _build_requests(
    source_commit: str,
    run_root: Path,
    repository: Path,
) -> tuple[BuildRequest, BuildRequest]:
    v6 = BuildRequest(
        kind=BuildKind.ARCHIVE,
        pass_id="worker:v6-host-bundle",
        stage_id="worker_v6_host_bundle",
        source_commit=source_commit,
        source_snapshot=repository,
        target_directory=run_root / "v6-target",
        output_directory=run_root / "v6-output",
        container_target_directory=V6_TARGET,
        container_output_directory="/build/zrpf-worker-v6/output",
        artifact_file="worker-v6-hosts.tar.gz",
        command=(
            planner.CANONICAL_CARGO,
            "build",
            "--manifest-path",
            "/src/zenodex/zk/zrpf_risc0/Cargo.toml",
            "--locked",
            "--offline",
            "--release",
            "--jobs",
            str(planner.BUILD_JOBS),
            "--target-dir",
            V6_TARGET,
            "-p",
            "zenodex-zrpf-risc0-harness",
            "-p",
            "zenodex-zrpf-risc0-verifier",
            "--features",
            "legacy-methods,spot-v6-methods",
            "--bins",
        ),
        extraction_source=f"{V6_TARGET}/worker-v6-hosts.tar.gz",
        archive_members=tuple(
            ArchiveMember(item.source, item.name, item.executable) for item in V6_MEMBERS
        ),
    )
    v7 = BuildRequest(
        kind=BuildKind.ARCHIVE,
        pass_id="worker:v7-bundle",
        stage_id="worker_v7_bundle",
        source_commit=source_commit,
        source_snapshot=repository,
        target_directory=run_root / "v7-target",
        output_directory=run_root / "v7-output",
        container_target_directory=V7_TARGET,
        container_output_directory="/build/zrpf-worker-v7/output",
        artifact_file="worker-v7-artifacts.tar.gz",
        command=(
            planner.CANONICAL_CARGO,
            "build",
            "--manifest-path",
            "/src/zenodex/zk/spot_settlement_v7_risc0/Cargo.toml",
            "--locked",
            "--offline",
            "--release",
            "--jobs",
            str(planner.BUILD_JOBS),
            "--target-dir",
            V7_TARGET,
            "-p",
            "zenodex-zrpf-risc0-spot-settlement-v7-harness",
            "-p",
            "zenodex-zrpf-risc0-spot-v7-remote-mutation-verifier",
            "--bins",
        ),
        extraction_source=f"{V7_TARGET}/worker-v7-artifacts.tar.gz",
        archive_members=tuple(
            ArchiveMember(item.source, item.name, item.executable) for item in V7_MEMBERS
        ),
    )
    return v6, v7


def _decode_archive(raw: bytes, expected: Sequence[MemberSpec]) -> dict[str, bytes]:
    try:
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as archive:
            members = archive.getmembers()
            expected_names = [item.name for item in sorted(expected, key=lambda item: item.name)]
            if [item.name for item in members] != expected_names:
                raise WorkerBuildError("worker build archive inventory mismatch")
            payloads: dict[str, bytes] = {}
            total = 0
            by_name = {item.name: item for item in expected}
            for member in members:
                spec = by_name[member.name]
                expected_mode = 0o555 if spec.executable else 0o444
                total += member.size
                if (
                    not member.isfile()
                    or member.uid != 0
                    or member.gid != 0
                    or member.mtime != 0
                    or member.mode != expected_mode
                    or not 0 < member.size <= planner.MAX_HOST_BINARY_BYTES
                    or total > MAX_UNPACKED_BYTES
                ):
                    raise WorkerBuildError("worker build archive member metadata mismatch")
                stream = archive.extractfile(member)
                if stream is None:
                    raise WorkerBuildError("worker build archive member is unreadable")
                value = stream.read(member.size + 1)
                if len(value) != member.size:
                    raise WorkerBuildError("worker build archive member size mismatch")
                magic = b"\x7fELF" if spec.executable else b"R0BF"
                if not value.startswith(magic):
                    raise WorkerBuildError("worker build archive member magic mismatch")
                payloads[spec.role] = value
            if archive.next() is not None:
                raise WorkerBuildError("worker build archive contains trailing members")
    except (OSError, tarfile.TarError, EOFError) as exc:
        raise WorkerBuildError("worker build archive rejected") from exc
    return payloads


def _build_report(
    source_commit: str,
    governance_raw: bytes,
    payloads: Mapping[str, bytes],
    runner_posture: Mapping[str, object],
    v7_image_id: str,
) -> dict[str, object]:
    report: dict[str, object] = {
        "authority": {field: False for field in AUTHORITY_FIELDS},
        "governance_sha256": hashlib.sha256(governance_raw).hexdigest(),
        "non_claims": list(NON_CLAIMS),
        "outputs": _output_rows(payloads),
        "report_id": ZERO_SHA256,
        "runner_posture": dict(runner_posture),
        "schema": REPORT_SCHEMA,
        "source_commit": source_commit,
        "status": REPORT_STATUS,
        "v7_image_id": v7_image_id,
        "validated_facts": dict(WORKER_VALIDATED_FACTS),
    }
    report["report_id"] = derive_worker_build_report_id(report)
    return report


def _output_rows(payloads: Mapping[str, bytes]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for role in BUILD_OUTPUT_ROLES:
        raw = payloads[role]
        rows.append(
            {
                "bytes": len(raw),
                "kind": "risc0_program" if role == "v7_program" else "executable",
                "role": role,
                "sha256": hashlib.sha256(raw).hexdigest(),
            }
        )
    return rows


def _require_build_result(result: BuildResult, raw: bytes, label: str) -> None:
    if (
        type(result.artifact_bytes) is not int
        or result.artifact_bytes != len(raw)
        or result.artifact_sha256 != hashlib.sha256(raw).hexdigest()
        or result.image_id is not None
    ):
        raise WorkerBuildError(f"{label} differs from the governed build result")


def _load_canonical_object(raw: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            raw.decode("utf-8", errors="strict"),
            object_pairs_hook=planner._unique_object,
            parse_float=planner._reject_float,
            parse_int=planner._bounded_int,
        )
        planner._validate_json_shape(value)
    except (UnicodeDecodeError, json.JSONDecodeError, planner.RebuildPlanError) as exc:
        raise WorkerBuildError(f"{label} JSON rejected") from exc
    if type(value) is not dict or raw != planner.canonical_bytes(value):
        raise WorkerBuildError(f"{label} must use canonical JSON bytes")
    return value


def _require_false_authority(value: object) -> None:
    if (
        type(value) is not dict
        or set(value) != set(AUTHORITY_FIELDS)
        or any(value[field] is not False for field in AUTHORITY_FIELDS)
    ):
        raise WorkerBuildError("worker build authority must remain exactly false")


def _require_exact_boolean_facts(
    value: object,
    expected: Mapping[str, bool],
    label: str,
) -> None:
    if (
        type(value) is not dict
        or set(value) != set(expected)
        or any(type(value[field]) is not bool for field in expected)
        or any(value[field] is not expected[field] for field in expected)
    ):
        raise WorkerBuildError(f"{label} mismatch")


def _require_commit(value: object) -> None:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise WorkerBuildError("worker build source commit is invalid")


def _require_image_id(value: object) -> None:
    if (
        type(value) is not str
        or value == ZERO_SHA256
        or re.fullmatch(r"[0-9a-f]{64}", value) is None
    ):
        raise WorkerBuildError("V7 image ID is invalid")


def _validate_governance_result(raw: bytes, expected_source_commit: str) -> dict[str, Any]:
    value = _load_canonical_object(raw, "governance result")
    if (
        set(value) != GOVERNANCE_FIELDS
        or value.get("schema") != governance.CHECK_SCHEMA
        or value.get("status") != "committed_post_pin_governance_binding_checked"
        or value.get("governance_commit") != expected_source_commit
        or value.get("non_claims") != list(GOVERNANCE_NON_CLAIMS)
    ):
        raise WorkerBuildError("governance result schema or source binding mismatch")
    _require_exact_boolean_facts(
        value.get("validated_facts"),
        GOVERNANCE_VALIDATED_FACTS,
        "governance result validated facts",
    )
    for field in ("c0_commit", "c1_commit", "c2_commit", "governance_commit"):
        _require_commit(value.get(field))
    for field in (
        "plan_sha256",
        "observations_sha256",
        "candidate_report_sha256",
        "materialization_manifest_sha256",
        "v6_settlement_image_id",
        "v7_child_policy_sha256",
    ):
        if type(value.get(field)) is not str or re.fullmatch(r"[0-9a-f]{64}", value[field]) is None:
            raise WorkerBuildError("governance result digest binding mismatch")
    tree = value.get("v7_child_policy_tree")
    if type(tree) is not str or re.fullmatch(r"[0-9a-f]{40}", tree) is None:
        raise WorkerBuildError("governance result tree binding mismatch")
    image_id = value["v6_settlement_image_id"]
    words = value.get("v6_settlement_image_id_words")
    if (
        image_id == ZERO_SHA256
        or type(words) is not list
        or len(words) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFF_FFFF for word in words)
        or b"".join(word.to_bytes(4, "little") for word in words).hex() != image_id
    ):
        raise WorkerBuildError("governance result image-word binding mismatch")
    authority = value.get("authority")
    if (
        type(authority) is not dict
        or set(authority) != set(governance.AUTHORITY_FIELDS)
        or any(authority[field] is not False for field in governance.AUTHORITY_FIELDS)
    ):
        raise WorkerBuildError("governance result authority must remain exactly false")
    return value


def _validate_output_paths(paths: Mapping[str, Path], repository: Path) -> dict[str, Path]:
    if set(paths) != set(OUTPUT_ROLES):
        raise WorkerBuildError("worker build output role inventory mismatch")
    normalized: dict[str, Path] = {}
    for role in OUTPUT_ROLES:
        path = paths[role]
        if (
            not isinstance(path, Path)
            or not path.is_absolute()
            or path.exists()
            or path.is_symlink()
        ):
            raise WorkerBuildError(f"{role} output must begin absent and absolute")
        candidate = path.resolve(strict=False)
        if (
            candidate != path
            or candidate == repository
            or repository in candidate.parents
            or candidate in repository.parents
        ):
            raise WorkerBuildError(f"{role} output must be canonical and external")
        normalized[role] = candidate
    candidates = tuple(normalized.values())
    for index, candidate in enumerate(candidates):
        for other in candidates[index + 1 :]:
            if candidate == other or candidate in other.parents or other in candidate.parents:
                raise WorkerBuildError("worker build output paths must form an antichain")
    for candidate in candidates:
        candidate.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        if candidate.parent.resolve(strict=True) != candidate.parent:
            raise WorkerBuildError("worker build output parent changed during validation")
    return normalized


def _validate_run_root(path: Path, repository: Path) -> Path:
    if not isinstance(path, Path) or not path.is_absolute() or path.exists() or path.is_symlink():
        raise WorkerBuildError("worker build run root must begin absent and be absolute")
    parent = path.parent.resolve(strict=True)
    candidate = parent / path.name
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise WorkerBuildError("worker build run root must be canonical and external")
    return candidate


def _require_disjoint(run_root: Path, outputs: Mapping[str, Path]) -> None:
    if any(
        run_root == path or run_root in path.parents or path in run_root.parents
        for path in outputs.values()
    ):
        raise WorkerBuildError("worker build outputs must be outside the disposable run root")


def _canonical_repository(path: Path) -> Path:
    root = path.resolve(strict=True)
    if root != path or not root.is_dir():
        raise WorkerBuildError("worker build repository must be one canonical directory")
    return root


def _create_private_directory(path: Path) -> None:
    path.mkdir(mode=0o700)
    facts = path.lstat()
    if (
        not stat.S_ISDIR(facts.st_mode)
        or stat.S_ISLNK(facts.st_mode)
        or facts.st_uid != os.getuid()
        or stat.S_IMODE(facts.st_mode) != 0o700
    ):
        raise WorkerBuildError("worker build private run-root creation rejected")


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
            raise WorkerBuildError(f"{label} must be one bounded regular file")
        raw = bytearray()
        while len(raw) <= maximum:
            chunk = os.read(descriptor, min(1 << 20, maximum + 1 - len(raw)))
            if not chunk:
                break
            raw.extend(chunk)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise WorkerBuildError(f"{label} could not be read") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
    identity = lambda item: (  # noqa: E731
        item.st_dev,
        item.st_ino,
        item.st_mode,
        item.st_nlink,
        item.st_size,
        item.st_mtime_ns,
        item.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(raw) != before.st_size:
        raise WorkerBuildError(f"{label} changed during read")
    return bytes(raw)


def _write_outputs(paths: Mapping[str, Path], payloads: Mapping[str, bytes]) -> None:
    if set(payloads) != set(OUTPUT_ROLES):
        raise WorkerBuildError("worker build payload inventory mismatch")
    created: list[Path] = []
    try:
        for role in OUTPUT_ROLES:
            raw = payloads[role]
            maximum = (
                MAX_GOVERNANCE_BYTES
                if role == "worker_build_report"
                else planner.MAX_HOST_BINARY_BYTES
            )
            if not 0 < len(raw) <= maximum:
                raise WorkerBuildError(f"{role} output exceeds its bound")
            descriptor = os.open(
                paths[role],
                os.O_WRONLY
                | os.O_CREAT
                | os.O_EXCL
                | getattr(os, "O_NOFOLLOW", 0)
                | getattr(os, "O_CLOEXEC", 0),
                0o500 if role in BINARY_OUTPUT_ROLES else 0o400,
            )
            created.append(paths[role])
            try:
                view = memoryview(raw)
                offset = 0
                while offset < len(view):
                    written = os.write(descriptor, view[offset:])
                    if written <= 0:
                        raise WorkerBuildError(f"{role} output write made no progress")
                    offset += written
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            _sync_directory(paths[role].parent)
    except BaseException:
        for path in reversed(created):
            path.unlink(missing_ok=True)
        raise


def _remove_completed_run_root(path: Path) -> None:
    shutil.rmtree(path)
    if path.exists() or path.is_symlink():
        raise WorkerBuildError("completed worker build run root remains")


def _sealed_program_image_computer(r0vm_descriptor: int) -> Callable[[bytes], str]:
    def compute(raw: bytes) -> str:
        if not raw.startswith(b"R0BF") or not 4 < len(raw) <= planner.MAX_PROGRAM_BINARY_BYTES:
            raise WorkerBuildError("V7 program is not one bounded R0BF binary")
        flags = getattr(os, "MFD_CLOEXEC", 0) | getattr(os, "MFD_ALLOW_SEALING", 0)
        try:
            descriptor = os.memfd_create("zrpf-v7-program", flags)
            view = memoryview(raw)
            offset = 0
            while offset < len(view):
                written = os.write(descriptor, view[offset:])
                if written <= 0:
                    raise WorkerBuildError("V7 program memfd write made no progress")
                offset += written
            os.lseek(descriptor, 0, os.SEEK_SET)
            fcntl.fcntl(
                descriptor,
                fcntl.F_ADD_SEALS,
                fcntl.F_SEAL_SEAL | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW | fcntl.F_SEAL_WRITE,
            )
            return image_checker._compute_program_image_id(r0vm_descriptor, descriptor)
        except (OSError, image_checker.BuildRecordError) as exc:
            raise WorkerBuildError("V7 program image-ID computation failed") from exc
        finally:
            if "descriptor" in locals():
                os.close(descriptor)

    return compute


def _checked_runner_posture(value: object) -> dict[str, Any]:
    try:
        return planner.check_runner_security_posture(value)
    except planner.RebuildPlanError as exc:
        raise WorkerBuildError("worker build runner posture rejected") from exc


def _sync_directory(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--post-pin-governance", type=Path, required=True)
    parser.add_argument("--packet-r0vm", type=Path, required=True)
    parser.add_argument("--risc0-home", type=Path, required=True)
    parser.add_argument("--cargo-registry-dir", type=Path, required=True)
    parser.add_argument("--docker", type=Path, required=True)
    for role in OUTPUT_ROLES:
        parser.add_argument(f"--{role.replace('_', '-')}-out", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    r0vm_descriptor: int | None = None
    try:
        require_exact_runtime_r0vm(args.risc0_home, args.packet_r0vm)
        r0vm_descriptor = image_checker._open_verified_r0vm(
            args.packet_r0vm,
            planner.TOOLCHAIN["r0vm_sha256"],
        )
        runner = DockerBuildRunner(
            risc0_home=args.risc0_home,
            cargo_registry_directory=args.cargo_registry_dir,
            docker=args.docker,
        )
        execute_worker_build_stage(
            source_commit=args.source_commit,
            governance_path=args.post_pin_governance,
            build_run_root=Path(BUILD_RUN_ROOT),
            output_paths={role: getattr(args, f"{role}_out") for role in OUTPUT_ROLES},
            runner=runner,
            image_id_computer=_sealed_program_image_computer(r0vm_descriptor),
        )
    except (
        WorkerBuildError,
        ExecutionError,
        IncompleteContainerCleanupError,
        image_checker.BuildRecordError,
        governance.GovernanceError,
        OSError,
    ) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    finally:
        if r0vm_descriptor is not None:
            os.close(r0vm_descriptor)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
