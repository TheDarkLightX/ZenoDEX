#!/usr/bin/env python3
"""Run one bounded, candidate-only source-opened Spot V6 proof chain.

The runner snapshots five explicitly pinned executables, recomputes all four
program image IDs through the pinned r0vm, and executes the governed singleton
chain in dependency order:

    leaf -> level one -> level two -> settlement

Every proof stage receives a fresh private TMPDIR below a caller-supplied
private scratch parent. Child processes receive only the documented environment
allowlist. Output is staged privately, checked for exact inventory and hash
relations, and published with Linux ``renameat2(RENAME_NOREPLACE)``.

Successful execution creates candidate proof artifacts. It does not perform the
separate retained-verifier replay and supplies no availability, finality,
ledger, release, settlement, privacy, general-scaling, or production authority.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from contextlib import ExitStack
from dataclasses import dataclass
from functools import partial
from pathlib import Path
from typing import Any, Mapping, NoReturn, Sequence

if __package__:
    from tools import zrpf_v3_replay_process as bounded_process
    from tools import zrpf_v3_replay_sealed_executable as sealed_executable
else:  # pragma: no cover - direct script execution
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import zrpf_v3_replay_process as bounded_process
    from tools import zrpf_v3_replay_sealed_executable as sealed_executable


REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_proof_chain_candidate/v2"
ERROR_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_proof_chain_error/v1"
SUCCINCT_PROFILE_ID = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
STAGE_ORDER = ("leaf", "level_one", "level_two", "settlement")
EXECUTABLE_ROLES = (
    "r0vm",
    "leaf_prover",
    "level_one_prover",
    "level_two_prover",
    "settlement_prover",
)
ARTIFACT_NAMES = (
    "source_request.json",
    "source_proof.json",
    "adapter_receipt.json",
    "leaf_source_envelope.bin",
    "leaf_receipt.json",
    "leaf_mutation_receipt.json",
    "l1_receipt.json",
    "l1_mutation_receipt.json",
    "l2_receipt.json",
    "l2_mutation_receipt.json",
    "settlement_receipt.json",
    "settlement_mutation_receipt.json",
    "settlement_admission_journal.bin",
    "settlement_guest_input.bin",
    "settlement_replay.bin",
    "settlement_da_certificate.bin",
    "spot_value_leaf_v6.bin",
    "spot_value_aggregate_l1_v6.bin",
    "spot_value_aggregate_l2_v6.bin",
    "source_opened_spot_settlement_v6.bin",
)
STAGE_REPORT_NAMES = (
    "leaf_report.json",
    "level_one_report.json",
    "level_two_report.json",
    "settlement_report.json",
)
PROGRAM_ARTIFACTS = {
    "leaf": "spot_value_leaf_v6.bin",
    "level_one": "spot_value_aggregate_l1_v6.bin",
    "level_two": "spot_value_aggregate_l2_v6.bin",
    "settlement": "source_opened_spot_settlement_v6.bin",
}
ENVIRONMENT_ALLOWLIST = (
    "HOME",
    "LANG",
    "LC_ALL",
    "PATH",
    "RISC0_PROVER",
    "RISC0_SERVER_PATH",
    "TMPDIR",
    "TZ",
)
NONCLAIMS = (
    "candidate artifacts require a separate pinned-verifier replay before any scoped replay claim",
    "this runner grants no data-availability, finality, ledger, release, settlement, privacy, general-scaling, or production authority",
    "proof-byte determinism, runtime resource containment, sandbox isolation, same-UID resistance, crash durability, and caller-supplied scratch encryption are not verified",
)

MAX_INPUT_BYTES = 16 * 1024 * 1024
MAX_PROGRAM_BYTES = 16 * 1024 * 1024
MAX_STAGE_ARTIFACT_BYTES = 64 * 1024 * 1024
MAX_TOTAL_AUTHORITY_INPUT_BYTES = 128 * 1024 * 1024
MAX_TOTAL_CANDIDATE_ARTIFACT_BYTES = 256 * 1024 * 1024
MAX_CAPTURE_BYTES = 128 * 1024
MAX_JSON_NESTING = 64
MAX_JSON_NODES = 1_000_000
MIN_TIMEOUT_SECONDS = 1
MAX_TIMEOUT_SECONDS = 6 * 60 * 60
DEFAULT_TIMEOUT_SECONDS = 2 * 60 * 60
_HASH = re.compile(r"[0-9a-f]{64}")
_R0BF_MAGIC = b"R0BF"


class ProofChainError(ValueError):
    """Stable fail-closed proof-chain orchestration rejection."""


@dataclass(frozen=True)
class ExecutablePin:
    """One executable path plus a separately supplied expected digest."""

    path: Path
    sha256: str


@dataclass(frozen=True)
class ProgramPin:
    """One RISC0 program binary plus its expected digest and image ID."""

    path: Path
    sha256: str
    image_id: str


@dataclass(frozen=True)
class ProofChainResult:
    """Published candidate facts. Authority fields are permanently false."""

    output_directory: Path
    proof_chain_report_sha256: str
    artifact_count: int
    report_count: int
    candidate_proof_chain_built: bool = True
    scoped_local_replay_claim_allowed: bool = False
    release_authority: bool = False
    settlement_authority: bool = False
    production_authority: bool = False


@dataclass(frozen=True)
class _StagePaths:
    root: Path
    home: Path
    temporary: Path
    output: Path


@dataclass(frozen=True)
class _PinnedExecutables:
    r0vm: sealed_executable.SealedExecutable
    leaf: sealed_executable.SealedExecutable
    level_one: sealed_executable.SealedExecutable
    level_two: sealed_executable.SealedExecutable
    settlement: sealed_executable.SealedExecutable


def run_proof_chain(
    *,
    scratch_parent: Path,
    output_directory: Path,
    r0vm: ExecutablePin,
    leaf_prover: ExecutablePin,
    level_one_prover: ExecutablePin,
    level_two_prover: ExecutablePin,
    settlement_prover: ExecutablePin,
    source_request: Path,
    source_proof: Path,
    adapter_receipt: Path,
    leaf_program: ProgramPin,
    level_one_program: ProgramPin,
    level_two_program: ProgramPin,
    settlement_program: ProgramPin,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
) -> ProofChainResult:
    """Execute, validate, and atomically publish one candidate proof chain."""

    if "RISC0_DEV_MODE" in os.environ:
        raise ProofChainError("ambient RISC0_DEV_MODE is forbidden")
    if type(timeout_seconds) is not int or not (
        MIN_TIMEOUT_SECONDS <= timeout_seconds <= MAX_TIMEOUT_SECONDS
    ):
        raise ProofChainError("stage timeout is outside the governed bound")

    scratch = _private_scratch_parent(scratch_parent)
    output = _new_output_path(output_directory)
    input_raw = {
        "source_request.json": _read_bounded_regular_file(
            source_request, "source request", MAX_INPUT_BYTES
        ),
        "source_proof.json": _read_bounded_regular_file(
            source_proof, "source proof", MAX_INPUT_BYTES
        ),
        "adapter_receipt.json": _read_bounded_regular_file(
            adapter_receipt, "adapter receipt", MAX_INPUT_BYTES
        ),
    }
    for label, name in (
        ("source request", "source_request.json"),
        ("source proof", "source_proof.json"),
        ("adapter receipt", "adapter_receipt.json"),
    ):
        _require_json_object(input_raw[name], label)

    program_pins = {
        "leaf": leaf_program,
        "level_one": level_one_program,
        "level_two": level_two_program,
        "settlement": settlement_program,
    }
    program_raw = {
        role: _snapshot_program(pin, role) for role, pin in program_pins.items()
    }
    if sum(map(len, (*input_raw.values(), *program_raw.values()))) > (
        MAX_TOTAL_AUTHORITY_INPUT_BYTES
    ):
        raise ProofChainError("authority input bytes exceed the governed aggregate bound")
    executable_pins = {
        "r0vm": r0vm,
        "leaf_prover": leaf_prover,
        "level_one_prover": level_one_prover,
        "level_two_prover": level_two_prover,
        "settlement_prover": settlement_prover,
    }
    for role, pin in executable_pins.items():
        _require_hash(pin.sha256, f"{role.replace('_', ' ')} expected SHA-256")

    workspace: Path | None = None
    try:
        with ExitStack() as stack:
            executables = _seal_executables(stack, executable_pins)
            workspace = Path(
                tempfile.mkdtemp(prefix=".zrpf-spot-v6-chain-", dir=scratch)
            )
            workspace.chmod(0o700)
            inputs = _private_directory(workspace / "inputs")
            for name, raw in input_raw.items():
                _write_private_file(inputs / name, raw)
            for role, raw in program_raw.items():
                _write_private_file(inputs / PROGRAM_ARTIFACTS[role], raw)

            identity_stage = _new_stage(workspace, "program-identity")
            _verify_program_identities(
                executables.r0vm,
                identity_stage,
                inputs,
                program_pins,
                timeout_seconds,
            )
            artifacts, reports = _execute_chain(
                executables,
                workspace,
                inputs,
                input_raw,
                program_raw,
                program_pins,
                timeout_seconds,
            )
            report = _candidate_report(
                executable_pins,
                executables,
                program_pins,
                program_raw,
                artifacts,
                reports,
            )
            report_raw = _canonical_json(report)
            publish = _assemble_candidate(workspace, artifacts, reports, report_raw)
            _validate_candidate_tree(publish)
            _atomic_publish_candidate(publish, output)
            return ProofChainResult(
                output_directory=output,
                proof_chain_report_sha256=_sha256(report_raw),
                artifact_count=len(ARTIFACT_NAMES),
                report_count=len(STAGE_REPORT_NAMES),
            )
    except ProofChainError:
        raise
    except RuntimeError as exc:
        raise ProofChainError("executable snapshot or bounded process failed") from exc
    finally:
        if workspace is not None and workspace.exists():
            shutil.rmtree(workspace)


def _seal_executables(
    stack: ExitStack,
    pins: Mapping[str, ExecutablePin],
) -> _PinnedExecutables:
    opened: dict[str, sealed_executable.SealedExecutable] = {}
    for role in EXECUTABLE_ROLES:
        pin = pins[role]
        try:
            executable = stack.enter_context(sealed_executable.SealedExecutable(pin.path))
        except RuntimeError as exc:
            raise ProofChainError(
                f"{role.replace('_', ' ')} executable snapshot failed"
            ) from exc
        if executable.identity.sha256 != pin.sha256:
            raise ProofChainError(f"{role.replace('_', ' ')} SHA-256 mismatch")
        opened[role] = executable
    return _PinnedExecutables(
        r0vm=opened["r0vm"],
        leaf=opened["leaf_prover"],
        level_one=opened["level_one_prover"],
        level_two=opened["level_two_prover"],
        settlement=opened["settlement_prover"],
    )


def _execute_chain(
    executables: _PinnedExecutables,
    workspace: Path,
    inputs: Path,
    input_raw: Mapping[str, bytes],
    program_raw: Mapping[str, bytes],
    program_pins: Mapping[str, ProgramPin],
    timeout_seconds: int,
) -> tuple[dict[str, bytes], dict[str, bytes]]:
    leaf_stage = _new_stage(workspace, "leaf")
    leaf_stdout = _run_prover(
        "leaf",
        executables.leaf,
        executables.r0vm,
        leaf_stage,
        (
            "--receipt-out",
            str(leaf_stage.output / "leaf_receipt.json"),
            "--source-envelope-out",
            str(leaf_stage.output / "leaf_source_envelope.bin"),
            "--source-request",
            str(inputs / "source_request.json"),
            "--source-proof",
            str(inputs / "source_proof.json"),
            "--adapter-receipt",
            str(inputs / "adapter_receipt.json"),
        ),
        timeout_seconds,
    )
    leaf_output = _read_stage_outputs(
        "leaf", leaf_stage.output, ("leaf_receipt.json", "leaf_source_envelope.bin")
    )
    leaf_report = _validate_leaf_report(
        leaf_stdout,
        leaf_output,
        input_raw,
        program_raw["leaf"],
        program_pins["leaf"],
    )
    leaf_mutation = _exact_seal_mutation(
        leaf_output["leaf_receipt.json"], "leaf"
    )

    level_one_stage = _new_stage(workspace, "level-one")
    level_one_stdout = _run_prover(
        "level_one",
        executables.level_one,
        executables.r0vm,
        level_one_stage,
        (
            "--receipt-out",
            str(level_one_stage.output / "l1_receipt.json"),
            "--child",
            str(leaf_stage.output / "leaf_receipt.json"),
        ),
        timeout_seconds,
    )
    level_one_output = _read_stage_outputs(
        "level_one", level_one_stage.output, ("l1_receipt.json",)
    )
    level_one_report = _validate_aggregate_report(
        level_one_stdout,
        role="level_one",
        receipt_name="l1_receipt.json",
        receipt=level_one_output["l1_receipt.json"],
        child=leaf_output["leaf_receipt.json"],
        program=program_pins["level_one"],
    )
    level_one_mutation = _exact_seal_mutation(
        level_one_output["l1_receipt.json"], "level_one"
    )

    level_two_stage = _new_stage(workspace, "level-two")
    level_two_stdout = _run_prover(
        "level_two",
        executables.level_two,
        executables.r0vm,
        level_two_stage,
        (
            "--receipt-out",
            str(level_two_stage.output / "l2_receipt.json"),
            "--child",
            str(level_one_stage.output / "l1_receipt.json"),
        ),
        timeout_seconds,
    )
    level_two_output = _read_stage_outputs(
        "level_two", level_two_stage.output, ("l2_receipt.json",)
    )
    level_two_report = _validate_aggregate_report(
        level_two_stdout,
        role="level_two",
        receipt_name="l2_receipt.json",
        receipt=level_two_output["l2_receipt.json"],
        child=level_one_output["l1_receipt.json"],
        program=program_pins["level_two"],
    )
    level_two_mutation = _exact_seal_mutation(
        level_two_output["l2_receipt.json"], "level_two"
    )

    settlement_stage = _new_stage(workspace, "settlement")
    settlement_stdout = _run_prover(
        "settlement",
        executables.settlement,
        executables.r0vm,
        settlement_stage,
        (
            "--receipt-out",
            str(settlement_stage.output / "settlement_receipt.json"),
            "--journal-out",
            str(settlement_stage.output / "settlement_admission_journal.bin"),
            "--mutation-out",
            str(settlement_stage.output / "settlement_mutation_receipt.json"),
            "--guest-input-out",
            str(settlement_stage.output / "settlement_guest_input.bin"),
            "--replay-out",
            str(settlement_stage.output / "settlement_replay.bin"),
            "--da-certificate-out",
            str(settlement_stage.output / "settlement_da_certificate.bin"),
            "--source-envelope",
            str(leaf_stage.output / "leaf_source_envelope.bin"),
            "--l2-receipt",
            str(level_two_stage.output / "l2_receipt.json"),
        ),
        timeout_seconds,
    )
    settlement_names = (
        "settlement_receipt.json",
        "settlement_mutation_receipt.json",
        "settlement_admission_journal.bin",
        "settlement_guest_input.bin",
        "settlement_replay.bin",
        "settlement_da_certificate.bin",
    )
    settlement_output = _read_stage_outputs(
        "settlement", settlement_stage.output, settlement_names
    )
    settlement_report = _validate_settlement_report(
        settlement_stdout,
        settlement_output,
        leaf_output["leaf_source_envelope.bin"],
        level_two_output["l2_receipt.json"],
        program_pins["settlement"],
    )
    expected_settlement_mutation = _exact_seal_mutation(
        settlement_output["settlement_receipt.json"], "settlement"
    )
    if settlement_output["settlement_mutation_receipt.json"] != expected_settlement_mutation:
        raise ProofChainError(
            "settlement mutation must XOR Succinct seal word 1 by exactly one"
        )

    artifacts = {
        **dict(input_raw),
        "leaf_source_envelope.bin": leaf_output["leaf_source_envelope.bin"],
        "leaf_receipt.json": leaf_output["leaf_receipt.json"],
        "leaf_mutation_receipt.json": leaf_mutation,
        "l1_receipt.json": level_one_output["l1_receipt.json"],
        "l1_mutation_receipt.json": level_one_mutation,
        "l2_receipt.json": level_two_output["l2_receipt.json"],
        "l2_mutation_receipt.json": level_two_mutation,
        **settlement_output,
        **{PROGRAM_ARTIFACTS[role]: raw for role, raw in program_raw.items()},
    }
    if tuple(artifacts) != ARTIFACT_NAMES:
        raise ProofChainError("internal candidate artifact ordering mismatch")
    if sum(map(len, artifacts.values())) > MAX_TOTAL_CANDIDATE_ARTIFACT_BYTES:
        raise ProofChainError("candidate artifact bytes exceed the governed aggregate bound")
    reports = {
        "leaf_report.json": leaf_report,
        "level_one_report.json": level_one_report,
        "level_two_report.json": level_two_report,
        "settlement_report.json": settlement_report,
    }
    return artifacts, reports


def _run_prover(
    role: str,
    executable: sealed_executable.SealedExecutable,
    r0vm: sealed_executable.SealedExecutable,
    stage: _StagePaths,
    arguments: tuple[str, ...],
    timeout_seconds: int,
) -> bytes:
    request = bounded_process.ProcessRequest(
        command=(executable.command_path, *arguments),
        cwd=stage.root,
        env=_stage_environment(stage, r0vm),
        timeout_seconds=timeout_seconds,
        output_limit_bytes=MAX_CAPTURE_BYTES,
        profile=bounded_process.ProcessProfile.BUILD,
        pass_fds=tuple(sorted(set((*executable.pass_fds, *r0vm.pass_fds)))),
    )
    try:
        completed = _run_governed_process(request)
    except (OSError, RuntimeError, ValueError) as exc:
        raise ProofChainError(f"{role} prover process failed") from exc
    if completed.returncode != 0:
        raise ProofChainError(f"{role} prover returned nonzero")
    if completed.stderr:
        raise ProofChainError(f"{role} prover emitted stderr")
    return completed.stdout


def _stage_environment(
    stage: _StagePaths,
    r0vm: sealed_executable.SealedExecutable,
) -> dict[str, str]:
    environment = {
        "HOME": str(stage.home),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "RISC0_PROVER": "ipc",
        "RISC0_SERVER_PATH": r0vm.command_path,
        "TMPDIR": str(stage.temporary),
        "TZ": "UTC",
    }
    if tuple(sorted(environment)) != ENVIRONMENT_ALLOWLIST:
        raise ProofChainError("proof-stage environment allowlist mismatch")
    return environment


def _verify_program_identities(
    r0vm: sealed_executable.SealedExecutable,
    stage: _StagePaths,
    inputs: Path,
    pins: Mapping[str, ProgramPin],
    timeout_seconds: int,
) -> None:
    for role in STAGE_ORDER:
        request = bounded_process.ProcessRequest(
            command=(
                r0vm.command_path,
                "--elf",
                str(inputs / PROGRAM_ARTIFACTS[role]),
                "--id",
            ),
            cwd=stage.root,
            env=_stage_environment(stage, r0vm),
            timeout_seconds=timeout_seconds,
            output_limit_bytes=1024,
            profile=bounded_process.ProcessProfile.TOOL,
            pass_fds=r0vm.pass_fds,
        )
        try:
            completed = _run_governed_process(request)
        except (OSError, RuntimeError, ValueError) as exc:
            raise ProofChainError(f"{role} image-ID recomputation failed") from exc
        if completed.returncode != 0 or completed.stderr:
            raise ProofChainError(f"{role} image-ID recomputation failed")
        expected_stdout = (pins[role].image_id + "\n").encode()
        if completed.stdout != expected_stdout:
            raise ProofChainError(f"{role} image ID mismatch")


def _run_governed_process(
    request: bounded_process.ProcessRequest,
) -> subprocess.CompletedProcess[bytes]:
    """Run one stage and ensure its complete process group is gone."""

    if request.timeout_seconds <= 0 or request.output_limit_bytes <= 0:
        raise ValueError("subprocess bounds must be positive")
    process = subprocess.Popen(
        request.command,
        cwd=request.cwd,
        env=request.env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        pass_fds=request.pass_fds,
        preexec_fn=partial(
            bounded_process._apply_process_profile,
            request.profile,
            request.timeout_seconds,
            request.output_limit_bytes,
        ),
        start_new_session=True,
    )
    if process.stdout is None or process.stderr is None:
        _kill_process_group(process)
        raise RuntimeError("subprocess pipes were not created")
    deadline = time.monotonic() + request.timeout_seconds
    try:
        stdout, stderr = bounded_process._capture_bounded(process, request, deadline)
        try:
            return_code = process.wait(timeout=max(0.1, deadline - time.monotonic()))
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError("subprocess timed out") from exc
    except BaseException:
        _kill_process_group(process)
        raise
    _kill_residual_process_group(process.pid)
    return subprocess.CompletedProcess(request.command, return_code, stdout, stderr)


def _kill_process_group(process: subprocess.Popen[bytes]) -> None:
    process_group = process.pid
    try:
        os.killpg(process_group, signal.SIGKILL)
    except ProcessLookupError:
        pass
    for stream in (process.stdout, process.stderr):
        if stream is not None and not stream.closed:
            stream.close()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired as exc:
        process.kill()
        process.wait()
        raise RuntimeError("subprocess leader resisted termination") from exc
    _await_process_group_empty(process_group)


def _kill_residual_process_group(process_group: int) -> None:
    try:
        os.killpg(process_group, signal.SIGKILL)
    except ProcessLookupError:
        return
    _await_process_group_empty(process_group)


def _await_process_group_empty(process_group: int) -> None:
    deadline = time.monotonic() + 5
    while True:
        try:
            os.killpg(process_group, 0)
        except ProcessLookupError:
            return
        except PermissionError as exc:
            raise RuntimeError("subprocess group ownership changed") from exc
        if time.monotonic() >= deadline:
            raise RuntimeError("subprocess group remained populated after termination")
        time.sleep(0.01)


def _validate_leaf_report(
    raw: bytes,
    outputs: Mapping[str, bytes],
    inputs: Mapping[str, bytes],
    program_raw: bytes,
    program: ProgramPin,
) -> bytes:
    report = _load_exact_report(
        raw,
        {
            "action_nullifier_root",
            "adapter_receipt_sha256",
            "candidate_accepted",
            "guest_program_binary_bytes",
            "guest_program_binary_sha256",
            "nonclaims",
            "ok",
            "receipt_bytes",
            "receipt_profile_id",
            "receipt_sha256",
            "schema",
            "source_envelope_bytes",
            "source_envelope_sha256",
            "source_proof_sha256",
            "statement_hash",
            "status",
            "v6_image_id",
            "verified_program_manifest_root",
        },
        "leaf",
    )
    receipt = outputs["leaf_receipt.json"]
    envelope = outputs["leaf_source_envelope.bin"]
    _require_equal(
        report["schema"],
        "zenodex/zrpf_source_opened_spot_value_leaf_v6_proof_report/v2",
        "leaf schema",
    )
    _require_equal(
        report["status"],
        "source_opened_spot_value_leaf_v6_succinct_receipt_verified",
        "leaf status",
    )
    _require_true(report["ok"], "leaf ok")
    _require_true(report["candidate_accepted"], "leaf candidate_accepted")
    _require_equal(report["v6_image_id"], program.image_id, "leaf image ID")
    _require_equal(
        report["receipt_profile_id"], SUCCINCT_PROFILE_ID, "leaf receipt profile"
    )
    _require_size_hash(report, "receipt", receipt, "leaf receipt")
    _require_size_hash(report, "source_envelope", envelope, "leaf source envelope")
    _require_equal(
        report["source_proof_sha256"],
        _sha256(inputs["source_proof.json"]),
        "leaf source proof SHA-256",
    )
    _require_equal(
        report["adapter_receipt_sha256"],
        _sha256(inputs["adapter_receipt.json"]),
        "leaf adapter receipt SHA-256",
    )
    _require_equal(
        report["guest_program_binary_bytes"],
        len(program_raw),
        "leaf program byte length",
    )
    _require_equal(
        report["guest_program_binary_sha256"],
        program.sha256,
        "leaf program SHA-256",
    )
    for field in (
        "action_nullifier_root",
        "statement_hash",
        "verified_program_manifest_root",
    ):
        _require_nonzero_hash(report[field], f"leaf {field}")
    _require_equal(
        report["nonclaims"],
        [
            "the V6 receipt alone grants no ledger, settlement, release, or production authority",
            "this report proves one bounded singleton Spot transition and no maximum-fanout throughput claim",
        ],
        "leaf nonclaims",
    )
    return raw


def _validate_aggregate_report(
    raw: bytes,
    *,
    role: str,
    receipt_name: str,
    receipt: bytes,
    child: bytes,
    program: ProgramPin,
) -> bytes:
    del receipt_name
    report = _load_exact_report(
        raw,
        {
            "child_receipt_sha256",
            "image_id",
            "ok",
            "receipt_bytes",
            "receipt_sha256",
            "schema",
            "status",
            "verified_child_count",
        },
        role,
    )
    label = "l1" if role == "level_one" else "l2"
    _require_equal(
        report["schema"],
        f"zenodex/zrpf_source_opened_spot_value_aggregate_{label}_v6_proof_report/v1",
        f"{role} schema",
    )
    _require_equal(
        report["status"],
        f"source_opened_spot_value_aggregate_{label}_v6_succinct_receipt_verified",
        f"{role} status",
    )
    _require_true(report["ok"], f"{role} ok")
    _require_equal(report["image_id"], program.image_id, f"{role} image ID")
    _require_equal(report["verified_child_count"], 1, f"{role} child count")
    _require_equal(
        report["child_receipt_sha256"],
        _sha256(child),
        f"{role} child receipt SHA-256",
    )
    _require_size_hash(report, "receipt", receipt, f"{role} receipt")
    return raw


def _validate_settlement_report(
    raw: bytes,
    outputs: Mapping[str, bytes],
    source_envelope: bytes,
    level_two_receipt: bytes,
    program: ProgramPin,
) -> bytes:
    report = _load_exact_report(
        raw,
        {
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
        },
        "settlement",
    )
    _require_equal(
        report["schema"],
        "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1",
        "settlement schema",
    )
    _require_equal(
        report["status"],
        "source_opened_spot_settlement_v6_succinct_receipt_verified",
        "settlement status",
    )
    _require_true(report["ok"], "settlement ok")
    _require_true(report["mutation_rejected"], "settlement mutation_rejected")
    _require_equal(report["action_count"], 1, "settlement action_count")
    _require_equal(
        report["consumed_object_count"], 1, "settlement consumed_object_count"
    )
    _require_equal(report["image_id"], program.image_id, "settlement image ID")
    _require_equal(
        report["settlement_program_id"],
        program.image_id,
        "settlement program ID",
    )
    _require_equal(
        report["succinct_receipt_profile_id"],
        SUCCINCT_PROFILE_ID,
        "settlement receipt profile",
    )
    _require_equal(
        report["l2_receipt_sha256"],
        _sha256(level_two_receipt),
        "settlement L2 receipt SHA-256",
    )
    _require_equal(
        report["source_envelope_sha256"],
        _sha256(source_envelope),
        "settlement source envelope SHA-256",
    )
    _require_size_hash(
        report, "receipt", outputs["settlement_receipt.json"], "settlement receipt"
    )
    _require_equal(
        report["mutation_receipt_sha256"],
        _sha256(outputs["settlement_mutation_receipt.json"]),
        "settlement mutation receipt SHA-256",
    )
    _require_size_hash(
        report,
        "admission_journal",
        outputs["settlement_admission_journal.bin"],
        "settlement admission journal",
    )
    _require_size_hash(
        report,
        "guest_input",
        outputs["settlement_guest_input.bin"],
        "settlement guest input",
    )
    _require_size_hash(
        report, "replay", outputs["settlement_replay.bin"], "settlement replay"
    )
    _require_equal(
        report["data_availability_certificate_bytes"],
        len(outputs["settlement_da_certificate.bin"]),
        "settlement DA certificate byte length",
    )
    _require_equal(
        report["data_availability_certificate_sha256"],
        _sha256(outputs["settlement_da_certificate.bin"]),
        "settlement DA certificate SHA-256",
    )
    for field in ("settlement_claim_binding", "settlement_program_manifest_root"):
        _require_nonzero_hash(report[field], f"settlement {field}")
    _require_equal(
        report["nonclaims"],
        [
            "the accepted source receipt does not establish an end-user signature scheme",
            "this local receipt grants no release, governance, Tau-finality, or production authority",
        ],
        "settlement nonclaims",
    )
    return raw


def _candidate_report(
    executable_pins: Mapping[str, ExecutablePin],
    executables: _PinnedExecutables,
    program_pins: Mapping[str, ProgramPin],
    program_raw: Mapping[str, bytes],
    artifacts: Mapping[str, bytes],
    reports: Mapping[str, bytes],
) -> dict[str, Any]:
    opened = {
        "r0vm": executables.r0vm,
        "leaf_prover": executables.leaf,
        "level_one_prover": executables.level_one,
        "level_two_prover": executables.level_two,
        "settlement_prover": executables.settlement,
    }
    return {
        "artifact_count": len(ARTIFACT_NAMES),
        "artifacts": [
            {
                "artifact": name,
                "sha256": _sha256(artifacts[name]),
                "size_bytes": len(artifacts[name]),
            }
            for name in ARTIFACT_NAMES
        ],
        "candidate_proof_chain_built": True,
        "crash_durable_publication_verified": False,
        "environment_allowlist": list(ENVIRONMENT_ALLOWLIST),
        "exact_seal_mutation_pairs_constructed": 4,
        "executables": [
            {
                "role": role,
                "sha256": executable_pins[role].sha256,
                "size_bytes": opened[role].identity.size_bytes,
                "transport": opened[role].identity.transport,
            }
            for role in EXECUTABLE_ROLES
        ],
        "independent_retained_replay_verified": False,
        "network_isolation_verified": False,
        "runtime_resource_containment_verified": False,
        "nonclaims": list(NONCLAIMS),
        "positive_succinct_receipt_count": 4,
        "production_authority": False,
        "programs": [
            {
                "image_id": program_pins[role].image_id,
                "program": role,
                "sha256": program_pins[role].sha256,
                "size_bytes": len(program_raw[role]),
            }
            for role in STAGE_ORDER
        ],
        "proof_byte_determinism_verified": False,
        "proof_generation_reproducibility_verified": False,
        "release_authority": False,
        "report_count": len(STAGE_REPORT_NAMES),
        "reports": [
            {
                "report": name,
                "sha256": _sha256(reports[name]),
                "size_bytes": len(reports[name]),
            }
            for name in STAGE_REPORT_NAMES
        ],
        "schema": REPORT_SCHEMA,
        "same_uid_resistance_verified": False,
        "sandbox_authority": False,
        "scoped_local_replay_claim_allowed": False,
        "scratch_parent_encryption_verified": False,
        "settlement_authority": False,
        "source_to_binary_reproducibility_verified": False,
        "stage_order": list(STAGE_ORDER),
        "status": "candidate_proof_chain_generated_authority_false",
    }


def _snapshot_program(pin: ProgramPin, role: str) -> bytes:
    _require_hash(pin.sha256, f"{role} program expected SHA-256")
    _require_hash(pin.image_id, f"{role} expected image ID")
    if pin.image_id == "0" * 64:
        raise ProofChainError(f"{role} expected image ID is zero")
    raw = _read_bounded_regular_file(
        pin.path, f"{role} program binary", MAX_PROGRAM_BYTES
    )
    if not raw.startswith(_R0BF_MAGIC):
        raise ProofChainError(f"{role} program binary lacks R0BF magic")
    if _sha256(raw) != pin.sha256:
        raise ProofChainError(f"{role} program SHA-256 mismatch")
    return raw


def _private_scratch_parent(path: Path) -> Path:
    candidate = _absolute(path)
    _reject_symlink_components(candidate, "scratch parent")
    try:
        metadata = candidate.lstat()
    except OSError as exc:
        raise ProofChainError("scratch parent is unavailable") from exc
    if candidate.is_symlink() or not stat.S_ISDIR(metadata.st_mode):
        raise ProofChainError("scratch parent must be a real directory")
    if stat.S_IMODE(metadata.st_mode) != 0o700:
        raise ProofChainError("scratch parent mode must be 0700")
    if metadata.st_uid != os.geteuid():
        raise ProofChainError("scratch parent must be owned by the current user")
    return candidate


def _new_output_path(path: Path) -> Path:
    candidate = _absolute(path)
    _reject_symlink_components(candidate.parent, "output parent")
    if candidate.exists() or candidate.is_symlink():
        raise ProofChainError("output directory already exists")
    try:
        parent = candidate.parent.lstat()
    except OSError as exc:
        raise ProofChainError("output parent is unavailable") from exc
    if candidate.parent.is_symlink() or not stat.S_ISDIR(parent.st_mode):
        raise ProofChainError("output parent must be a real directory")
    return candidate


def _new_stage(workspace: Path, label: str) -> _StagePaths:
    root = _private_directory(workspace / f"stage-{label}")
    home = _private_directory(root / "home")
    temporary = _private_directory(root / "tmp")
    output = _private_directory(root / "out")
    return _StagePaths(root, home, temporary, output)


def _private_directory(path: Path) -> Path:
    path.mkdir(mode=0o700)
    path.chmod(0o700)
    return path


def _read_stage_outputs(
    role: str,
    output: Path,
    expected: Sequence[str],
) -> dict[str, bytes]:
    observed = set()
    for candidate in output.iterdir():
        if candidate.is_symlink() or not candidate.is_file():
            raise ProofChainError(f"{role} output inventory contains a non-file")
        observed.add(candidate.name)
    if observed != set(expected):
        raise ProofChainError(f"{role} output inventory mismatch")
    return {
        name: _read_bounded_regular_file(
            output / name, f"{role} output {name}", MAX_STAGE_ARTIFACT_BYTES
        )
        for name in expected
    }


def _read_bounded_regular_file(path: Path, label: str, maximum_bytes: int) -> bytes:
    path = _absolute(path)
    _reject_symlink_components(path.parent, f"{label} parent")
    # O_NONBLOCK makes a hostile FIFO or device candidate observable to fstat
    # without allowing open(2) to block outside the governed process timeout.
    flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ProofChainError(f"{label} is unavailable or symlinked") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > maximum_bytes
        ):
            raise ProofChainError(f"{label} is not a bounded regular file")
        chunks: list[bytes] = []
        remaining = before.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                raise ProofChainError(f"{label} was truncated while reading")
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(descriptor, 1):
            raise ProofChainError(f"{label} grew while reading")
        after = os.fstat(descriptor)
        identity = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        if identity != (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise ProofChainError(f"{label} changed while reading")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _require_json_object(raw: bytes, label: str) -> dict[str, Any]:
    value = _load_json(raw, label)
    if type(value) is not dict:
        raise ProofChainError(f"{label} must be a JSON object")
    return value


def _load_json(raw: bytes, label: str) -> Any:
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise ProofChainError(f"{label} contains a duplicate JSON key")
            value[key] = item
        return value

    def reject_noninteger_number(_value: str) -> NoReturn:
        raise ProofChainError(f"{label} contains a non-integer JSON number")

    try:
        value = json.loads(
            raw,
            object_pairs_hook=reject_duplicates,
            parse_float=reject_noninteger_number,
            parse_constant=reject_noninteger_number,
        )
    except ProofChainError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ProofChainError(f"{label} is not valid JSON") from exc
    _require_bounded_json_shape(value, label)
    return value


def _require_bounded_json_shape(value: Any, label: str) -> None:
    stack: list[tuple[Any, int]] = [(value, 0)]
    nodes = 0
    while stack:
        node, depth = stack.pop()
        nodes += 1
        if nodes > MAX_JSON_NODES:
            raise ProofChainError(f"{label} exceeds the JSON node bound")
        if depth > MAX_JSON_NESTING:
            raise ProofChainError(f"{label} exceeds the JSON nesting bound")
        if type(node) is dict:
            stack.extend((child, depth + 1) for child in node.values())
        elif type(node) is list:
            stack.extend((child, depth + 1) for child in node)


def _load_exact_report(raw: bytes, fields: set[str], label: str) -> dict[str, Any]:
    if not raw.endswith(b"\n") or b"\n" in raw[:-1]:
        raise ProofChainError(f"{label} report must be one canonical JSON line")
    value = _require_json_object(raw[:-1], f"{label} report")
    if set(value) != fields:
        raise ProofChainError(f"{label} report field set mismatch")
    if _canonical_json(value) != raw:
        raise ProofChainError(f"{label} report is not canonical JSON")
    return value


def _exact_seal_mutation(raw: bytes, role: str) -> bytes:
    receipt = _require_json_object(raw, f"{role} receipt")
    if _canonical_json_preserving_order(receipt) != raw:
        raise ProofChainError(f"{role} receipt is not canonical compact JSON")
    if set(receipt) != {"inner", "journal", "metadata"}:
        raise ProofChainError(f"{role} receipt outer field set mismatch")
    inner = receipt.get("inner")
    if type(inner) is not dict or set(inner) != {"Succinct"}:
        raise ProofChainError(f"{role} receipt is not structurally Succinct")
    succinct = inner.get("Succinct")
    if type(succinct) is not dict:
        raise ProofChainError(f"{role} receipt Succinct body is malformed")
    seal = succinct.get("seal")
    if type(seal) is not list or len(seal) <= 1 or type(seal[1]) is not int:
        raise ProofChainError(f"{role} receipt Succinct seal is malformed")
    seal[1] ^= 1
    return _canonical_json_preserving_order(receipt)


def _assemble_candidate(
    workspace: Path,
    artifacts: Mapping[str, bytes],
    reports: Mapping[str, bytes],
    proof_chain_report: bytes,
) -> Path:
    publish = _private_directory(workspace / "publish")
    artifact_directory = _private_directory(publish / "artifacts")
    report_directory = _private_directory(publish / "reports")
    for name in ARTIFACT_NAMES:
        _write_private_file(artifact_directory / name, artifacts[name])
    for name in STAGE_REPORT_NAMES:
        _write_private_file(report_directory / name, reports[name])
    _write_private_file(publish / "proof_chain_report.json", proof_chain_report)
    _fsync_directory(artifact_directory)
    _fsync_directory(report_directory)
    _fsync_directory(publish)
    return publish


def _write_private_file(path: Path, raw: bytes) -> None:
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
        0o600,
    )
    try:
        view = memoryview(raw)
        offset = 0
        while offset < len(view):
            written = os.write(descriptor, view[offset:])
            if written <= 0:
                raise ProofChainError("private candidate write failed")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _validate_candidate_tree(root: Path) -> None:
    expected_root = {"artifacts", "reports", "proof_chain_report.json"}
    if {path.name for path in root.iterdir()} != expected_root:
        raise ProofChainError("candidate root inventory mismatch")
    _require_exact_file_inventory(root / "artifacts", ARTIFACT_NAMES, "artifact")
    _require_exact_file_inventory(root / "reports", STAGE_REPORT_NAMES, "report")
    report = root / "proof_chain_report.json"
    if report.is_symlink() or not report.is_file():
        raise ProofChainError("candidate proof-chain report is not a regular file")


def _require_exact_file_inventory(
    directory: Path, expected: Sequence[str], label: str
) -> None:
    observed = set()
    for path in directory.iterdir():
        if path.is_symlink() or not path.is_file():
            raise ProofChainError(f"candidate {label} inventory contains a non-file")
        observed.add(path.name)
    if observed != set(expected):
        raise ProofChainError(f"candidate {label} inventory mismatch")


def _atomic_publish_candidate(source: Path, destination: Path) -> None:
    if source.stat().st_dev != destination.parent.stat().st_dev:
        raise ProofChainError("atomic candidate publication requires one filesystem")
    try:
        # Publication has one commit point. No fallible validation or durability
        # claim occurs after the no-replace rename becomes externally visible.
        _fsync_directory(destination.parent)
        _rename_noreplace(source, destination)
    except OSError as exc:
        raise ProofChainError("atomic candidate publication failed") from exc


def _rename_noreplace(source: Path, destination: Path) -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2: Any = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise OSError(errno.ENOSYS, "renameat2 is required")
    renameat2.argtypes = (
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    )
    renameat2.restype = ctypes.c_int
    directory_flags = (
        os.O_RDONLY
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    source_parent = os.open(source.parent, directory_flags)
    try:
        destination_parent = os.open(destination.parent, directory_flags)
        try:
            result = renameat2(
                source_parent,
                os.fsencode(source.name),
                destination_parent,
                os.fsencode(destination.name),
                1,
            )
            if result != 0:
                error = ctypes.get_errno()
                raise OSError(error, os.strerror(error), destination)
        finally:
            _close_descriptor_noexcept(destination_parent)
    finally:
        _close_descriptor_noexcept(source_parent)


def _close_descriptor_noexcept(descriptor: int) -> None:
    """Release a rename directory descriptor without changing commit outcome.

    ``renameat2`` is the publication commit point. A close error after a
    successful rename cannot turn a visible candidate into a reported reject.
    The process is one-shot, so a rare ambiguous close may retain only a
    bounded directory descriptor until process exit.
    """

    try:
        os.close(descriptor)
    except OSError:
        pass


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _require_hash(value: str, label: str) -> None:
    if type(value) is not str or _HASH.fullmatch(value) is None:
        raise ProofChainError(f"{label} must be 64 lowercase hex characters")


def _require_nonzero_hash(value: Any, label: str) -> None:
    if type(value) is not str or _HASH.fullmatch(value) is None or value == "0" * 64:
        raise ProofChainError(f"{label} must be a nonzero lowercase SHA-256 value")


def _require_true(value: Any, label: str) -> None:
    if value is not True:
        raise ProofChainError(f"{label} must be exactly true")


def _require_equal(observed: Any, expected: Any, label: str) -> None:
    if type(observed) is not type(expected) or observed != expected:
        raise ProofChainError(f"{label} mismatch")


def _require_size_hash(
    report: Mapping[str, Any], prefix: str, raw: bytes, label: str
) -> None:
    _require_equal(report[f"{prefix}_bytes"], len(raw), f"{label} byte length")
    _require_equal(report[f"{prefix}_sha256"], _sha256(raw), f"{label} SHA-256")


def _canonical_json(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _canonical_json_preserving_order(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _absolute(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _reject_symlink_components(path: Path, label: str) -> None:
    candidate = _absolute(path)
    current = Path(candidate.anchor)
    for part in candidate.parts[1:]:
        current /= part
        try:
            metadata = current.lstat()
        except OSError as exc:
            raise ProofChainError(f"{label} path component is unavailable") from exc
        if stat.S_ISLNK(metadata.st_mode):
            raise ProofChainError(f"{label} path contains a symlink")


def _executable_pin(path: Path, sha256: str) -> ExecutablePin:
    return ExecutablePin(path=path, sha256=sha256)


def _program_pin(path: Path, sha256: str, image_id: str) -> ProgramPin:
    return ProgramPin(path=path, sha256=sha256, image_id=image_id)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch-parent", required=True, type=Path)
    parser.add_argument("--output-directory", required=True, type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--source-request", required=True, type=Path)
    parser.add_argument("--source-proof", required=True, type=Path)
    parser.add_argument("--adapter-receipt", required=True, type=Path)
    for role in EXECUTABLE_ROLES:
        option = role.replace("_", "-")
        parser.add_argument(f"--{option}", required=True, type=Path)
        parser.add_argument(f"--{option}-sha256", required=True)
    for role in STAGE_ORDER:
        option = role.replace("_", "-")
        parser.add_argument(f"--{option}-program", required=True, type=Path)
        parser.add_argument(f"--{option}-program-sha256", required=True)
        parser.add_argument(f"--{option}-image-id", required=True)
    return parser


def main() -> int:
    arguments = _parser().parse_args()
    try:
        result = run_proof_chain(
            scratch_parent=arguments.scratch_parent,
            output_directory=arguments.output_directory,
            r0vm=_executable_pin(arguments.r0vm, arguments.r0vm_sha256),
            leaf_prover=_executable_pin(
                arguments.leaf_prover, arguments.leaf_prover_sha256
            ),
            level_one_prover=_executable_pin(
                arguments.level_one_prover, arguments.level_one_prover_sha256
            ),
            level_two_prover=_executable_pin(
                arguments.level_two_prover, arguments.level_two_prover_sha256
            ),
            settlement_prover=_executable_pin(
                arguments.settlement_prover, arguments.settlement_prover_sha256
            ),
            source_request=arguments.source_request,
            source_proof=arguments.source_proof,
            adapter_receipt=arguments.adapter_receipt,
            leaf_program=_program_pin(
                arguments.leaf_program,
                arguments.leaf_program_sha256,
                arguments.leaf_image_id,
            ),
            level_one_program=_program_pin(
                arguments.level_one_program,
                arguments.level_one_program_sha256,
                arguments.level_one_image_id,
            ),
            level_two_program=_program_pin(
                arguments.level_two_program,
                arguments.level_two_program_sha256,
                arguments.level_two_image_id,
            ),
            settlement_program=_program_pin(
                arguments.settlement_program,
                arguments.settlement_program_sha256,
                arguments.settlement_image_id,
            ),
            timeout_seconds=arguments.timeout_seconds,
        )
        response = {
            "artifact_count": result.artifact_count,
            "candidate_proof_chain_built": True,
            "ok": True,
            "production_authority": False,
            "proof_chain_report_sha256": result.proof_chain_report_sha256,
            "release_authority": False,
            "report_count": result.report_count,
            "schema": REPORT_SCHEMA,
            "scoped_local_replay_claim_allowed": False,
            "settlement_authority": False,
        }
    except (OSError, ProofChainError) as exc:
        response = {
            "error": str(exc),
            "ok": False,
            "production_authority": False,
            "release_authority": False,
            "schema": ERROR_SCHEMA,
            "settlement_authority": False,
        }
    print(json.dumps(response, sort_keys=True, separators=(",", ":")))
    return 0 if response["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
