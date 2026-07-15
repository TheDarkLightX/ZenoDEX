#!/usr/bin/env python3
"""Execute one governed ZRPF reproof task into a private authority-false stage."""

from __future__ import annotations

import argparse
import hashlib
import os
import resource
import selectors
import signal
import stat
import subprocess
import sys
import time
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Mapping, Sequence

if __package__ in {None, ""}:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import check_zrpf_initial_paid_calibration_attempt_v1 as paid_calibration
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools.zrpf_remote_reproof_handoff_v2_catalog import (
    CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID,
)
from tools.zrpf_remote_reproof_worker_v2_contract import (
    CAPTURE_SCHEMA,
    WORKER_NON_CLAIMS,
    CommandTemplate,
    ProverComputeProfile,
    ResourcePolicy,
    ValidatedStage,
    WorkerError,
    derive_capture_id,
    false_authority,
    resolved_argv_sha256,
    validate_capture_shape,
    validate_stage_packet,
    validate_worker_checkout,
)
from tools.zrpf_remote_reproof_worker_v2_contract import (
    PROVER_COMPUTE_PROFILES as _PROVER_COMPUTE_PROFILES,
)
from tools.zrpf_remote_reproof_worker_v2_contract import (
    RESOURCE_POLICIES as _RESOURCE_POLICIES,
)

RESOURCE_POLICIES = _RESOURCE_POLICIES
PROVER_COMPUTE_PROFILES = _PROVER_COMPUTE_PROFILES
MAX_RUN_TREE_ENTRIES = 1024
MAX_RUNNER_BYTES = 128 * 1024 * 1024
MAX_EXECUTION_PACKET_BYTES = 4 * 1024 * 1024
EXECUTION_PACKET_SNAPSHOT = "execution-packet.json"
FIXED_RUNNERS = {"python3": Path("/usr/bin/python3")}


@dataclass(frozen=True, slots=True)
class ResolvedCommand:
    argv: tuple[str, ...]
    stdin_path: Path | None
    stdout_artifact_role: str | None
    stdout_maximum_bytes: int
    command_template_sha256: str


@dataclass(frozen=True, slots=True)
class ProcessResult:
    stdout: bytes
    stderr: bytes
    exit_code: int
    duration_milliseconds: int


def clean_environment(
    home: Path,
    risc0_home: Path | None,
    compute_profile: ProverComputeProfile,
    r0vm: Path | None,
) -> dict[str, str]:
    environment = {
        "HOME": str(home),
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "PYTHONDONTWRITEBYTECODE": "1",
        "TZ": "UTC",
    }
    if risc0_home is not None:
        environment["RISC0_HOME"] = str(risc0_home)
    if compute_profile.risc0_prover is not None:
        if r0vm is None or not r0vm.is_absolute() or not r0vm.is_file():
            raise WorkerError("prover compute profile requires one packet-bound r0vm")
        environment["RISC0_PROVER"] = compute_profile.risc0_prover
        if compute_profile.risc0_executor is None:
            raise WorkerError("prover compute profile lacks an executor")
        environment["RISC0_EXECUTOR"] = compute_profile.risc0_executor
        environment["RISC0_SERVER_PATH"] = str(r0vm)
        if compute_profile.cuda_visible_devices is not None:
            environment["CUDA_VISIBLE_DEVICES"] = compute_profile.cuda_visible_devices
    return environment


def execute_stage(
    document: Mapping[str, object],
    packet: Mapping[str, object],
    repo_root: Path,
    artifact_root: Path,
    run_root: Path,
    *,
    runtime_bindings: Mapping[str, Path] | None = None,
    trusted_current_epoch_seconds: int | None = None,
) -> dict[str, object]:
    """Run one exact packet; return only an authority-false local capture."""

    stage = validate_stage_packet(document, packet, repo_root, artifact_root)
    _require_stage_compute_eligibility(stage)
    repository = validate_worker_checkout(stage, repo_root)
    bound_runtime = _validate_runtime_bindings(stage, runtime_bindings)
    bound_epoch = _validate_trusted_epoch_binding(stage, trusted_current_epoch_seconds)
    input_root, output_root, home = _create_private_run_root(run_root)
    bound_runtime = _snapshot_runtime_file_bindings(bound_runtime, input_root)
    input_paths = _snapshot_inputs(stage, artifact_root, input_root)
    input_paths["execution_packet_file"] = _snapshot_execution_packet(packet, input_root)
    output_paths = _prepare_output_paths(stage, output_root)
    r0vm = input_paths.get("prover_r0vm")
    risc0_home = r0vm.parent.parent if r0vm is not None else None
    environment = clean_environment(
        home,
        risc0_home,
        stage.prover_compute_profile,
        r0vm,
    )
    command_captures: list[dict[str, object]] = []

    for ordinal, template in enumerate(stage.commands):
        command = _resolve_command(
            template,
            stage,
            input_paths,
            output_paths,
            bound_runtime,
            bound_epoch,
        )
        runner_sha256, runner_bytes = _runner_identity(Path(command.argv[0]))
        command_policy = _command_resource_policy(
            stage,
            ordinal,
            input_paths,
            output_paths,
            bound_runtime,
            bound_epoch,
        )
        result = _run_bounded_command(command, command_policy, environment, repository)
        if command.stdout_artifact_role is not None:
            _write_new(
                output_paths[command.stdout_artifact_role],
                result.stdout,
                "command stdout artifact",
                mode=0o600,
            )
        command_captures.append(
            {
                "ordinal": ordinal,
                "command_template_sha256": command.command_template_sha256,
                "resolved_argv_sha256": resolved_argv_sha256(command.argv),
                "effective_resource_policy_id": command_policy.record()["policy_id"],
                "effective_timeout_seconds": command_policy.timeout_seconds,
                "runner_sha256": runner_sha256,
                "runner_bytes": runner_bytes,
                "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
                "stdout_bytes": len(result.stdout),
                "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
                "stderr_bytes": len(result.stderr),
                "exit_status": result.exit_code,
                "duration_milliseconds": result.duration_milliseconds,
            }
        )

    _validate_input_snapshots(stage, input_root)
    validate_worker_checkout(stage, repository)
    output_records = _exact_output_records(stage, output_root)
    capture: dict[str, object] = {
        "schema": CAPTURE_SCHEMA,
        "status": "outputs_captured_without_proof_or_release_authority",
        "capture_id": "0" * 64,
        "handoff_id": stage.handoff_id,
        "execution_packet_id": stage.execution_packet_id,
        "task_id": stage.task_id,
        "stage_id": stage.stage_id,
        "ordinal": stage.ordinal,
        "resource_policy": stage.resource_policy.record(),
        "prover_compute_profile": stage.prover_compute_profile.record(),
        "commands": command_captures,
        "outputs": output_records,
        "authority": false_authority(),
        "non_claims": list(WORKER_NON_CLAIMS),
    }
    capture["capture_id"] = derive_capture_id(capture)
    validate_worker_capture(
        document,
        packet,
        capture,
        repository,
        artifact_root,
        run_root,
        runtime_bindings=bound_runtime,
        trusted_current_epoch_seconds=bound_epoch,
    )
    return capture


def validate_worker_capture(
    document: Mapping[str, object],
    packet: Mapping[str, object],
    capture: Mapping[str, object],
    repo_root: Path,
    artifact_root: Path,
    run_root: Path,
    *,
    runtime_bindings: Mapping[str, Path] | None = None,
    trusted_current_epoch_seconds: int | None = None,
) -> None:
    stage = validate_stage_packet(document, packet, repo_root, artifact_root)
    _require_stage_compute_eligibility(stage)
    repository = validate_worker_checkout(stage, repo_root)
    bound_runtime = _validate_runtime_bindings(stage, runtime_bindings)
    bound_epoch = _validate_trusted_epoch_binding(stage, trusted_current_epoch_seconds)
    input_root, output_root, _home = _existing_run_root(run_root)
    bound_runtime = _validate_runtime_file_snapshots(bound_runtime, input_root)
    input_paths = _validate_input_snapshots(stage, input_root)
    input_paths["execution_packet_file"] = _validate_execution_packet_snapshot(packet, input_root)
    output_paths = {item.role: output_root / item.path for item in stage.outputs}
    command_captures, captured_outputs = validate_capture_shape(capture, stage)
    observed_outputs = _exact_output_records(stage, output_root)
    if not handoff._canonical_values_equal(captured_outputs, observed_outputs):
        raise WorkerError("worker output artifact inventory differs from capture")

    for ordinal, (command_capture, template) in enumerate(
        zip(command_captures, stage.commands, strict=True)
    ):
        resolved = _resolve_command(
            template,
            stage,
            input_paths,
            output_paths,
            bound_runtime,
            bound_epoch,
        )
        effective_policy = _command_resource_policy(
            stage,
            ordinal,
            input_paths,
            output_paths,
            bound_runtime,
            bound_epoch,
        )
        if (
            command_capture["effective_resource_policy_id"]
            != effective_policy.record()["policy_id"]
            or command_capture["effective_timeout_seconds"] != effective_policy.timeout_seconds
        ):
            raise WorkerError("worker effective command resource policy mismatch")
        if (
            type(command_capture["duration_milliseconds"]) is not int
            or command_capture["duration_milliseconds"] > effective_policy.timeout_seconds * 1_000
        ):
            raise WorkerError("worker command duration exceeds its effective deadline")
        runner_sha256, runner_bytes = _runner_identity(Path(resolved.argv[0]))
        if command_capture["resolved_argv_sha256"] != resolved_argv_sha256(resolved.argv):
            raise WorkerError("worker resolved argv digest mismatch")
        if (
            command_capture["runner_sha256"] != runner_sha256
            or command_capture["runner_bytes"] != runner_bytes
        ):
            raise WorkerError("worker runner identity mismatch")
        if resolved.stdout_artifact_role is None:
            if (
                command_capture["stdout_bytes"] != 0
                or command_capture["stdout_sha256"] != hashlib.sha256(b"").hexdigest()
            ):
                raise WorkerError("unexpected worker stdout capture")
        else:
            output = next(
                row for row in observed_outputs if row["role"] == resolved.stdout_artifact_role
            )
            if (
                command_capture["stdout_sha256"] != output["sha256"]
                or command_capture["stdout_bytes"] != output["size_bytes"]
            ):
                raise WorkerError("worker stdout artifact binding mismatch")
    validate_worker_checkout(stage, repository)


def _create_private_run_root(run_root: Path) -> tuple[Path, Path, Path]:
    if not run_root.is_absolute():
        raise WorkerError("run root must be an absolute path")
    try:
        parent = run_root.parent.resolve(strict=True)
    except OSError as exc:
        raise WorkerError("run root parent is unavailable") from exc
    if parent != run_root.parent:
        raise WorkerError("run root parent must be one real canonical directory")
    try:
        os.mkdir(run_root, mode=0o700)
    except FileExistsError as exc:
        raise WorkerError("run root must begin absent") from exc
    except OSError as exc:
        raise WorkerError("run root could not be created") from exc
    input_root = run_root / "inputs"
    output_root = run_root / "outputs"
    home = run_root / "home"
    for path in (input_root, output_root, home):
        os.mkdir(path, mode=0o700)
    return input_root, output_root, home


def _existing_run_root(run_root: Path) -> tuple[Path, Path, Path]:
    if not run_root.is_absolute() or run_root.resolve(strict=True) != run_root:
        raise WorkerError("run root must be one real canonical directory")
    input_root = run_root / "inputs"
    output_root = run_root / "outputs"
    home = run_root / "home"
    roots = (input_root, output_root, home)
    if any(not path.is_dir() or path.is_symlink() for path in roots):
        raise WorkerError("run root layout mismatch")
    return input_root, output_root, home


def _snapshot_inputs(
    stage: ValidatedStage, artifact_root: Path, input_root: Path
) -> dict[str, Path]:
    source_root = artifact_root.resolve(strict=True)
    records: list[Mapping[str, object]] = []
    paths: dict[str, Path] = {}
    for contract in stage.inputs:
        raw = handoff._stable_read_beneath(
            source_root,
            contract.path,
            contract.role,
            contract.maximum_bytes,
        )
        record = handoff._artifact_record_from_bytes(contract.raw, contract.path, raw)
        records.append(record)
        destination = input_root / contract.path
        _ensure_private_parents(input_root, PurePosixPath(contract.path).parent)
        mode = 0o500 if contract.kind == "executable" else 0o400
        _write_new(destination, raw, f"{contract.role} input snapshot", mode=mode)
        paths[contract.role] = destination
    if not handoff._canonical_values_equal(records, list(stage.input_records)):
        raise WorkerError("input artifact changed before private snapshot")
    return paths


def _validate_input_snapshots(stage: ValidatedStage, input_root: Path) -> dict[str, Path]:
    records = [handoff._artifact_record(contract.raw, input_root) for contract in stage.inputs]
    if not handoff._canonical_values_equal(records, list(stage.input_records)):
        raise WorkerError("private input snapshot changed during execution")
    return {contract.role: input_root / contract.path for contract in stage.inputs}


def _snapshot_execution_packet(packet: Mapping[str, object], input_root: Path) -> Path:
    destination = input_root / EXECUTION_PACKET_SNAPSHOT
    _write_new(
        destination,
        handoff.canonical_json_bytes(packet),
        "execution packet snapshot",
        mode=0o400,
    )
    return destination


def _validate_execution_packet_snapshot(packet: Mapping[str, object], input_root: Path) -> Path:
    path = input_root / EXECUTION_PACKET_SNAPSHOT
    observed = _stable_regular_read(
        path,
        "execution packet snapshot",
        MAX_EXECUTION_PACKET_BYTES,
    )
    if observed != handoff.canonical_json_bytes(packet):
        raise WorkerError("execution packet snapshot changed during execution")
    return path


def _prepare_output_paths(stage: ValidatedStage, output_root: Path) -> dict[str, Path]:
    paths: dict[str, Path] = {}
    for contract in stage.outputs:
        if contract.maximum_bytes > stage.resource_policy.maximum_output_file_bytes:
            raise WorkerError("artifact bound exceeds the governed resource policy")
        destination = output_root / contract.path
        _ensure_private_parents(output_root, PurePosixPath(contract.path).parent)
        if destination.exists() or destination.is_symlink():
            raise WorkerError("declared output must begin absent")
        paths[contract.role] = destination
    return paths


def _ensure_private_parents(root: Path, relative: PurePosixPath) -> None:
    current = root
    for part in relative.parts:
        if part in {"", "."}:
            continue
        current = current / part
        try:
            os.mkdir(current, mode=0o700)
        except FileExistsError:
            facts = current.lstat()
            if not stat.S_ISDIR(facts.st_mode) or current.is_symlink():
                raise WorkerError("run-root path contains a non-directory or symlink") from None


def _resolve_command(
    template: CommandTemplate,
    stage: ValidatedStage,
    input_paths: Mapping[str, Path],
    output_paths: Mapping[str, Path],
    runtime_bindings: Mapping[str, Path],
    trusted_current_epoch_seconds: int | None = None,
) -> ResolvedCommand:
    runner = _resolve_runner(template.runner, stage, input_paths)
    arguments = tuple(
        _resolve_argument(
            item,
            stage,
            input_paths,
            output_paths,
            runtime_bindings,
            trusted_current_epoch_seconds,
        )
        for item in template.argv
    )
    stdin_path = (
        None
        if template.stdin_artifact_role is None
        else _required_role(input_paths, template.stdin_artifact_role, "stdin")
    )
    stdout_maximum = stage.resource_policy.maximum_stdout_bytes
    if template.stdout_artifact_role is not None:
        contract = next(
            (item for item in stage.outputs if item.role == template.stdout_artifact_role),
            None,
        )
        if contract is None:
            raise WorkerError("command stdout role is not one declared output")
        stdout_maximum = min(stdout_maximum, contract.maximum_bytes)
    return ResolvedCommand(
        argv=(str(runner), *arguments),
        stdin_path=stdin_path,
        stdout_artifact_role=template.stdout_artifact_role,
        stdout_maximum_bytes=stdout_maximum,
        command_template_sha256=template.template_sha256,
    )


def _resolve_runner(token: str, stage: ValidatedStage, input_paths: Mapping[str, Path]) -> Path:
    if token.startswith("@"):
        role = token[1:]
        path = _required_role(input_paths, role, "runner")
        contract = next((item for item in stage.inputs if item.role == role), None)
        if contract is None or contract.kind != "executable":
            raise WorkerError("artifact runner must be one declared executable input")
        return path
    try:
        fixed = FIXED_RUNNERS[token]
    except KeyError as exc:
        raise WorkerError("fixed command runner is not governed") from exc
    try:
        resolved = fixed.resolve(strict=True)
    except OSError as exc:
        raise WorkerError("fixed command runner is unavailable") from exc
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise WorkerError("fixed command runner is not executable")
    return resolved


def _resolve_argument(
    token: str,
    stage: ValidatedStage,
    input_paths: Mapping[str, Path],
    output_paths: Mapping[str, Path],
    runtime_bindings: Mapping[str, Path],
    trusted_current_epoch_seconds: int | None = None,
) -> str:
    if not token.startswith("@"):
        return token
    role = token[1:]
    if role == "c0_commit":
        return stage.c0_commit
    if role == "worker_commit":
        return stage.worker_commit
    if role == "prover_compute_profile_id":
        return stage.prover_compute_profile.profile_id
    if role == "trusted_current_epoch_seconds":
        if trusted_current_epoch_seconds is None:
            raise WorkerError("trusted current epoch binding is unavailable")
        return str(trusted_current_epoch_seconds)
    if role.startswith("runtime_"):
        runtime_role = role.removeprefix("runtime_")
        try:
            return str(runtime_bindings[runtime_role])
        except KeyError as exc:
            raise WorkerError("command contains an unbound runtime placeholder") from exc
    if role in input_paths:
        return str(input_paths[role])
    if role in output_paths:
        return str(output_paths[role])
    raise WorkerError("command contains an unknown or unbound placeholder")


def _validate_runtime_bindings(
    stage: ValidatedStage,
    supplied: Mapping[str, Path] | None,
) -> dict[str, Path]:
    required = {
        token.removeprefix("@runtime_")
        for command in stage.commands
        for token in command.argv
        if token.startswith("@runtime_")
    }
    values = {} if supplied is None else dict(supplied)
    if set(values) != required:
        raise WorkerError("runtime binding inventory mismatch")
    normalized: dict[str, Path] = {}
    for role in sorted(required):
        path = values[role]
        if not isinstance(path, Path) or not path.is_absolute():
            raise WorkerError("runtime binding must be an absolute pathlib.Path")
        try:
            resolved = path.resolve(strict=True)
        except OSError as exc:
            raise WorkerError("runtime binding is unavailable") from exc
        if resolved != path or path.is_symlink():
            raise WorkerError("runtime binding must be one canonical non-symlink path")
        normalized[role] = resolved
    return normalized


def _snapshot_runtime_file_bindings(
    bindings: Mapping[str, Path], input_root: Path
) -> dict[str, Path]:
    result = dict(bindings)
    budget = result.get("attempt_budget_and_price")
    if budget is None:
        return result
    raw = _stable_regular_read(
        budget,
        "attempt budget and price runtime input",
        paid_calibration.MAX_INPUT_BYTES,
    )
    runtime_root = input_root / "runtime"
    os.mkdir(runtime_root, mode=0o700)
    destination = runtime_root / "attempt-budget-and-price.json"
    _write_new(destination, raw, "attempt budget and price snapshot", mode=0o400)
    result["attempt_budget_and_price"] = destination
    return result


def _validate_runtime_file_snapshots(
    bindings: Mapping[str, Path], input_root: Path
) -> dict[str, Path]:
    result = dict(bindings)
    if "attempt_budget_and_price" not in result:
        return result
    snapshot = input_root / "runtime/attempt-budget-and-price.json"
    _stable_regular_read(
        snapshot,
        "attempt budget and price snapshot",
        paid_calibration.MAX_INPUT_BYTES,
    )
    result["attempt_budget_and_price"] = snapshot
    return result


def _validate_trusted_epoch_binding(stage: ValidatedStage, supplied: int | None) -> int | None:
    required = any(
        token == "@trusted_current_epoch_seconds"
        for command in stage.commands
        for token in command.argv
    )
    if not required:
        if supplied is not None:
            raise WorkerError("trusted current epoch binding is surplus")
        return None
    if isinstance(supplied, bool) or not isinstance(supplied, int):
        raise WorkerError("trusted current epoch binding must be an integer")
    if not 0 < supplied < 2**63:
        raise WorkerError("trusted current epoch binding is outside its bound")
    return supplied


def _require_stage_compute_eligibility(stage: ValidatedStage) -> None:
    if (
        stage.stage_id == paid_calibration.SOURCE_STAGE_ID
        and stage.prover_compute_profile.profile_id
        != CUDA_SINGLE_VISIBLE_DEVICE_PROVER_COMPUTE_PROFILE_ID
    ):
        raise WorkerError("source proof execution requires the governed CUDA compute profile")


def _command_resource_policy(
    stage: ValidatedStage,
    ordinal: int,
    input_paths: Mapping[str, Path],
    output_paths: Mapping[str, Path],
    runtime_bindings: Mapping[str, Path],
    trusted_current_epoch_seconds: int | None,
) -> ResourcePolicy:
    policy = stage.resource_policy
    if stage.stage_id != paid_calibration.SOURCE_STAGE_ID:
        return policy
    if ordinal < len(stage.commands) - 1:
        return replace(policy, timeout_seconds=min(policy.timeout_seconds, 60))
    required_inputs = {
        "source_execution_profile",
        "cuda_r0vm_build_attestation",
        "h100_preflight",
        "execution_packet_file",
    }
    if not required_inputs.issubset(input_paths):
        raise WorkerError("source calibration input inventory is incomplete")
    try:
        budget_path = runtime_bindings["attempt_budget_and_price"]
        qualification_path = output_paths["source_calibration_qualification"]
    except KeyError as exc:
        raise WorkerError("source calibration runtime binding is incomplete") from exc
    if trusted_current_epoch_seconds is None:
        raise WorkerError("source calibration trusted epoch is unavailable")
    try:
        expected = paid_calibration.check_qualification(
            input_paths["source_execution_profile"],
            input_paths["cuda_r0vm_build_attestation"],
            input_paths["h100_preflight"],
            input_paths["execution_packet_file"],
            budget_path,
            trusted_current_epoch_seconds=trusted_current_epoch_seconds,
        )
    except paid_calibration.AttemptQualificationError as exc:
        raise WorkerError("source calibration qualification no longer validates") from exc
    observed = _stable_regular_read(
        qualification_path,
        "source calibration qualification",
        64 * 1024,
    )
    expected_bytes = paid_calibration.canonical_bytes(expected) + b"\n"
    if observed != expected_bytes:
        raise WorkerError("source calibration qualification output mismatch")
    deadline = expected["hard_attempt_deadline_milliseconds"]
    if (
        type(deadline) is not int
        or not 1_000 <= deadline <= paid_calibration.MAX_HARD_ATTEMPT_CAP_MILLISECONDS
    ):
        raise WorkerError("source calibration deadline cannot govern a proof command")
    return replace(policy, timeout_seconds=deadline // 1_000)


def _required_role(paths: Mapping[str, Path], role: str, label: str) -> Path:
    try:
        return paths[role]
    except KeyError as exc:
        raise WorkerError(f"command {label} role is not one declared input") from exc


def _runner_identity(path: Path) -> tuple[str, int]:
    raw = _stable_regular_read(path, "command runner", MAX_RUNNER_BYTES, executable=True)
    return hashlib.sha256(raw).hexdigest(), len(raw)


def _run_bounded_command(
    command: ResolvedCommand,
    policy: ResourcePolicy,
    environment: dict[str, str],
    cwd: Path,
) -> ProcessResult:
    stdin_handle = None
    started = time.monotonic()
    try:
        if command.stdin_path is not None:
            stdin_handle = command.stdin_path.open("rb")
        process = subprocess.Popen(
            list(command.argv),
            cwd=cwd,
            env=environment,
            stdin=subprocess.DEVNULL if stdin_handle is None else stdin_handle,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            close_fds=True,
            shell=False,
            start_new_session=True,
            preexec_fn=lambda: _install_child_limits(policy),
        )
    except OSError as exc:
        raise WorkerError("governed command could not start") from exc
    finally:
        if stdin_handle is not None:
            stdin_handle.close()
    try:
        stdout, stderr = _capture_process(
            process,
            maximum_stdout=command.stdout_maximum_bytes,
            maximum_stderr=policy.maximum_stderr_bytes,
            timeout_seconds=policy.timeout_seconds,
        )
    except (OSError, TimeoutError, subprocess.TimeoutExpired, WorkerError):
        _terminate_process_group(process)
        raise
    residual = _terminate_process_group(process)
    if residual:
        raise WorkerError("governed command left a residual process")
    if process.returncode != 0:
        raise WorkerError(f"governed command returned exit status {process.returncode}")
    duration = int((time.monotonic() - started) * 1000)
    if duration > policy.timeout_seconds * 1_000:
        raise WorkerError("governed command exceeded its total elapsed-time bound")
    return ProcessResult(stdout, stderr, process.returncode, duration)


def _capture_process(
    process: subprocess.Popen[bytes],
    *,
    maximum_stdout: int,
    maximum_stderr: int,
    timeout_seconds: int,
) -> tuple[bytes, bytes]:
    if process.stdout is None or process.stderr is None:
        raise WorkerError("governed command pipes are unavailable")
    streams = {
        process.stdout.fileno(): ("stdout", maximum_stdout),
        process.stderr.fileno(): ("stderr", maximum_stderr),
    }
    buffers = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    deadline = time.monotonic() + timeout_seconds
    try:
        for descriptor in streams:
            os.set_blocking(descriptor, False)
            selector.register(descriptor, selectors.EVENT_READ)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise WorkerError("governed command timed out")
            events = selector.select(min(remaining, 1.0))
            if not events:
                continue
            for key, _mask in events:
                descriptor = int(key.fd)
                label, maximum = streams[descriptor]
                try:
                    chunk = os.read(descriptor, 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(descriptor)
                    continue
                if len(buffers[label]) + len(chunk) > maximum:
                    raise WorkerError(f"governed command {label} exceeds its bound")
                buffers[label].extend(chunk)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise WorkerError("governed command timed out")
        process.wait(timeout=remaining)
    finally:
        selector.close()
        process.stdout.close()
        process.stderr.close()
    return bytes(buffers["stdout"]), bytes(buffers["stderr"])


def _terminate_process_group(process: subprocess.Popen[bytes]) -> bool:
    residual = False
    try:
        os.killpg(process.pid, signal.SIGKILL)
        residual = process.poll() is not None
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)
    return residual


def _install_child_limits(policy: ResourcePolicy) -> None:
    _set_soft_limit(resource.RLIMIT_CORE, 0)
    _set_soft_limit(resource.RLIMIT_FSIZE, policy.maximum_output_file_bytes)
    _set_soft_limit(resource.RLIMIT_NOFILE, policy.maximum_open_files)
    _set_soft_limit(resource.RLIMIT_AS, policy.maximum_address_space_bytes)
    _set_soft_limit(resource.RLIMIT_CPU, policy.timeout_seconds + 30)


def _set_soft_limit(resource_id: int, requested: int) -> None:
    _soft, hard = resource.getrlimit(resource_id)
    effective = requested if hard == resource.RLIM_INFINITY else min(requested, hard)
    resource.setrlimit(resource_id, (effective, hard))


def _exact_output_records(stage: ValidatedStage, output_root: Path) -> list[dict[str, object]]:
    expected_files = {item.path for item in stage.outputs}
    expected_directories: set[str] = set()
    for relative in expected_files:
        parent = PurePosixPath(relative).parent
        while parent.as_posix() not in {"", "."}:
            expected_directories.add(parent.as_posix())
            parent = parent.parent
    actual_files, actual_directories = _scan_tree(output_root)
    missing = sorted(expected_files - actual_files)
    if missing:
        raise WorkerError(f"missing declared output: {missing[0]}")
    surplus_files = sorted(actual_files - expected_files)
    if surplus_files:
        raise WorkerError(f"surplus output file: {surplus_files[0]}")
    surplus_directories = sorted(actual_directories - expected_directories)
    if surplus_directories:
        raise WorkerError(f"surplus output directory: {surplus_directories[0]}")
    missing_directories = sorted(expected_directories - actual_directories)
    if missing_directories:
        raise WorkerError(f"missing declared output directory: {missing_directories[0]}")
    records = [handoff._artifact_record(item.raw, output_root) for item in stage.outputs]
    handoff._require_aggregate_artifact_bound(records)
    for path in (output_root / item.path for item in stage.outputs):
        path.chmod(0o400)
    return records


def _scan_tree(root: Path) -> tuple[set[str], set[str]]:
    if root.resolve(strict=True) != root or root.is_symlink() or not root.is_dir():
        raise WorkerError("output root must be one real canonical directory")
    files: set[str] = set()
    directories: set[str] = set()
    entries = 0
    for current, names, filenames in os.walk(root, topdown=True, followlinks=False):
        current_path = Path(current)
        for name in sorted(names):
            entries += 1
            path = current_path / name
            facts = path.lstat()
            if stat.S_ISLNK(facts.st_mode):
                raise WorkerError("output tree contains a symlink")
            if not stat.S_ISDIR(facts.st_mode):
                raise WorkerError("output tree contains a non-directory component")
            directories.add(path.relative_to(root).as_posix())
        for name in sorted(filenames):
            entries += 1
            path = current_path / name
            facts = path.lstat()
            if stat.S_ISLNK(facts.st_mode):
                raise WorkerError("output tree contains a symlink")
            if not stat.S_ISREG(facts.st_mode) or facts.st_nlink != 1:
                raise WorkerError("output tree contains a non-regular or hard-linked file")
            files.add(path.relative_to(root).as_posix())
        if entries > MAX_RUN_TREE_ENTRIES:
            raise WorkerError("output tree entry count exceeds its bound")
    return files, directories


def _stable_regular_read(
    path: Path, label: str, maximum_bytes: int, *, executable: bool = False
) -> bytes:
    try:
        before = path.lstat()
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_nlink != 1
            or not 0 < before.st_size <= maximum_bytes
            or (executable and before.st_mode & 0o111 == 0)
        ):
            raise WorkerError(f"{label} must be one bounded regular file")
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            raw = handle.read(maximum_bytes + 1)
            after = os.fstat(handle.fileno())
    except OSError as exc:
        raise WorkerError(f"{label} could not be read") from exc

    def identity(value: os.stat_result) -> tuple[int, int, int, int, int, int]:
        return (
            value.st_dev,
            value.st_ino,
            value.st_mode,
            value.st_size,
            value.st_mtime_ns,
            value.st_ctime_ns,
        )

    if identity(before) != identity(opened) or identity(opened) != identity(after):
        raise WorkerError(f"{label} changed during read")
    if len(raw) != before.st_size:
        raise WorkerError(f"{label} read length mismatch")
    return raw


def _write_new(path: Path, raw: bytes, label: str, *, mode: int) -> None:
    descriptor: int | None = None
    try:
        descriptor = os.open(
            path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            mode,
        )
        offset = 0
        while offset < len(raw):
            written = os.write(descriptor, raw[offset:])
            if written <= 0:
                raise WorkerError(f"{label} write made no progress")
            offset += written
        os.fsync(descriptor)
    except FileExistsError as exc:
        raise WorkerError(f"{label} must begin absent") from exc
    except OSError as exc:
        raise WorkerError(f"{label} write failed") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("run-stage", "check-capture"):
        command = subparsers.add_parser(name)
        command.add_argument("--repository", type=Path, required=True)
        command.add_argument("--handoff", type=Path, required=True)
        command.add_argument("--packet", type=Path, required=True)
        command.add_argument("--artifact-root", type=Path, required=True)
        command.add_argument("--run-root", type=Path, required=True)
        command.add_argument("--capture-output", type=Path, required=True)
        command.add_argument("--risc0-home", type=Path)
        command.add_argument("--cargo-registry-dir", type=Path)
        command.add_argument("--docker", type=Path)
        command.add_argument("--attempt-budget-and-price", type=Path)
        command.add_argument("--trusted-current-epoch-seconds", type=int)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        document = handoff._object(handoff.load_canonical_json(args.handoff, "handoff"), "handoff")
        packet = handoff._object(
            handoff.load_canonical_json(args.packet, "execution packet"),
            "execution packet",
        )
        runtime_bindings = {
            role: path
            for role, path in (
                ("risc0_home", args.risc0_home),
                ("cargo_registry_dir", args.cargo_registry_dir),
                ("docker", args.docker),
                ("attempt_budget_and_price", args.attempt_budget_and_price),
            )
            if path is not None
        }
        if args.command == "run-stage":
            capture = execute_stage(
                document,
                packet,
                args.repository,
                args.artifact_root,
                args.run_root,
                runtime_bindings=runtime_bindings,
                trusted_current_epoch_seconds=args.trusted_current_epoch_seconds,
            )
            handoff._write_new(
                args.capture_output,
                handoff.canonical_json_bytes(capture),
                "worker capture output",
            )
        else:
            capture = handoff._object(
                handoff.load_canonical_json(args.capture_output, "worker capture"),
                "worker capture",
            )
            validate_worker_capture(
                document,
                packet,
                capture,
                args.repository,
                args.artifact_root,
                args.run_root,
                runtime_bindings=runtime_bindings,
                trusted_current_epoch_seconds=args.trusted_current_epoch_seconds,
            )
            sys.stdout.buffer.write(
                handoff.canonical_json_bytes(
                    {
                        "accepted": True,
                        "capture_id": capture["capture_id"],
                        "authority": false_authority(),
                    }
                )
            )
    except (WorkerError, handoff.HandoffError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
