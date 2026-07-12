"""Bounded runtime support for exact RISC0 V1 retained-receipt replay."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools import check_risc0_recursive_rebuild_evidence as rebuild
from tools import zrpf_v3_replay_environment as replay_environment
from tools import zrpf_v3_replay_process as replay_process
from tools import zrpf_v3_replay_sealed_executable as sealed_executable

ENVIRONMENT_PROFILE_ABSENT = "minimal_environment_risc0_dev_mode_absent_v1"
DEV_MODE_DISABLED_VALUES = ("0",)
DEV_MODE_ENABLED_VALUES = ("1", "true", "yes", "on")
DEV_MODE_REJECT_ERROR = "RISC0_DEV_MODE set: verifier refuses dev-mode receipts"
MAX_RUNTIME_OUTPUT_BYTES = 4 * 1024 * 1024
MAX_RUNTIME_INPUT_BYTES = 4 * 1024 * 1024
RUNTIME_TIMEOUT_SECONDS = 60
ZERO_SHA256 = hashlib.sha256(b"").hexdigest()
CHECKER_SOURCE_PATHS = {
    "artifact_checker": "tools/check_risc0_recursive_rebuild_evidence.py",
    "environment": "tools/zrpf_v3_replay_environment.py",
    "live_replay_checker": "tools/check_risc0_recursive_live_replay.py",
    "live_replay_support": "tools/risc0_recursive_live_replay_support.py",
    "process_runner": "tools/zrpf_v3_replay_process.py",
    "sealed_executable": "tools/zrpf_v3_replay_sealed_executable.py",
}


class LiveReplayError(ValueError):
    """Stable rejection at the executable V1 replay boundary."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code


@dataclass(frozen=True)
class RuntimeInput:
    raw: bytes
    sha256: str
    size_bytes: int


@dataclass(frozen=True)
class RuntimeInputs:
    malformed_request: RuntimeInput
    malformed_stdout: bytes
    positive_request: RuntimeInput
    positive_stdout: bytes


@dataclass(frozen=True)
class ExecutionEvidence:
    live_runs: dict[str, Any]
    verifier_identity: dict[str, Any]


def reject(code: str, detail: str) -> LiveReplayError:
    return LiveReplayError(code, detail)


def require_unprivileged_linux() -> None:
    if sys.platform != "linux" or os.geteuid() == 0:
        raise reject("EXECUTION_CONTEXT", "live replay requires unprivileged Linux")
    try:
        status = Path("/proc/self/status").read_text(encoding="ascii")
    except OSError as exc:
        raise reject("EXECUTION_CONTEXT", "process capability state unavailable") from exc
    capability_fields = {"CapInh", "CapPrm", "CapEff", "CapAmb"}
    observed: dict[str, int] = {}
    for line in status.splitlines():
        name, separator, value = line.partition(":")
        if separator and name in capability_fields:
            try:
                observed[name] = int(value.strip(), 16)
            except ValueError as exc:
                raise reject("EXECUTION_CONTEXT", f"invalid {name}") from exc
    if set(observed) != capability_fields or any(observed.values()):
        raise reject("EXECUTION_CONTEXT", "live replay requires zero process capabilities")


def read_expected(
    path: Path,
    *,
    expected_sha256: object,
    expected_size_bytes: object,
    label: str,
    max_bytes: int,
) -> RuntimeInput:
    if not isinstance(expected_sha256, str) or not isinstance(expected_size_bytes, int):
        raise reject("ARTIFACT_REPORT", f"missing expected {label} identity")
    try:
        digest = rebuild._read_regular_path(path, label=label, max_bytes=max_bytes)
    except rebuild.EvidenceError as exc:
        raise reject("ARTIFACT_READ", str(exc)) from exc
    if digest.sha256 != expected_sha256 or digest.size_bytes != expected_size_bytes:
        raise reject("ARTIFACT_IDENTITY", label)
    return RuntimeInput(digest.raw, digest.sha256, digest.size_bytes)


def authenticated_reference(
    reference_path: Path = rebuild.REFERENCE_PATH,
) -> Mapping[str, Any]:
    try:
        raw = rebuild._read_regular_path(
            reference_path,
            label="reference",
            max_bytes=rebuild.MAX_REFERENCE_BYTES,
        ).raw
        reference = rebuild.validate_reference(rebuild._parse_json(raw, label="REFERENCE"))
    except rebuild.EvidenceError as exc:
        raise reject("REFERENCE", str(exc)) from exc
    actual = rebuild.reference_canonical_sha256(reference)
    if actual != rebuild.EXPECTED_REFERENCE_CANONICAL_SHA256:
        raise reject("REFERENCE", "canonical digest mismatch")
    return reference


def checker_source_closure(repository_root: Path | None = None) -> dict[str, str]:
    root = Path(__file__).resolve().parents[1] if repository_root is None else repository_root
    closure: dict[str, str] = {}
    for role, relative_path in CHECKER_SOURCE_PATHS.items():
        try:
            source = rebuild._read_regular_path(
                root / relative_path,
                label=f"{role}_source",
                max_bytes=rebuild.MAX_SOURCE_FILE_BYTES,
            )
        except rebuild.EvidenceError as exc:
            raise reject("CHECKER_SOURCE", str(exc)) from exc
        closure[role] = source.sha256
    return closure


def expected_malformed_stdout(raw: bytes) -> bytes:
    try:
        value = rebuild._parse_json(raw, label="MALFORMED_REJECT_TRANSCRIPT")
    except rebuild.EvidenceError as exc:
        raise reject("MALFORMED_TRANSCRIPT", str(exc)) from exc
    if not isinstance(value, dict) or set(value) != {"process_exit_code", "response", "stderr"}:
        raise reject("MALFORMED_TRANSCRIPT", "unexpected transcript shape")
    if value.get("process_exit_code") != 0 or value.get("stderr") != "":
        raise reject("MALFORMED_TRANSCRIPT", "unexpected process outcome")
    response = value.get("response")
    expected_response = {"error": rebuild.CRYPTOGRAPHIC_INVALID_ERROR, "ok": False}
    if response != expected_response:
        raise reject("MALFORMED_TRANSCRIPT", "unexpected response")
    return json.dumps(response, sort_keys=True, separators=(",", ":")).encode("utf-8")


def capture_inputs(
    paths: rebuild.RebuildEvidencePaths,
    artifact_report: Mapping[str, Any],
    reference: Mapping[str, Any],
) -> RuntimeInputs:
    malformed_reference = reference["malformed_proof_reject"]
    positive_request = read_expected(
        paths.positive_verify_request,
        expected_sha256=artifact_report.get("positive_verify_request_sha256"),
        expected_size_bytes=reference["positive_verify_request"]["size_bytes"],
        label="positive_verify_request",
        max_bytes=MAX_RUNTIME_INPUT_BYTES,
    )
    malformed_request = read_expected(
        paths.malformed_verify_request,
        expected_sha256=artifact_report.get("malformed_verify_request_sha256"),
        expected_size_bytes=malformed_reference["verify_request"]["size_bytes"],
        label="malformed_verify_request",
        max_bytes=MAX_RUNTIME_INPUT_BYTES,
    )
    positive_transcript = read_expected(
        paths.verified_transcript,
        expected_sha256=artifact_report.get("verified_transcript_sha256"),
        expected_size_bytes=reference["verified_transcript"]["size_bytes"],
        label="verified_transcript",
        max_bytes=MAX_RUNTIME_OUTPUT_BYTES,
    )
    malformed_transcript = read_expected(
        paths.malformed_reject_transcript,
        expected_sha256=artifact_report.get("malformed_reject_transcript_sha256"),
        expected_size_bytes=malformed_reference["reject_transcript"]["size_bytes"],
        label="malformed_reject_transcript",
        max_bytes=MAX_RUNTIME_OUTPUT_BYTES,
    )
    return RuntimeInputs(
        malformed_request=malformed_request,
        malformed_stdout=expected_malformed_stdout(malformed_transcript.raw),
        positive_request=positive_request,
        positive_stdout=positive_transcript.raw,
    )


def _runtime_environment(runtime_directory: Path, dev_mode_value: str | None) -> dict[str, str]:
    environment = replay_environment.clean_environment()
    environment.update({"HOME": str(runtime_directory), "TMPDIR": str(runtime_directory)})
    if dev_mode_value is not None:
        environment["RISC0_DEV_MODE"] = dev_mode_value
    return environment


def run_verifier(
    executable: sealed_executable.SealedExecutable,
    *,
    request: RuntimeInput,
    runtime_directory: Path,
    dev_mode_value: str | None,
) -> subprocess.CompletedProcess[bytes]:
    try:
        return replay_process.run_bounded(
            replay_process.ProcessRequest(
                command=(executable.command_path,),
                cwd=runtime_directory,
                env=_runtime_environment(runtime_directory, dev_mode_value),
                timeout_seconds=RUNTIME_TIMEOUT_SECONDS,
                output_limit_bytes=MAX_RUNTIME_OUTPUT_BYTES,
                profile=replay_process.ProcessProfile.REPLAY,
                pass_fds=executable.pass_fds,
                stdin_bytes=request.raw,
                input_limit_bytes=MAX_RUNTIME_INPUT_BYTES,
            )
        )
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
        raise reject("VERIFIER_EXECUTION", str(exc)) from exc


def outcome(
    process: subprocess.CompletedProcess[bytes],
    *,
    expected_stdout: bytes,
    label: str,
    environment_profile: str,
) -> dict[str, Any]:
    if process.returncode != 0:
        raise reject("VERIFIER_EXIT", f"{label}:{process.returncode}")
    if process.stderr:
        raise reject("VERIFIER_STDERR", label)
    if process.stdout != expected_stdout:
        raise reject("VERIFIER_STDOUT", label)
    return {
        "environment_profile": environment_profile,
        "exit_code": process.returncode,
        "stderr_sha256": ZERO_SHA256,
        "stderr_size_bytes": 0,
        "stdout_sha256": hashlib.sha256(process.stdout).hexdigest(),
        "stdout_size_bytes": len(process.stdout),
    }


def _dev_mode_outcomes(
    executable: sealed_executable.SealedExecutable,
    inputs: RuntimeInputs,
    runtime_directory: Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    expected_reject = json.dumps(
        {"error": DEV_MODE_REJECT_ERROR, "ok": False},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    disabled = {
        value: outcome(
            run_verifier(
                executable,
                request=inputs.positive_request,
                runtime_directory=runtime_directory,
                dev_mode_value=value,
            ),
            expected_stdout=inputs.positive_stdout,
            label=f"positive_dev_mode_{value}",
            environment_profile=f"minimal_environment_risc0_dev_mode_{value}_v1",
        )
        for value in DEV_MODE_DISABLED_VALUES
    }
    enabled = {
        value: outcome(
            run_verifier(
                executable,
                request=inputs.positive_request,
                runtime_directory=runtime_directory,
                dev_mode_value=value,
            ),
            expected_stdout=expected_reject,
            label=f"positive_dev_mode_{value}",
            environment_profile=f"minimal_environment_risc0_dev_mode_{value}_v1",
        )
        for value in DEV_MODE_ENABLED_VALUES
    }
    return disabled, enabled


def _run_controls(
    executable: sealed_executable.SealedExecutable,
    inputs: RuntimeInputs,
    runtime_directory: Path,
) -> dict[str, Any]:
    positive = outcome(
        run_verifier(
            executable,
            request=inputs.positive_request,
            runtime_directory=runtime_directory,
            dev_mode_value=None,
        ),
        expected_stdout=inputs.positive_stdout,
        label="positive",
        environment_profile=ENVIRONMENT_PROFILE_ABSENT,
    )
    disabled, enabled = _dev_mode_outcomes(executable, inputs, runtime_directory)
    malformed = outcome(
        run_verifier(
            executable,
            request=inputs.malformed_request,
            runtime_directory=runtime_directory,
            dev_mode_value=None,
        ),
        expected_stdout=inputs.malformed_stdout,
        label="malformed",
        environment_profile=ENVIRONMENT_PROFILE_ABSENT,
    )
    return {
        "ambient_dev_mode_disabled_parity": disabled,
        "ambient_dev_mode_enabled_rejections": enabled,
        "malformed_exact_seal_mutation": malformed,
        "positive": positive,
    }


def execute_controls(
    paths: rebuild.RebuildEvidencePaths,
    artifact_report: Mapping[str, Any],
    reference: Mapping[str, Any],
    inputs: RuntimeInputs,
    runtime_directory: Path,
) -> ExecutionEvidence:
    runtime = replay_environment.create_private_target(runtime_directory)
    primary_error: BaseException | None = None
    try:
        with sealed_executable.SealedExecutable(paths.static_verifier) as executable:
            if executable.identity.sha256 != artifact_report.get("static_verifier_sha256"):
                raise reject("VERIFIER_IDENTITY", "sealed verifier hash mismatch")
            if executable.identity.size_bytes != reference["static_verifier"]["size_bytes"]:
                raise reject("VERIFIER_IDENTITY", "sealed verifier size mismatch")
            return ExecutionEvidence(
                live_runs=_run_controls(executable, inputs, runtime),
                verifier_identity={
                    "sha256": executable.identity.sha256,
                    "size_bytes": executable.identity.size_bytes,
                    "transport": executable.identity.transport,
                },
            )
    except BaseException as exc:
        primary_error = exc
        raise
    finally:
        try:
            shutil.rmtree(runtime)
        except OSError as exc:
            cleanup_error = reject("RUNTIME_CLEANUP_FAILED", "private runtime directory")
            if primary_error is None:
                raise cleanup_error from exc
            detail = f"cleanup_failure={cleanup_error.code}: private runtime directory"
            if isinstance(primary_error, LiveReplayError):
                primary_error.args = (f"{primary_error}; {detail}",)
            else:
                primary_error.add_note(detail)
