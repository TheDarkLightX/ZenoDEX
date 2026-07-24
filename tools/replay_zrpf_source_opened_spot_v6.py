#!/usr/bin/env python3
"""Execute the retained Spot V6 settlement and full-chain verifier controls.

This runner compares exact canonical transcripts. It supplies no sandbox,
release, ledger, settlement, privacy, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import selectors
import signal
import stat
import subprocess
import time
from contextlib import ExitStack
from dataclasses import dataclass
from functools import partial
from pathlib import Path
from typing import Any

if __package__:
    from tools import zrpf_v3_replay_process as replay_process
    from tools import zrpf_v3_replay_sealed_executable as sealed_executable
else:
    import zrpf_v3_replay_process as replay_process
    import zrpf_v3_replay_sealed_executable as sealed_executable

SETTLEMENT_REQUEST_SCHEMA = "zenodex.source_opened_spot_settlement_verifier_v6.request.v1"
SETTLEMENT_ERROR_SCHEMA = "zenodex.source_opened_spot_settlement_verifier_v6.error.v1"
CHAIN_REQUEST_SCHEMA = "zenodex.source_opened_spot_v6_chain_verifier.request.v1"
REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_retained_replay/v1"
MUTATION_ERROR_CODE = "source_opened_spot_settlement_v6_receipt_rejected"
MAX_ARTIFACT_BYTES = 64 * 1_024 * 1_024
MAX_REQUEST_BYTES = 64 * 1_024 * 1_024
MAX_STDOUT_BYTES = 20 * 1_024 * 1_024
MAX_STDERR_BYTES = 1 * 1_024 * 1_024
TIMEOUT_SECONDS = 300


class ReplayError(ValueError):
    """Stable retained-replay rejection."""


def canonical_request(fields: tuple[tuple[str, str], ...]) -> bytes:
    return json.dumps(
        dict(fields),
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")


def replay(
    *,
    artifact_directory: Path,
    settlement_verifier: Path,
    chain_verifier: Path,
) -> dict[str, Any]:
    artifacts = {
        name: _read_bounded_regular_file(artifact_directory / name)
        for name in (
            "leaf_source_envelope.bin",
            "leaf_receipt.json",
            "leaf_mutation_receipt.json",
            "l1_receipt.json",
            "l1_mutation_receipt.json",
            "l2_receipt.json",
            "l2_mutation_receipt.json",
            "settlement_receipt.json",
            "settlement_mutation_receipt.json",
            "settlement_guest_input.bin",
            "external_verifier_output.json",
            "chain_verifier_output.json",
        )
    }
    try:
        with ExitStack() as stack:
            settlement = stack.enter_context(
                sealed_executable.SealedExecutable(settlement_verifier)
            )
            chain = stack.enter_context(sealed_executable.SealedExecutable(chain_verifier))
            return _replay_with_sealed_verifiers(
                artifacts,
                settlement=settlement,
                chain=chain,
            )
    except RuntimeError as exc:
        raise ReplayError("verifier snapshot failed") from exc


def _replay_with_sealed_verifiers(
    artifacts: dict[str, bytes],
    *,
    settlement: sealed_executable.SealedExecutable,
    chain: sealed_executable.SealedExecutable,
) -> dict[str, Any]:
    positive = _run_verifier(
        settlement,
        _settlement_request(artifacts, mutation=False),
        ambient_dev=False,
    )
    _require_success(
        positive,
        artifacts["external_verifier_output.json"],
        "settlement positive replay",
    )

    mutation = _run_verifier(
        settlement,
        _settlement_request(artifacts, mutation=True),
        ambient_dev=False,
    )
    _require_mutation_reject(mutation)

    chain_request = _chain_request(artifacts)
    normal = _run_verifier(chain, chain_request, ambient_dev=False)
    ambient_dev = _run_verifier(chain, chain_request, ambient_dev=True)
    expected_chain = artifacts["chain_verifier_output.json"]
    _require_success(normal, expected_chain, "normal chain replay")
    _require_success(ambient_dev, expected_chain, "ambient-dev chain replay")
    if normal.stdout != ambient_dev.stdout:
        raise ReplayError("normal and ambient-dev chain outputs differ")

    return {
        "ambient_dev_chain_output_sha256": _sha256(ambient_dev.stdout),
        "chain_verifier_sha256": chain.identity.sha256,
        "exact_seal_mutations_rejected": 4,
        "fake_receipt_rejected": True,
        "normal_chain_output_sha256": _sha256(normal.stdout),
        "normal_dev_outputs_equal": True,
        "ok": True,
        "positive_receipts_verified": 4,
        "production_authority": False,
        "release_authority": False,
        "schema": REPORT_SCHEMA,
        "settlement_authority": False,
        "settlement_mutation_error_code": MUTATION_ERROR_CODE,
        "settlement_verifier_sha256": settlement.identity.sha256,
        "settlement_verifier_output_sha256": _sha256(positive.stdout),
    }


def _settlement_request(artifacts: dict[str, bytes], *, mutation: bool) -> bytes:
    receipt = "settlement_mutation_receipt.json" if mutation else "settlement_receipt.json"
    return canonical_request(
        (
            ("schema", SETTLEMENT_REQUEST_SCHEMA),
            ("receipt_hex", artifacts[receipt].hex()),
            ("guest_input_hex", artifacts["settlement_guest_input.bin"].hex()),
        )
    )


def _chain_request(artifacts: dict[str, bytes]) -> bytes:
    return canonical_request(
        (
            ("schema", CHAIN_REQUEST_SCHEMA),
            ("leaf_source_envelope_hex", artifacts["leaf_source_envelope.bin"].hex()),
            ("leaf_receipt_hex", artifacts["leaf_receipt.json"].hex()),
            (
                "leaf_mutation_receipt_hex",
                artifacts["leaf_mutation_receipt.json"].hex(),
            ),
            ("level_one_receipt_hex", artifacts["l1_receipt.json"].hex()),
            (
                "level_one_mutation_receipt_hex",
                artifacts["l1_mutation_receipt.json"].hex(),
            ),
            ("level_two_receipt_hex", artifacts["l2_receipt.json"].hex()),
            (
                "level_two_mutation_receipt_hex",
                artifacts["l2_mutation_receipt.json"].hex(),
            ),
            ("settlement_receipt_hex", artifacts["settlement_receipt.json"].hex()),
            (
                "settlement_mutation_receipt_hex",
                artifacts["settlement_mutation_receipt.json"].hex(),
            ),
            (
                "settlement_guest_input_hex",
                artifacts["settlement_guest_input.bin"].hex(),
            ),
        )
    )


@dataclass(frozen=True)
class _CompletedVerifier:
    returncode: int
    stdout: bytes
    stderr: bytes


def _run_verifier(
    executable: sealed_executable.SealedExecutable,
    request: bytes,
    *,
    ambient_dev: bool,
) -> _CompletedVerifier:
    if not request or len(request) > MAX_REQUEST_BYTES:
        raise ReplayError("verifier request exceeds governed bound")
    environment = {
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    if ambient_dev:
        environment["RISC0_DEV_MODE"] = "1"
    try:
        process = subprocess.Popen(
            [executable.command_path],
            cwd=Path("/"),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            pass_fds=executable.pass_fds,
            preexec_fn=partial(
                replay_process._apply_process_profile,
                replay_process.ProcessProfile.REPLAY,
                TIMEOUT_SECONDS,
                max(MAX_STDOUT_BYTES, MAX_STDERR_BYTES),
            ),
            start_new_session=True,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise ReplayError("verifier process failed") from exc
    deadline = time.monotonic() + TIMEOUT_SECONDS
    try:
        stdout, stderr = _communicate_bounded(process, request, deadline)
        try:
            return_code = process.wait(timeout=max(0.1, deadline - time.monotonic()))
        except subprocess.TimeoutExpired as exc:
            raise ReplayError("verifier process timed out") from exc
    except BaseException:
        _kill_process_group(process)
        raise
    return _CompletedVerifier(return_code, stdout, stderr)


def _communicate_bounded(
    process: subprocess.Popen[bytes],
    request: bytes,
    deadline: float,
) -> tuple[bytes, bytes]:
    if process.stdin is None or process.stdout is None or process.stderr is None:
        raise ReplayError("verifier process pipes were not created")
    stdin = process.stdin
    stdout = process.stdout
    stderr = process.stderr
    for stream in (stdin, stdout, stderr):
        os.set_blocking(stream.fileno(), False)
    selector = selectors.DefaultSelector()
    selector.register(stdin, selectors.EVENT_WRITE, "stdin")
    selector.register(stdout, selectors.EVENT_READ, "stdout")
    selector.register(stderr, selectors.EVENT_READ, "stderr")
    outputs = {"stdout": bytearray(), "stderr": bytearray()}
    request_offset = 0
    try:
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise ReplayError("verifier process timed out")
            events = selector.select(remaining)
            if not events:
                raise ReplayError("verifier process timed out")
            for key, _event in events:
                label = key.data
                if label == "stdin":
                    request_offset = _write_request_chunk(
                        selector,
                        stdin,
                        request,
                        request_offset,
                    )
                    continue
                limit = MAX_STDOUT_BYTES if label == "stdout" else MAX_STDERR_BYTES
                _read_output_chunk(selector, key.fileobj, outputs[label], limit)
    finally:
        selector.close()
        for stream in (stdin, stdout, stderr):
            if not stream.closed:
                stream.close()
    if request_offset != len(request):
        raise ReplayError("verifier process did not consume the complete request")
    return bytes(outputs["stdout"]), bytes(outputs["stderr"])


def _write_request_chunk(
    selector: selectors.BaseSelector,
    stdin: Any,
    request: bytes,
    offset: int,
) -> int:
    try:
        written = os.write(stdin.fileno(), request[offset : offset + 65_536])
    except BlockingIOError:
        return offset
    except BrokenPipeError as exc:
        raise ReplayError("verifier process closed stdin before the complete request") from exc
    if written <= 0:
        raise ReplayError("verifier request write failed")
    offset += written
    if offset == len(request):
        selector.unregister(stdin)
        stdin.close()
    return offset


def _read_output_chunk(
    selector: selectors.BaseSelector,
    stream: Any,
    output: bytearray,
    limit: int,
) -> None:
    try:
        chunk = os.read(stream.fileno(), min(65_536, limit + 1 - len(output)))
    except BlockingIOError:
        return
    if chunk:
        output.extend(chunk)
        if len(output) > limit:
            raise ReplayError("verifier output exceeds governed bound")
        return
    selector.unregister(stream)
    stream.close()


def _kill_process_group(process: subprocess.Popen[bytes]) -> None:
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    for stream in (process.stdin, process.stdout, process.stderr):
        if stream is not None and not stream.closed:
            stream.close()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def _require_success(
    completed: _CompletedVerifier,
    expected_stdout: bytes,
    label: str,
) -> None:
    if completed.returncode != 0:
        raise ReplayError(f"{label} returned nonzero")
    if completed.stderr:
        raise ReplayError(f"{label} emitted stderr")
    if completed.stdout != expected_stdout:
        raise ReplayError(f"{label} output differs from retained transcript")


def _require_mutation_reject(completed: _CompletedVerifier) -> None:
    if completed.returncode == 0 or completed.stdout:
        raise ReplayError("settlement mutation did not fail closed")
    try:
        response = json.loads(completed.stderr)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReplayError("settlement mutation error is not JSON") from exc
    expected = {
        "ok": False,
        "schema": SETTLEMENT_ERROR_SCHEMA,
        "error_code": MUTATION_ERROR_CODE,
    }
    expected_bytes = (json.dumps(expected, separators=(",", ":")) + "\n").encode()
    if response != expected or completed.stderr != expected_bytes:
        raise ReplayError("settlement mutation reject transcript mismatch")


def _read_bounded_regular_file(path: Path) -> bytes:
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise ReplayError("artifact metadata is unavailable") from exc
    if (
        path.is_symlink()
        or not stat.S_ISREG(metadata.st_mode)
        or metadata.st_size <= 0
        or metadata.st_size > MAX_ARTIFACT_BYTES
    ):
        raise ReplayError("artifact must be a bounded regular file")
    raw = path.read_bytes()
    after = path.stat(follow_symlinks=False)
    if len(raw) != metadata.st_size or (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ) != (metadata.st_dev, metadata.st_ino, metadata.st_size, metadata.st_mtime_ns):
        raise ReplayError("artifact changed while it was read")
    return raw


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-directory", type=Path, required=True)
    parser.add_argument("--settlement-verifier", type=Path, required=True)
    parser.add_argument("--chain-verifier", type=Path, required=True)
    arguments = parser.parse_args()
    try:
        report = replay(
            artifact_directory=arguments.artifact_directory,
            settlement_verifier=arguments.settlement_verifier,
            chain_verifier=arguments.chain_verifier,
        )
    except (OSError, ReplayError) as exc:
        report = {
            "errors": [str(exc)],
            "ok": False,
            "production_authority": False,
            "release_authority": False,
            "schema": REPORT_SCHEMA,
            "settlement_authority": False,
        }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
