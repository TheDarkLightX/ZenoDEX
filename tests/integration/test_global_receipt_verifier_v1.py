"""Process-protocol evidence only; no fixture in this module is a RISC0 proof."""

from __future__ import annotations

import hashlib
import os
import selectors
import signal
import subprocess
import sys
import traceback
from pathlib import Path

import pytest

from src.integration import global_receipt_verifier_v1 as bridge

IMAGE = "0x" + "01" * 32
OTHER_IMAGE = "0x" + "02" * 32


def backend(**changes: object) -> bridge.GlobalReceiptVerifierV1:
    options: dict[str, object] = {
        "executable_path": str(Path(sys.executable).resolve()),
        "executable_sha256": hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest(),
        "expected_image_id": IMAGE,
        "timeout_ms": 5000,
    }
    options.update(changes)
    return bridge.GlobalReceiptVerifierV1(**options)  # type: ignore[arg-type]


def verify(verifier: bridge.GlobalReceiptVerifierV1, **changes: object) -> None:
    options: dict[str, object] = {
        "receipt_bytes": b"fixture-receipt-is-not-proof",
        "expected_image_id": IMAGE,
        "expected_journal_bytes": b"journal",
    }
    options.update(changes)
    verifier.verify_succinct_receipt(**options)  # type: ignore[arg-type]


def install_protocol_process(
    monkeypatch: pytest.MonkeyPatch,
    code: str,
    inherited_descriptors: tuple[int, ...] = (),
) -> list[subprocess.Popen[bytes]]:
    """Substitute the launch only; sandbox memfd execution is unavailable locally.

    The sealed measured bytes are checked independently. This fixture exercises
    the pipes and protocol with an ordinary interpreter, never cryptography or
    successful deployment of the measured executable.
    """
    original_popen = subprocess.Popen
    started: list[subprocess.Popen[bytes]] = []
    # Protocol fixtures do not qualify the host's manager or cgroup delegation.
    fixture_environment = {"RISC0_DEV_MODE": "0", "LC_ALL": "C", "XDG_RUNTIME_DIR": "/fixture"}
    monkeypatch.setattr(bridge, "_sandbox_environment_v1", lambda: dict(fixture_environment))

    def launch(command: tuple[str, ...], **kwargs: object) -> subprocess.Popen[bytes]:
        assert kwargs["env"] == fixture_environment
        assert kwargs["start_new_session"] is True
        assert command[0] == "/usr/bin/systemd-run"
        assert "/usr/bin/bwrap" in command
        assert command[-1] == "/verifier"
        kwargs["pass_fds"] = (*kwargs["pass_fds"], *inherited_descriptors)  # type: ignore[misc]
        process = original_popen((sys.executable, "-c", code), **kwargs)  # type: ignore[call-overload]
        started.append(process)
        return process

    monkeypatch.setattr(bridge.subprocess, "Popen", launch)
    return started


PROTOCOL_ACCEPT = """
import hashlib, sys
request = sys.stdin.buffer.read()
image = request[8:40]
sys.stdout.buffer.write(b'ZDXRV1OK' + hashlib.sha256(request).digest() + image)
"""


def test_given_protocol_fixture_when_exact_response_then_transport_accepts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    install_protocol_process(monkeypatch, PROTOCOL_ACCEPT)
    verify(backend())


@pytest.mark.parametrize(
    "changes",
    [
        {"executable_path": "relative/path"},
        {"executable_path": "/nul\x00path"},
        {"executable_sha256": "AA" * 32},
        {"expected_image_id": "0x" + "00" * 32},
        {"expected_image_id": "0x" + "AA" * 32},
        {"timeout_ms": 0},
        {"timeout_ms": 60_001},
        {"timeout_ms": True},
    ],
)
def test_invalid_deployment_parameters_never_construct_backend(changes: dict[str, object]) -> None:
    with pytest.raises(ValueError):
        backend(**changes)


def test_request_frame_has_independent_fixed_vector() -> None:
    request = bridge._encode_request_v1(b"receipt", IMAGE, b"journal")
    assert request == (b"ZDXRV1RQ" + b"\x01" * 32 + b"\x07\x00\x00\x00" * 2 + b"journalreceipt")


@pytest.mark.parametrize(
    "changes,reason",
    [
        ({"expected_image_id": OTHER_IMAGE}, "IMAGE_BINDING"),
        ({"expected_image_id": "0x" + "00" * 32}, "IMAGE_BINDING"),
        ({"receipt_bytes": b""}, "INPUT_BOUNDS"),
        ({"receipt_bytes": bytearray(b"receipt")}, "INPUT_BOUNDS"),
        ({"expected_journal_bytes": b""}, "INPUT_BOUNDS"),
        ({"expected_journal_bytes": memoryview(b"journal")}, "INPUT_BOUNDS"),
        ({"receipt_bytes": b"x" * (bridge.MAX_RECEIPT_BYTES_V1 + 1)}, "INPUT_BOUNDS"),
        ({"expected_journal_bytes": b"x" * (bridge.MAX_JOURNAL_BYTES_V1 + 1)}, "INPUT_BOUNDS"),
    ],
)
def test_invalid_request_rejects_before_launch(
    monkeypatch: pytest.MonkeyPatch,
    changes: dict[str, object],
    reason: str,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("invalid input launched verifier")

    monkeypatch.setattr(bridge.subprocess, "Popen", forbidden)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend(), **changes)
    assert error.value.reason.value == reason


@pytest.mark.parametrize(
    "code,reason",
    [
        ("import sys; sys.stdin.buffer.read(); sys.exit(2)", "VERIFICATION_REJECTED"),
        ("import sys; sys.stdin.buffer.read(); print('accepted')", "RESPONSE_BINDING"),
        (PROTOCOL_ACCEPT.replace("image)", "b'\\x02' * 32)"), "RESPONSE_BINDING"),
        (
            PROTOCOL_ACCEPT.replace("hashlib.sha256(request).digest()", "b'\\x00' * 32"),
            "RESPONSE_BINDING",
        ),
        (PROTOCOL_ACCEPT + "\nsys.stdout.buffer.write(b'extra')", "RESPONSE_BINDING"),
        (PROTOCOL_ACCEPT + "\nsys.stderr.write('diagnostic')", "RESPONSE_BINDING"),
        (
            "import sys; sys.stdin.buffer.read(); sys.stdout.buffer.write(b'x' * 65536)",
            "OUTPUT_LIMIT",
        ),
        (
            "import sys; sys.stdin.buffer.read(); sys.stderr.buffer.write(b'x' * 65536)",
            "OUTPUT_LIMIT",
        ),
    ],
)
def test_unbound_response_or_resource_failure_has_typed_rejection(
    monkeypatch: pytest.MonkeyPatch,
    code: str,
    reason: str,
) -> None:
    processes = install_protocol_process(monkeypatch, code)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend())
    assert error.value.reason.value == reason
    assert all(process.returncode is not None for process in processes)


def test_executable_digest_mismatch_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend(executable_sha256="00" * 32))
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING


def test_unavailable_executable_rejects(tmp_path: Path) -> None:
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend(executable_path=str(tmp_path / "absent")))
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.EXECUTABLE_UNAVAILABLE


def test_unavailable_launch_is_typed_and_contains_no_backend_details(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def unavailable(*args: object, **kwargs: object) -> None:
        raise PermissionError("private backend details")

    monkeypatch.setattr(bridge.subprocess, "Popen", unavailable)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend())
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
    assert "private backend details" not in str(error.value)
    assert "private backend details" not in "".join(traceback.format_exception(error.value))


def test_script_cannot_substitute_for_measured_elf(tmp_path: Path) -> None:
    script = tmp_path / "verifier"
    script.write_bytes(b"#!/bin/sh\nexit 0\n")
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(
            backend(
                executable_path=str(script),
                executable_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),
            )
        )
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING


def test_measured_executable_snapshot_is_sealed_against_later_writes() -> None:
    verifier = backend()
    with bridge._sealed_executable_v1(verifier) as descriptor:
        assert os.read(descriptor, 4) == b"\x7fELF"
        with pytest.raises(PermissionError):
            os.write(descriptor, b"mutation")


def test_source_replacement_cannot_change_sealed_snapshot(tmp_path: Path) -> None:
    original_bytes = Path(sys.executable).read_bytes()
    source = tmp_path / "verifier"
    source.write_bytes(original_bytes)
    verifier = backend(executable_path=str(source))
    with bridge._sealed_executable_v1(verifier) as descriptor:
        source.write_bytes(b"replacement")
        with os.fdopen(os.dup(descriptor), "rb") as snapshot:
            assert snapshot.read() == original_bytes


def test_timeout_rejects_and_reaps_process_without_sleep(monkeypatch: pytest.MonkeyPatch) -> None:
    processes = install_protocol_process(monkeypatch, "import sys; sys.stdin.buffer.read()")
    ticks = iter((0, 10_000_000_000))
    monkeypatch.setattr(bridge.time, "monotonic_ns", lambda: next(ticks))
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
        verify(backend())
    assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT
    assert len(processes) == 1 and processes[0].returncode is not None


@pytest.mark.parametrize("deadline_offset_ns", [-1, 0, 1])
def test_exact_response_must_be_observed_before_deadline(
    monkeypatch: pytest.MonkeyPatch,
    deadline_offset_ns: int,
) -> None:
    processes = install_protocol_process(monkeypatch, PROTOCOL_ACCEPT)
    elapsed_ns = 0
    observe = bridge._unreaped_exit_status_v1

    def observe_at_deadline(process_id: int) -> int | None:
        nonlocal elapsed_ns
        status = observe(process_id)
        if status is not None:
            elapsed_ns = 5_000_000_000 + deadline_offset_ns
        return status

    monkeypatch.setattr(bridge.time, "monotonic_ns", lambda: elapsed_ns)
    monkeypatch.setattr(bridge, "_unreaped_exit_status_v1", observe_at_deadline)
    if deadline_offset_ns < 0:
        verify(backend())
    else:
        with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
            verify(backend())
        assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT
    assert len(processes) == 1 and processes[0].returncode == 0


def test_reaped_process_pid_is_never_signalled(monkeypatch: pytest.MonkeyPatch) -> None:
    process = subprocess.Popen((sys.executable, "-c", ""), start_new_session=True)
    process.wait()

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("reaped process PID could have been reused")

    monkeypatch.setattr(bridge.os, "killpg", forbidden)
    bridge._kill_and_reap_v1(process)


@pytest.mark.parametrize("exit_status", [0, 2, -signal.SIGTERM])
def test_exited_verifier_cannot_leave_same_group_descendant_running(
    monkeypatch: pytest.MonkeyPatch,
    exit_status: int,
) -> None:
    # EOF on this independent pipe requires every inherited writer to close.
    # The descendant retains its writer while blocked, even after closing stdio.
    read_fd, write_fd = os.pipe()
    code = f"""
import hashlib, os, signal, sys
request = sys.stdin.buffer.read()
if os.fork() == 0:
    os.write({write_fd}, b'R')
    for descriptor in (0, 1, 2):
        os.close(descriptor)
    signal.pause()
    os._exit(99)
sys.stdout.buffer.write(b'ZDXRV1OK' + hashlib.sha256(request).digest() + request[8:40])
sys.stdout.buffer.flush()
if {exit_status} < 0:
    os.kill(os.getpid(), -{exit_status})
sys.exit({exit_status})
"""
    processes = install_protocol_process(monkeypatch, code, (write_fd,))
    group_closed = False
    try:
        if exit_status == 0:
            verify(backend())
        else:
            with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as error:
                verify(backend())
            assert error.value.reason is bridge.GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
        os.close(write_fd)
        write_fd = -1
        assert os.read(read_fd, 1) == b'R'
        with selectors.DefaultSelector() as selector:
            selector.register(read_fd, selectors.EVENT_READ)
            assert selector.select(2), "verifier descendant retained execution after return"
        group_closed = os.read(read_fd, 1) == b''
        assert group_closed, "verifier descendant did not close its inherited writer"
        assert len(processes) == 1 and processes[0].returncode == exit_status
    finally:
        # A failing baseline leaves the controlled child holding this PGID.
        if not group_closed and processes:
            try:
                os.killpg(processes[0].pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if write_fd >= 0:
            os.close(write_fd)
        os.close(read_fd)


def test_exact_retry_repeats_verification_with_no_replay_consumption(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    install_protocol_process(monkeypatch, PROTOCOL_ACCEPT)
    verifier = backend()
    verify(verifier)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1):
        verify(verifier, expected_image_id=OTHER_IMAGE)
    verify(verifier)
