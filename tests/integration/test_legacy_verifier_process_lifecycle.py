"""Real process-lifetime regressions; JSON endpoints here are protocol fixtures."""

from __future__ import annotations

import json
import os
import selectors
import signal
import subprocess
import sys

import pytest

from src.integration import _verifier_process as lifecycle
from src.integration import confidential_attestation_verifier as attestation
from src.integration import proof_verifier as proof


@pytest.fixture(params=(proof.SubprocessProofVerifier, attestation.SubprocessConfidentialAttestationVerifier))
def verifier_type(request):
    return request.param


def _verifier(verifier_type, code: str, *, timeout_s: float = 2.0):
    return verifier_type(
        cmd=[sys.executable, "-c", code], timeout_s=timeout_s,
        max_bytes=1024, max_stdout_bytes=1024, max_stderr_bytes=1024,
    )


def _response() -> dict:
    return {"ok": True, "result": {
        "measurement": "0x" + "11" * 32, "policy_digest": "0x" + "22" * 32,
        "attestation_epoch": 1,
    }}


@pytest.mark.parametrize("timeout", (float("nan"), float("inf"), float("-inf"), 10**1000))
def test_nonfinite_timeout_cannot_construct_a_verifier(verifier_type, timeout):
    with pytest.raises(ValueError, match="timeout_s must be positive"):
        _verifier(verifier_type, "raise SystemExit('must not run')", timeout_s=timeout)


@pytest.mark.parametrize("exit_status", (0, 7, -signal.SIGTERM))
def test_completed_verifier_cannot_leave_a_same_group_descendant_running(
    verifier_type, exit_status, monkeypatch,
):
    read_fd, write_fd = os.pipe()
    original_popen = subprocess.Popen
    processes = []

    def launch(*args, **kwargs):
        process = original_popen(*args, **(kwargs | {"pass_fds": (write_fd,)}))
        processes.append(process)
        return process

    monkeypatch.setattr(subprocess, "Popen", launch)
    code = f"""
import os, signal, sys
sys.stdin.buffer.read()
ready_read, ready_write = os.pipe()
if os.fork() == 0:
    os.write({write_fd}, b'R')
    os.write(ready_write, b'R')
    for fd in (0, 1, 2):
        os.close(fd)
    signal.pause()
    os._exit(99)
os.read(ready_read, 1)
sys.stdout.write({json.dumps(_response())!r})
sys.stdout.flush()
if {exit_status} < 0:
    os.kill(os.getpid(), -{exit_status})
sys.exit({exit_status})
"""
    group_closed = False
    try:
        value, error = _verifier(verifier_type, code).verify({})
        assert (error is None) is (exit_status == 0)
        assert bool(value) is (exit_status == 0)
        os.close(write_fd)
        write_fd = -1
        assert os.read(read_fd, 1) == b"R"
        with selectors.DefaultSelector() as selector:
            selector.register(read_fd, selectors.EVENT_READ)
            assert selector.select(2), "verifier descendant survived completed verification"
        group_closed = os.read(read_fd, 1) == b""
        assert group_closed
        assert len(processes) == 1 and processes[0].returncode == exit_status
    finally:
        # The failing baseline's controlled child keeps this process group alive.
        if not group_closed and processes:
            try:
                os.killpg(processes[0].pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if write_fd >= 0:
            os.close(write_fd)
        os.close(read_fd)


@pytest.mark.parametrize("observed_at,accepted", ((0.999, True), (1.0, False), (1.001, False)))
def test_completion_obeys_deadline(verifier_type, monkeypatch, observed_at, accepted):
    now = [0.0]
    monkeypatch.setattr(proof.time, "monotonic", lambda: now[0])
    original_popen = subprocess.Popen
    original_observe = lifecycle.unreaped_exit_status

    def observe(pid):
        status = original_observe(pid)
        if status is not None:
            now[0] = observed_at
        return status

    def launch(*args, **kwargs):
        process = original_popen(*args, **kwargs)
        poll = process.poll
        wait = process.wait

        def observe_old_poll():
            status = poll()
            if status is not None:
                now[0] = observed_at
            return status

        process.poll = observe_old_poll

        def observe_old_wait(*args, **kwargs):
            status = wait(*args, **kwargs)
            now[0] = observed_at
            return status

        process.wait = observe_old_wait
        return process

    monkeypatch.setattr(subprocess, "Popen", launch)
    monkeypatch.setattr(lifecycle, "unreaped_exit_status", observe)
    code = "import sys; sys.stdin.buffer.read(); sys.stdout.write(" + repr(json.dumps(_response())) + ")"
    value, error = _verifier(verifier_type, code, timeout_s=1.0).verify({})
    assert bool(value) is accepted
    assert (error is None) is accepted
    if not accepted:
        assert "timed out" in error


@pytest.mark.parametrize("missing", ("waitid", "WNOWAIT"))
def test_unavailable_unreaped_wait_rejects_before_launch(verifier_type, monkeypatch, missing):
    monkeypatch.delattr(os, missing)
    monkeypatch.setattr(subprocess, "Popen", lambda *args, **kwargs: pytest.fail("must not launch"))
    value, error = _verifier(verifier_type, "").verify({})
    assert not value
    assert error is not None and "requires waitid with WNOWAIT" in error


def test_exit_observation_error_rejects(verifier_type, monkeypatch):
    def unavailable(pid):
        raise ChildProcessError("exit status unavailable")

    monkeypatch.setattr(lifecycle, "unreaped_exit_status", unavailable)
    code = "import sys; sys.stdin.buffer.read(); sys.stdout.write(" + repr(json.dumps(_response())) + ")"
    value, error = _verifier(verifier_type, code).verify({})
    assert not value
    assert error is not None and "did not exit" in error


def test_closed_pipes_do_not_hide_a_running_verifier(verifier_type, monkeypatch):
    read_fd, write_fd = os.pipe()
    original_popen = subprocess.Popen

    def launch(*args, **kwargs):
        return original_popen(*args, **(kwargs | {"pass_fds": (read_fd,)}))

    monkeypatch.setattr(subprocess, "Popen", launch)
    code = f"import os, sys; sys.stdin.buffer.read(); os.close(1); os.close(2); os.read({read_fd}, 1)"
    try:
        value, error = _verifier(verifier_type, code, timeout_s=0.1).verify({})
        assert not value
        assert error is not None and "timed out" in error
    finally:
        os.close(read_fd)
        os.close(write_fd)


def test_missing_pipe_still_terminates_and_reaps_child(verifier_type, monkeypatch):
    original_popen = subprocess.Popen
    processes = []
    detached_streams = []

    def launch(*args, **kwargs):
        process = original_popen(*args, **kwargs)
        detached_streams.append(process.stdout)
        process.stdout = None
        processes.append(process)
        return process

    monkeypatch.setattr(subprocess, "Popen", launch)
    try:
        value, error = _verifier(verifier_type, "import sys; sys.stdin.buffer.read()").verify({})
        assert not value
        assert error is not None and "subprocess pipes unavailable" in error
        assert len(processes) == 1 and processes[0].returncode is not None
    finally:
        for process in processes:
            if process.returncode is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=1)
        for stream in detached_streams:
            stream.close()
