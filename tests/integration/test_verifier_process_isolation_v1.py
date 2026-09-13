"""Native capability evidence, enabled explicitly on a Linux proof host.

The C endpoint is a controlled attack probe, never a proof or signature oracle.
Network probes use a test-owned abstract Unix socket; no external traffic.
"""

from __future__ import annotations

import errno
import hashlib
import os
import select
import signal
import socket
import subprocess
from pathlib import Path

import pytest

from src.integration import global_receipt_verifier_v1 as bridge


@pytest.fixture(scope="module")
def native_probe(tmp_path_factory: pytest.TempPathFactory) -> Path:
    if os.environ.get("ZENODEX_TEST_NATIVE_VERIFIER_ISOLATION") != "1":
        pytest.skip("explicit Linux namespace/native-execution qualification required")
    target = tmp_path_factory.mktemp("verifier-isolation") / "probe"
    source = Path(__file__).with_name("fixtures") / "verifier_isolation_probe_v1.c"
    subprocess.run(
        ("/usr/bin/cc", "-O2", "-Wall", "-Wextra", "-Werror", str(source), "-o", str(target)),
        check=True, capture_output=True, timeout=30,
    )
    return target


def _invoke(probe: Path, request: bytes, *, timeout_ms: int = 5000) -> bytes:
    backend = bridge.GlobalReceiptVerifierV1(
        str(probe), hashlib.sha256(probe.read_bytes()).hexdigest(), "0x" + "01" * 32,
        timeout_ms,
    )
    with bridge._sealed_executable_v1(backend) as descriptor:
        stdout, stderr, status = bridge._invoke_v1(descriptor, request, timeout_ms)
    assert (status, stderr) == (0, b"")
    return stdout


@pytest.mark.parametrize("operation", ("read", "write"))
def test_given_host_state_when_verifier_opens_it_then_access_is_denied_without_change(
    native_probe: Path, tmp_path: Path, operation: str,
) -> None:
    state = tmp_path / "owned-state"
    state.write_bytes(b"unchanged")
    request = f"{operation} {state}\n".encode()
    # Reachability control outside containment on disposable, test-owned state.
    control = subprocess.run((str(native_probe),), input=request, capture_output=True, check=True)
    assert control.stdout == b"1 0\n"
    state.write_bytes(b"unchanged")

    result = _invoke(native_probe, request)

    assert result == f"0 {errno.ENOENT}\n".encode()
    assert state.read_bytes() == b"unchanged"


def test_given_host_abstract_socket_when_verifier_connects_then_access_is_denied(
    native_probe: Path, tmp_path: Path,
) -> None:
    name = "zenodex-test-" + hashlib.sha256(str(tmp_path).encode()).hexdigest()
    request = f"network {name}\n".encode()
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
        listener.bind("\0" + name)
        listener.listen(2)
        control = subprocess.run((str(native_probe),), input=request, capture_output=True, check=True)
        assert control.stdout == b"1\n"

        result = _invoke(native_probe, request)

    assert result == b"0\n"


def test_verifier_has_no_privilege_or_nested_user_namespace_authority(native_probe: Path) -> None:
    assert _invoke(native_probe, b"privileges unused\n") == b"1 0 0 -1\n"


@pytest.mark.parametrize("path", ("/proc/self/status", "/dev/null", "/etc/passwd"))
def test_verifier_runtime_does_not_mount_proc_devices_or_host_configuration(
    native_probe: Path, path: str,
) -> None:
    request = f"read {path}\n".encode()
    control = subprocess.run((str(native_probe),), input=request, capture_output=True, check=True)
    assert control.stdout == b"1 0\n"
    assert _invoke(native_probe, request) == f"0 {errno.ENOENT}\n".encode()


def _leaf_processes(parent: int) -> tuple[int, ...]:
    path = Path(f"/proc/{parent}/task/{parent}/children")
    children = tuple(map(int, path.read_text().split()))
    return tuple(leaf for child in children for leaf in _leaf_processes(child)) or (parent,)


def test_timeout_terminates_descendant_even_after_it_creates_a_new_session(
    native_probe: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    exchange = bridge._exchange_v1
    descendants: list[int] = []

    def observe_child(process, request, timeout_ms):
        # Synchronize with the child's successful setsid before opening pidfds.
        process.stdin.write(request)
        process.stdin.flush()
        assert select.select([process.stdout], [], [], 5)[0], "probe did not become ready"
        assert process.stdout.readline() == b"READY\n"
        descendants.extend(os.pidfd_open(pid) for pid in _leaf_processes(process.pid))
        return exchange(process, b"", timeout_ms)

    monkeypatch.setattr(bridge, "_exchange_v1", observe_child)
    try:
        with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
            _invoke(native_probe, b"escape unused\n", timeout_ms=100)
        assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_TIMEOUT
        assert descendants
        for descriptor in descendants:
            assert select.select([descriptor], [], [], 2)[0], "escaped verifier child survived"
    finally:
        # A failing baseline or mutant must never leave the controlled probe alive.
        for descriptor in descendants:
            try:
                signal.pidfd_send_signal(descriptor, signal.SIGKILL)
            except ProcessLookupError:
                pass
            os.close(descriptor)


def test_missing_isolator_never_falls_back_to_direct_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    launches = []

    def unavailable(command, **kwargs):
        launches.append(command)
        raise FileNotFoundError("test-owned unavailable launcher")

    monkeypatch.setattr(bridge.subprocess, "Popen", unavailable)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
        bridge._invoke_v1(123, b"request", 1000)
    assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
    assert len(launches) == 1
    assert launches[0][0] == "/usr/bin/bwrap"
