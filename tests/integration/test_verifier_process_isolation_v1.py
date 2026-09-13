"""Native capability evidence, enabled explicitly on a Linux proof host.

The C endpoint is a controlled attack probe, never a proof or signature oracle.
Network probes use a test-owned abstract Unix socket; no external traffic.
"""

from __future__ import annotations

import errno
import hashlib
import io
import os
import select
import signal
import socket
import stat
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

from src.integration import global_receipt_verifier_v1 as bridge


@pytest.fixture(scope="module")
def native_probe(tmp_path_factory: pytest.TempPathFactory) -> Path:
    if os.environ.get("ZENODEX_TEST_NATIVE_VERIFIER_ISOLATION") != "1":
        pytest.skip("explicit Linux namespace/native-execution qualification required")
    target = tmp_path_factory.mktemp("verifier-isolation") / "probe"
    source = Path(__file__).with_name("fixtures") / "verifier_isolation_probe_v1.c"
    subprocess.run(
        ("/usr/bin/cc", "-O2", "-Wall", "-Wextra", "-Werror", "-pthread", str(source), "-o", str(target)),
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


def _scope(process: subprocess.Popen[bytes]) -> Path:
    rows = Path(f"/proc/{process.pid}/cgroup").read_text().splitlines()
    unified = [row.removeprefix("0::") for row in rows if row.startswith("0::")]
    assert len(unified) == 1
    return Path("/sys/fs/cgroup") / unified[0].lstrip("/")


@pytest.mark.parametrize("mode", ("hold", "cpu"))
def test_limits_are_installed_before_endpoint_work_and_scope_is_empty_after_exit(
    native_probe: Path, monkeypatch: pytest.MonkeyPatch, mode: str,
) -> None:
    if mode == "cpu" and len(os.sched_getaffinity(0)) < 2:
        pytest.skip("native throttle observation requires at least two available CPUs")
    exchange = bridge._exchange_v1
    scopes = []

    def observe_scope(process, request, timeout_ms):
        process.stdin.write(request)
        process.stdin.flush()
        assert select.select([process.stdout], [], [], 5)[0]
        assert process.stdout.readline() == b"READY\n"
        scope = _scope(process)
        scopes.append(scope)
        assert scope.name.startswith("run-") and scope.name.endswith(".scope")
        assert (scope / "memory.max").read_text().strip() == "536870912"
        assert (scope / "memory.swap.max").read_text().strip() == "0"
        assert (scope / "memory.oom.group").read_text().strip() == "1"
        assert (scope / "pids.max").read_text().strip() == "16"
        quota, period = map(int, (scope / "cpu.max").read_text().split())
        assert quota == period
        if mode == "cpu":
            counters = dict(line.split() for line in (scope / "cpu.stat").read_text().splitlines())
            assert int(counters["nr_throttled"]) > 0
        return exchange(process, b"x", timeout_ms)

    monkeypatch.setattr(bridge, "_exchange_v1", observe_scope)
    assert _invoke(native_probe, f"{mode} unused\n".encode()) == b"DONE\n"
    assert len(scopes) == 1
    events = scopes[0] / "cgroup.events"
    assert not events.exists() or "populated 0" in events.read_text()


def test_resource_manager_environment_does_not_reach_the_endpoint(native_probe: Path) -> None:
    assert _invoke(native_probe, b"environment unused\n") == b"0 0 0 0 C\n"


@pytest.mark.parametrize("mode", ("tasks", "threads"))
def test_descendants_share_one_process_quota(native_probe: Path, mode: str) -> None:
    # All children remain alive until spawning ends, so process exit cannot
    # turn this into an unbounded sequence below an instantaneous limit.
    assert 1 <= int(_invoke(native_probe, f"{mode} unused\n".encode())) < 16


def test_children_cannot_multiply_the_memory_quota(native_probe: Path) -> None:
    backend = bridge.GlobalReceiptVerifierV1(
        str(native_probe), hashlib.sha256(native_probe.read_bytes()).hexdigest(),
        "0x" + "01" * 32, 5000,
    )
    with bridge._sealed_executable_v1(backend) as descriptor:
        stdout, _stderr, status = bridge._invoke_v1(descriptor, b"memory unused\n", 5000)
    assert status != 0
    assert b"ALLOCATED" not in stdout


def test_scope_backstop_terminates_a_session_escape_when_transport_deadline_is_lost(
    native_probe: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    exchange = bridge._exchange_v1

    def stalled_transport(process, request, timeout_ms):
        process.stdin.write(request)
        process.stdin.flush()
        assert select.select([process.stdout], [], [], 5)[0]
        assert process.stdout.readline() == b"READY\n"
        # Fault injection: the parent misses its 100 ms deadline. The external
        # 1100 ms backstop must end the group before this longer exchange ends.
        return exchange(process, b"", 5000)

    monkeypatch.setattr(bridge, "_exchange_v1", stalled_transport)
    backend = bridge.GlobalReceiptVerifierV1(
        str(native_probe), hashlib.sha256(native_probe.read_bytes()).hexdigest(),
        "0x" + "01" * 32, 100,
    )
    with bridge._sealed_executable_v1(backend) as descriptor:
        _stdout, _stderr, status = bridge._invoke_v1(descriptor, b"escape unused\n", 100)
    assert status != 0


@pytest.mark.parametrize(
    "permissions,foreign_owner,controllers",
    [
        (stat.S_IFREG | 0o700, False, b"cpu memory pids"),
        (stat.S_IFLNK | 0o700, False, b"cpu memory pids"),
        (stat.S_IFDIR | 0o700, True, b"cpu memory pids"),
        (stat.S_IFDIR | 0o770, False, b"cpu memory pids"),
        (stat.S_IFDIR | 0o707, False, b"cpu memory pids"),
        (stat.S_IFDIR | 0o700, False, b"memory pids"),
        (stat.S_IFDIR | 0o700, False, b"cpu pids"),
        (stat.S_IFDIR | 0o700, False, b"cpu memory"),
    ],
)
def test_unqualified_resource_host_rejects_before_process_creation(
    monkeypatch: pytest.MonkeyPatch, permissions: int, foreign_owner: bool, controllers: bytes,
) -> None:
    uid = os.geteuid()
    real_stat = os.stat

    def metadata(path, **kwargs):
        if os.fspath(path) == f"/run/user/{uid}":
            return SimpleNamespace(st_mode=permissions, st_uid=uid + int(foreign_owner))
        return real_stat(path, **kwargs)

    def forbidden(*args, **kwargs):
        pytest.fail("unqualified host launched a verifier")

    monkeypatch.setattr(bridge.os, "stat", metadata)
    monkeypatch.setattr(bridge, "open", lambda *args: io.BytesIO(controllers), raising=False)
    monkeypatch.setattr(bridge.subprocess, "Popen", forbidden)
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
        bridge._invoke_v1(123, b"request", 1000)
    assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE


def test_missing_user_manager_rejects_without_an_unbounded_fallback(
    native_probe: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(bridge, "_sandbox_environment_v1", lambda: {
        "RISC0_DEV_MODE": "0", "LC_ALL": "C", "XDG_RUNTIME_DIR": str(tmp_path / "missing"),
    })
    image = "0x" + "01" * 32
    backend = bridge.GlobalReceiptVerifierV1(
        str(native_probe), hashlib.sha256(native_probe.read_bytes()).hexdigest(), image, 5000,
    )
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
        backend.verify_succinct_receipt(b"fixture", expected_image_id=image, expected_journal_bytes=b"j")
    assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
    assert str(tmp_path) not in str(caught.value)


def test_interrupted_launcher_has_no_endpoint_holding_its_protocol_pipes(
    native_probe: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    start = subprocess.Popen
    processes = []

    def interrupt(command, **kwargs):
        process = start(command, **kwargs)
        processes.append(process)
        # Interrupt before the transport sends any input. Scope registration
        # may be pending or complete; neither case may leave an endpoint alive.
        os.killpg(process.pid, signal.SIGKILL)
        return process

    monkeypatch.setattr(bridge.subprocess, "Popen", interrupt)
    image = "0x" + "01" * 32
    backend = bridge.GlobalReceiptVerifierV1(
        str(native_probe), hashlib.sha256(native_probe.read_bytes()).hexdigest(), image, 1000,
    )
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
        backend.verify_succinct_receipt(b"fixture", expected_image_id=image, expected_journal_bytes=b"j")
    assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
    assert len(processes) == 1 and processes[0].returncode == -signal.SIGKILL
    assert all(stream.closed for stream in (processes[0].stdin, processes[0].stdout, processes[0].stderr))


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
    monkeypatch.setattr(bridge, "_sandbox_environment_v1", lambda: {})
    with pytest.raises(bridge.GlobalReceiptVerifierErrorV1) as caught:
        bridge._invoke_v1(123, b"request", 1000)
    assert caught.value.reason is bridge.GlobalReceiptVerifierRejectV1.PROCESS_UNAVAILABLE
    assert len(launches) == 1
    assert launches[0][0] == "/usr/bin/systemd-run"
    assert "/usr/bin/bwrap" in launches[0]
