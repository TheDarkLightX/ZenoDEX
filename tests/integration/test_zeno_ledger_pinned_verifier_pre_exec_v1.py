from __future__ import annotations

import errno
import hashlib
import json
import os
import socket
from pathlib import Path

import pytest

from src.integration import _zeno_ledger_pinned_verifier_process_v1 as pinned

_ADDRESS_SPACE_BYTES = 384 * 1024 * 1024
_STACK_BYTES = 8 * 1024 * 1024
_TIMEOUT_SECONDS = 4


def _write_script(path: Path, source: str) -> Path:
    path.write_text("#!/usr/bin/env python3\n" + source, encoding="utf-8")
    path.chmod(0o700)
    return path


def _execute(script: Path, request: bytes = b"{}") -> bytes:
    return pinned.execute_pinned_verifier_once(
        executable=script.resolve(),
        expected_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),
        executable_format=pinned.VerifierExecutableFormatV1.TEST_SCRIPT,
        request_bytes=request,
        timeout_seconds=_TIMEOUT_SECONDS,
        max_address_space_bytes=_ADDRESS_SPACE_BYTES,
        max_stack_bytes=_STACK_BYTES,
    )


def _security_probe(path: Path) -> Path:
    return _write_script(
        path,
        """import errno
import json
import os
import resource
import socket

status = {}
for line in open("/proc/self/status", encoding="ascii"):
    if line.startswith("NoNewPrivs:"):
        status["no_new_privileges"] = int(line.split()[1])

socket_errnos = {}
for family in (socket.AF_INET, socket.AF_UNIX):
    try:
        network = socket.socket(family, socket.SOCK_STREAM)
    except OSError as exc:
        socket_errnos[str(family)] = exc.errno
    else:
        network.close()
        socket_errnos[str(family)] = None

inherited = []
for name in os.listdir("/proc/self/fd"):
    descriptor = int(name)
    if descriptor <= 2:
        continue
    try:
        target = os.readlink(f"/proc/self/fd/{descriptor}")
    except FileNotFoundError:
        continue
    inherited.append({"fd": descriptor, "target": target})

status.update(
    {
        "address_space": list(resource.getrlimit(resource.RLIMIT_AS)),
        "stack": list(resource.getrlimit(resource.RLIMIT_STACK)),
        "cpu": list(resource.getrlimit(resource.RLIMIT_CPU)),
        "core": list(resource.getrlimit(resource.RLIMIT_CORE)),
        "file_size": list(resource.getrlimit(resource.RLIMIT_FSIZE)),
        "open_files": list(resource.getrlimit(resource.RLIMIT_NOFILE)),
        "processes": list(resource.getrlimit(resource.RLIMIT_NPROC)),
        "socket_errnos": socket_errnos,
        "inherited": inherited,
    }
)
print(json.dumps(status, sort_keys=True, separators=(",", ":")), end="")
""",
    )


def test_governed_verifier_observes_complete_pre_exec_contract(tmp_path: Path) -> None:
    probe = _security_probe(tmp_path / "security-probe.py")
    extra_read, extra_write = os.pipe()
    os.set_inheritable(extra_read, True)
    os.set_inheritable(extra_write, True)
    try:
        observed = json.loads(_execute(probe))
    finally:
        os.close(extra_read)
        os.close(extra_write)

    assert observed["no_new_privileges"] == 1
    assert observed["address_space"] == [_ADDRESS_SPACE_BYTES] * 2
    assert observed["stack"] == [_STACK_BYTES] * 2
    assert observed["cpu"] == [_TIMEOUT_SECONDS + 1] * 2
    assert observed["core"] == [0, 0]
    assert observed["file_size"] == [pinned.MAX_VERIFIER_STDOUT_BYTES] * 2
    assert observed["open_files"] == [pinned.MAX_VERIFIER_OPEN_FILES] * 2
    assert observed["processes"] == [pinned.MAX_VERIFIER_PROCESSES] * 2
    assert observed["socket_errnos"] == {
        str(socket.AF_INET): errno.EPERM,
        str(socket.AF_UNIX): errno.EPERM,
    }
    assert len(observed["inherited"]) == 1
    assert "zenodex-ledger-risc0-verifier" in observed["inherited"][0]["target"]


def test_success_with_nonempty_stderr_rejects_canonical_output(tmp_path: Path) -> None:
    script = _write_script(
        tmp_path / "stderr.py",
        "import sys\nsys.stderr.write('uncommitted diagnostic')\nsys.stdout.write('{}')\n",
    )

    with pytest.raises(pinned.PinnedVerifierProcessError) as caught:
        _execute(script)

    assert caught.value.reason is pinned.PinnedVerifierProcessFailure.OUTPUT_INVALID


def test_launcher_setup_failure_prevents_governed_verifier_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sentinel = tmp_path / "verifier-executed.txt"
    script = _write_script(
        tmp_path / "must-not-run.py",
        f"from pathlib import Path\nPath({str(sentinel)!r}).write_text('ran')\n",
    )
    monkeypatch.setattr(
        pinned,
        "_PRE_EXEC_LAUNCHER_SOURCE",
        "import os\nos._exit(93)\n",
    )

    with pytest.raises(pinned.PinnedVerifierProcessError) as caught:
        _execute(script)

    assert caught.value.reason is pinned.PinnedVerifierProcessFailure.PROCESS_FAILED
    assert not sentinel.exists()


def test_process_source_has_no_parent_side_prlimit_or_preexec_fn() -> None:
    source = Path(pinned.__file__).read_text(encoding="utf-8")

    assert "resource.prlimit" not in source
    assert "preexec_fn" not in source
    assert "PR_SET_NO_NEW_PRIVS" in source
    assert "SECCOMP_MODE_FILTER" in source
