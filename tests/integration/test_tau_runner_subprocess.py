from __future__ import annotations

import sys
from pathlib import Path

from src.integration import tau_runner as tau_runner_mod
from src.integration.tau_runner import _run_subprocess_with_output_caps


def test_run_subprocess_with_output_caps_success(tmp_path: Path) -> None:
    rc, out, err = _run_subprocess_with_output_caps(
        [sys.executable, "-c", "import sys; data=sys.stdin.read(); sys.stdout.write(data); sys.stderr.write('e')"],
        input_text="hello",
        cwd=tmp_path,
        timeout_s=1.0,
        max_stdout_bytes=1024,
        max_stderr_bytes=1024,
    )
    assert rc == 0
    assert out == "hello"
    assert err == "e"


def test_run_subprocess_with_output_caps_times_out(tmp_path: Path) -> None:
    rc, out, err = _run_subprocess_with_output_caps(
        [sys.executable, "-c", "import time; time.sleep(2)"],
        input_text="",
        cwd=tmp_path,
        timeout_s=0.1,
        max_stdout_bytes=1024,
        max_stderr_bytes=1024,
    )
    assert rc == -1
    assert out == ""
    assert err == "tau timed out"


def test_run_subprocess_with_output_caps_enforces_stdout_cap(tmp_path: Path) -> None:
    rc, out, err = _run_subprocess_with_output_caps(
        [sys.executable, "-c", "print('x' * 5000)"],
        input_text="",
        cwd=tmp_path,
        timeout_s=1.0,
        max_stdout_bytes=100,
        max_stderr_bytes=1024,
    )
    assert rc == -1
    assert out.startswith("x")
    assert len(out) == 100
    assert err == "tau stdout too large"


def test_run_subprocess_with_output_caps_enforces_stderr_cap(tmp_path: Path) -> None:
    rc, out, err = _run_subprocess_with_output_caps(
        [sys.executable, "-c", "import sys; sys.stderr.write('x' * 5000)"],
        input_text="",
        cwd=tmp_path,
        timeout_s=1.0,
        max_stdout_bytes=1024,
        max_stderr_bytes=100,
    )
    assert rc == -1
    assert out == ""
    assert err == "tau stderr too large"


def test_run_subprocess_with_output_caps_rejects_zero_byte_stdin_progress(monkeypatch, tmp_path: Path) -> None:
    class _Pipe:
        def __init__(self, name: str) -> None:
            self.name = name

        def fileno(self) -> int:
            return {"stdin": 10, "stdout": 11, "stderr": 12}[self.name]

        def write(self, _data: memoryview) -> int:
            return 0

        def read(self, _size: int) -> bytes:
            return b""

        def close(self) -> None:
            return None

    class _Proc:
        def __init__(self) -> None:
            self.pid = 12345
            self.stdin = _Pipe("stdin")
            self.stdout = _Pipe("stdout")
            self.stderr = _Pipe("stderr")
            self.returncode: int | None = None

        def poll(self) -> int | None:
            return self.returncode

        def wait(self, timeout: float | None = None) -> int:
            del timeout
            if self.returncode is None:
                self.returncode = -9
            return self.returncode

        def kill(self) -> None:
            self.returncode = -9

    proc = _Proc()
    monkeypatch.setattr(tau_runner_mod.subprocess, "Popen", lambda *args, **kwargs: proc)
    monkeypatch.setattr(tau_runner_mod.os, "set_blocking", lambda *args, **kwargs: None)
    monkeypatch.setattr(
        tau_runner_mod.select,
        "select",
        lambda r, w, x, timeout: ([], list(w), []),
    )
    monkeypatch.setattr(tau_runner_mod.os, "killpg", lambda *args, **kwargs: (_ for _ in ()).throw(ProcessLookupError()))

    rc, out, err = _run_subprocess_with_output_caps(
        ["fake-tau"],
        input_text="abc",
        cwd=tmp_path,
        timeout_s=1.0,
        max_stdout_bytes=1024,
        max_stderr_bytes=1024,
    )
    assert (rc, out, err) == (-1, "", "tau stdin made no progress")
