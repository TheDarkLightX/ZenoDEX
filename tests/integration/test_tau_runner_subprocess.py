from __future__ import annotations

import sys
from pathlib import Path

import pytest

import src.integration.tau_runner as tau_runner
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


def test_run_subprocess_with_output_caps_pipe_cleanup_fault_boundary(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    class _NoPipeProc:
        stdin = None
        stdout = None
        stderr = None
        returncode = None
        pid = 123

        def __init__(self, kill_exc: BaseException) -> None:
            self._kill_exc = kill_exc

        def kill(self) -> None:
            raise self._kill_exc

        def wait(self, timeout: float | None = None) -> int:
            del timeout
            return 0

    monkeypatch.setattr(
        tau_runner.subprocess,
        "Popen",
        lambda *args, **kwargs: _NoPipeProc(OSError("already gone")),
    )
    with pytest.raises(RuntimeError, match="pipes unavailable"):
        _run_subprocess_with_output_caps(
            [sys.executable, "-c", "print('ok')"],
            input_text="",
            cwd=tmp_path,
            timeout_s=1.0,
            max_stdout_bytes=1024,
            max_stderr_bytes=1024,
        )

    monkeypatch.setattr(
        tau_runner.subprocess,
        "Popen",
        lambda *args, **kwargs: _NoPipeProc(RuntimeError("tau cleanup bug")),
    )
    with pytest.raises(RuntimeError, match="tau cleanup bug"):
        _run_subprocess_with_output_caps(
            [sys.executable, "-c", "print('ok')"],
            input_text="",
            cwd=tmp_path,
            timeout_s=1.0,
            max_stdout_bytes=1024,
            max_stderr_bytes=1024,
        )


def test_try_import_tau_python_binding_treats_import_error_as_unavailable(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setattr(tau_runner, "_find_tau_python_binding_dirs", lambda _project_root: [tmp_path])
    monkeypatch.setattr(
        tau_runner.importlib,
        "import_module",
        lambda _name: (_ for _ in ()).throw(ImportError("tau binding unavailable")),
    )

    assert tau_runner._try_import_tau_python_binding(project_root=tmp_path) is None


def test_try_import_tau_python_binding_does_not_hide_unexpected_import_fault(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setattr(tau_runner, "_find_tau_python_binding_dirs", lambda _project_root: [tmp_path])
    monkeypatch.setattr(
        tau_runner.importlib,
        "import_module",
        lambda _name: (_ for _ in ()).throw(RuntimeError("tau binding import bug")),
    )

    with pytest.raises(RuntimeError, match="tau binding import bug"):
        tau_runner._try_import_tau_python_binding(project_root=tmp_path)
