from __future__ import annotations

import sys
from pathlib import Path

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
