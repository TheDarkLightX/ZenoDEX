from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Sequence

import pytest

from src.integration import tau_runner
from src.integration.tau_runner import TauRunError


def _write_minimal_spec(tmp_path: Path) -> Path:
    spec_path = tmp_path / "gate.tau"
    spec_path.write_text(
        "\n".join(
            [
                "i1[t]:bv[32]",
                "o1[t]:bv[32]",
                "always o1 = i1.",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return spec_path


def _write_tau_bin(tmp_path: Path) -> str:
    tau_bin = tmp_path / "tau"
    tau_bin.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    tau_bin.chmod(tau_bin.stat().st_mode | 0o111)
    return str(tau_bin)


def _write_complete_outputs(input_text: str) -> None:
    for raw_path in re.findall(r'out file\("([^"]+)"\)', input_text):
        Path(raw_path).write_text("1\n", encoding="utf-8")


def _load_formal_completeness_checker():
    checker_path = Path(__file__).parents[1] / "tau" / "check_formal_completeness.py"
    module_spec = importlib.util.spec_from_file_location("check_formal_completeness", checker_path)
    assert module_spec is not None and module_spec.loader is not None
    checker = importlib.util.module_from_spec(module_spec)
    sys.modules[module_spec.name] = checker
    module_spec.loader.exec_module(checker)
    return checker


def test_run_tau_spec_steps_rejects_primary_nonzero_without_spec_mode_fallback(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)
    commands: list[list[str]] = []

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        commands.append(list(cmd))
        if "-x" in cmd:
            return 0, "o1[0] := 1\n", ""
        return 17, "", "primary Tau rejection"

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(RuntimeError, match=r"tau failed \(rc=17\): primary Tau rejection"):
        tau_runner.run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
        )

    assert commands
    assert all("-x" not in command for command in commands)


def test_run_tau_spec_steps_rejects_missing_outputs_without_spec_mode_fallback(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)
    commands: list[list[str]] = []

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        commands.append(list(cmd))
        if "-x" in cmd:
            return 0, "o1[0] := 1\n", ""
        return 0, "", ""

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(RuntimeError, match=r"tau did not create output file\(s\): o1"):
        tau_runner.run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
        )

    assert commands
    assert all("-x" not in command for command in commands)


def test_run_tau_spec_steps_rejects_rc0_ansi_error_before_complete_outputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        _write_complete_outputs(input_text)
        return 0, "\x1b[31m(\x1b[1mE\x1b[0mrror)\x1b[0m rejected\n", ""

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(RuntimeError, match="error diagnostic"):
        tau_runner.run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
        )


def test_run_tau_spec_steps_with_trace_rejects_rc0_ansi_error_before_complete_outputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        _write_complete_outputs(input_text)
        return 0, "", "(\x1b[31mE\x1b[0mrror) rejected\n"

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(TauRunError, match="error diagnostic"):
        tau_runner.run_tau_spec_steps_with_trace(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
        )


def test_spec_mode_rejects_complete_outputs_from_nonzero_tau_exit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        return 42, "o1[0] := 1\n", "fatal: spec runner rejected after emitting output"

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(TauRunError) as exc_info:
        tau_runner.run_tau_spec_steps_spec_mode(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
            retry_on_timeout=False,
        )

    assert exc_info.value.rc == 42
    assert "fatal: spec runner rejected" in str(exc_info.value)


def test_spec_mode_uses_stdout_assignments_only(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        return 0, "o1[0] := 1\n", "o1[0] := 99\n"

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    assert tau_runner.run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=[{"i1": 1}],
        timeout_s=1.0,
        retry_on_timeout=False,
    ) == {0: {"o1": 1}}


def test_spec_mode_rejects_duplicate_stdout_assignments(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        return 0, "o1[0] := 1\no1[0] := 2\n", ""

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(TauRunError, match="duplicate"):
        tau_runner.run_tau_spec_steps_spec_mode(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
            retry_on_timeout=False,
        )


def test_spec_mode_rejects_rc0_ansi_error_even_with_complete_stdout(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        return 0, "o1[0] := 1\n", "(\x1b[31mE\x1b[0mrror) rejected\n"

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    with pytest.raises(TauRunError, match="error diagnostic"):
        tau_runner.run_tau_spec_steps_spec_mode(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=[{"i1": 1}],
            timeout_s=1.0,
            retry_on_timeout=False,
        )


def test_spec_mode_selects_experimental_flag_only_when_requested(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec_path = _write_minimal_spec(tmp_path)
    tau_bin = _write_tau_bin(tmp_path)
    commands: list[list[str]] = []

    def fake_run(
        cmd: Sequence[str],
        *,
        input_text: str,
        cwd: Path,
        timeout_s: float,
        max_stdout_bytes: int,
        max_stderr_bytes: int,
    ) -> tuple[int, str, str]:
        commands.append(list(cmd))
        return 0, "o1[0] := 1\n", ""

    monkeypatch.setattr(tau_runner, "_run_subprocess_with_output_caps", fake_run)

    tau_runner.run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=[{"i1": 1}],
        timeout_s=1.0,
        retry_on_timeout=False,
    )
    tau_runner.run_tau_spec_steps_spec_mode(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=[{"i1": 1}],
        timeout_s=1.0,
        experimental=True,
        retry_on_timeout=False,
    )

    assert "-x" not in commands[0]
    assert "--experimental" not in commands[0]
    assert "-x" not in commands[1]
    assert "--experimental" in commands[1]


def test_formal_completeness_syntax_check_rejects_rc0_ansi_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker = _load_formal_completeness_checker()

    def fake_run(*args: object, **kwargs: object) -> SimpleNamespace:
        return SimpleNamespace(
            returncode=0,
            stdout="(\x1b[31mE\x1b[0mrror) rejected\n",
            stderr="",
        )

    monkeypatch.setattr(checker.subprocess, "run", fake_run)

    failures = checker.run_syntax_checks(
        "tau",
        [checker.ROOT / "tests" / "tau" / "check_formal_completeness.py"],
    )
    assert failures
