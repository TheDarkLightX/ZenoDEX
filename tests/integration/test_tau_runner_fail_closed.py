from __future__ import annotations

from pathlib import Path
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
