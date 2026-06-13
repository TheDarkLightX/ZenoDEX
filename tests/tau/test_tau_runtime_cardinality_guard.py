"""Regression tests for runtime-active Tau trace cardinality checks."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "tools" / "check_tau_runtime_cardinality.py"
SAFE_CANDIDATE = ROOT / "experiments" / "tau_frontier" / "refractory_rate_limiter_gate_candidate_v1.tau"
UNSAFE_FEEDBACK = ROOT / "experiments" / "tau_frontier" / "unsafe_output_feedback_latch_candidate_v1.tau"


def _run_checker(spec_path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), "--spec", str(spec_path), "--rows", "4"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=120,
    )


def _skip_if_only_missing_tau(proc: subprocess.CompletedProcess[str]) -> None:
    lines = [line for line in (proc.stdout + proc.stderr).splitlines() if line.strip()]
    if proc.returncode == 1 and lines and all(
        "<missing-tau>" in line and "Tau binary" in line and "not found" in line for line in lines
    ):
        pytest.skip("Tau binary not found for runtime cardinality checker")


def test_input_history_candidate_is_cardinality_safe() -> None:
    proc = _run_checker(SAFE_CANDIDATE)
    _skip_if_only_missing_tau(proc)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "FAIL" not in proc.stdout
    assert proc.stdout.count("OK\t") == 10


def test_output_feedback_latch_is_rejected_for_runtime_cardinality() -> None:
    proc = _run_checker(UNSAFE_FEEDBACK)
    _skip_if_only_missing_tau(proc)
    assert proc.returncode == 1
    output = proc.stdout + proc.stderr
    assert "FAIL" in output
    assert "output length mismatch" in output
