from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_perp_live_risk_param_monotonicity_typechecks_without_placeholders() -> None:
    lean = shutil.which("lean")
    if not lean:
        pytest.skip("lean executable missing")

    root = Path(__file__).resolve().parents[2]
    target = root / "lean-mathlib" / "Proofs" / "PerpLiveRiskParamMonotonicity.lean"
    proc = subprocess.run(
        [lean, str(target)],
        cwd=root / "lean-mathlib",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=60,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
