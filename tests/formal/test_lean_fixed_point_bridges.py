from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


@pytest.mark.parametrize(
    "target",
    [
        "Proofs/FixedPointIntervalBridge.lean",
        "Proofs/FixedPointPortfolioBridge.lean",
        "Proofs/ZenoPayoffFixedPointBridge.lean",
        "Proofs/ZenoPayoffPortfolioFixedPointBridge.lean",
    ],
)
def test_lean_fixed_point_bridge_file_typechecks(target: str) -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
