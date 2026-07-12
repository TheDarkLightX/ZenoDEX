from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_perp_partial_liquidation_exact_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("Lean lake executable missing")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/PerpPartialLiquidationExact.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    proc = subprocess.run(
        [lake, "env", "lean", target],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
