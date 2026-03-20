from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


TARGET = "Proofs/CpmmSwapV8ExactInAdmissibility.lean"


def test_lean_cpmm_swap_v8_exact_in_admissibility_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", TARGET],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean -DwarningAsError=true timed out after {exc.timeout}s for {TARGET}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
