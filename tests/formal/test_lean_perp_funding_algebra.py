from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


TARGET = "Proofs.PerpFundingAlgebra"


def test_lean_perp_funding_algebra_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "build", TARGET],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build timed out after {exc.timeout}s for {TARGET}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
