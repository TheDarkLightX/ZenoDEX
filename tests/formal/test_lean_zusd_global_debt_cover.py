from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
PROOF = LEAN_ROOT / "Proofs" / "ZUSDGlobalDebtCover.lean"


def test_zusd_global_debt_cover_lean_proof_checks() -> None:
    if shutil.which("lake") is None:
        pytest.skip("lake is not installed")
    completed = subprocess.run(
        ["lake", "env", "lean", str(PROOF.relative_to(LEAN_ROOT))],
        cwd=LEAN_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
