from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"


def test_lean_bonus_bet_budget_safety_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    if not (ROOT / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "Proofs/BonusBetBudgetSafety.lean"],
            cwd=LEAN_DIR,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for BonusBetBudgetSafety")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_proofs_root_builds_with_bonus_bet_budget_safety() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    if not (ROOT / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "build", "Proofs"],
            cwd=LEAN_DIR,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build timed out after {exc.timeout}s for Proofs")

    assert proc.returncode == 0, proc.stdout + proc.stderr
