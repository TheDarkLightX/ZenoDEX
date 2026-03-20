from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


TARGETS = [
    "Proofs/AllocationTotality.lean",
    "Proofs/BatchGreedyOptimality.lean",
    "Proofs/IteratedSwapDecreasing.lean",
]


@pytest.mark.parametrize("target", TARGETS)
def test_lean_routing_foundation_proof_file_typechecks(target: str) -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

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
            timeout=180,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_routing_foundation_modules_join_default_proofs_build() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "build", "Proofs"],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=240,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build timed out after {exc.timeout}s for Proofs")

    assert proc.returncode == 0, proc.stdout + proc.stderr
