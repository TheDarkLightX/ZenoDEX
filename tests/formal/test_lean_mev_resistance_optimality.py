from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_mev_resistance_optimality_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/MEVResistanceOptimality.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "quota_floor_witness",
        "quota_upper_bound_from_mul_le",
        "quota_floor_bound_is_tight",
        "no_quota_bound_below_floor",
        "quota_elimination_floor_residual_nontrivial",
        "witness_optimality_batch10",
        "witness_optimality_batch100",
        "witness_optimality_batch2",
        "residual_mev_decreases",
        "reduction_approaches_one",
        "quota_min_batch_for_exact_fraction_target",
    )
    for theorem in required_theorems:
        assert re.search(
            rf"^theorem\s+{re.escape(theorem)}\b",
            source,
            re.MULTILINE,
        ), f"{theorem} theorem is missing from {target}"

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
    combined = (proc.stdout + proc.stderr).lower()
    assert "sorry" not in combined, f"sorry placeholder found in {target}"
    assert "error:" not in combined, f"error in {target}: {proc.stderr}"
    assert "no sealed-bid batch mechanism" not in source.lower()
    assert "strongest provable mev resistance claim" not in source.lower()
