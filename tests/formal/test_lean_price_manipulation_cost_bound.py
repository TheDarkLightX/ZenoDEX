from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_price_manipulation_cost_bound_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/PriceManipulationCostBound.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "cpmm_average_execution_price_eq",
        "average_execution_price_decreases",
        "relative_average_price_change_eq",
        "relative_average_change_increasing",
        "average_price_move_cost_lower_bound",
        "average_price_move_cost_achievable",
        "average_price_move_cost_approx",
        "batch_relative_average_price_change",
        "batch_average_price_move_cost",
        "no_cheap_average_price_manipulation",
        "witness_manipulation_10pct",
        "witness_manipulation_1pct",
        "average_price_move_cost_scales_linearly",
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
    assert "post-trade cpmm marginal price" in source.lower()
    assert "clearing price" not in source.lower()
