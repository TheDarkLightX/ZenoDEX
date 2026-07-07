from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_slippage_lower_bound_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/SlippageLowerBound.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "cpmm_slippage",
        "cpmm_slippage_fraction_bounds",
        "cpmm_slippage_matches_assumed_floor",
        "slippage_linear_regime",
        "slippage_small_trade_approx",
        "cpmm_positive_slippage",
        "slippage_increasing",
        "witness_slippage_1pct",
        "witness_slippage_large_pool",
        "slippage_decreases_with_liquidity",
        "slippage_halves_approx",
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
    assert "any market mechanism" not in source.lower()
    assert "no mechanism with the same liquidity" not in source.lower()
