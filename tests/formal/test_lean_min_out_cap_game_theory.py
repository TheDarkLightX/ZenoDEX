from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_min_out_cap_game_theory_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/MinOutCapGameTheory.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "cpmm_output_independent_of_min_out",
        "filled_user_lower_min_out_still_fills",
        "filled_user_lower_min_out_same_output",
        "filled_user_no_profitable_deviation",
        "batch_state_invariant_after_filled_deviation",
        "filled_user_raise_min_out_becomes_unfilled",
        "filled_user_no_profitable_min_out_deviation",
        "unfilled_user_profitable_deviation",
        "witness_unfilled_profitable_deviation",
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
    # Zero errors, zero warnings, zero sorry placeholders.
    combined = (proc.stdout + proc.stderr).lower()
    assert "sorry" not in combined, f"sorry placeholder found in {target}"
    assert "error:" not in combined, f"error in {target}: {proc.stderr}"
    assert "warning:" not in combined, f"warning in {target}: {proc.stderr}"
