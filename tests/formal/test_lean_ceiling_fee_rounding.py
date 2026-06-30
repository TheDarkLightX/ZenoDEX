from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_ceiling_fee_rounding_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/CeilingFeeRounding.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "cpmm_output_lipschitz_wrt_net",
        "cpmm_prod_floor_error_bound_directed",
        "split_prod_floor_error_bound",
        "cpmm_prod_discrete_argmax_proximity",
        "cpmm_prod_certified_anchor_argmax_distance",
        "cpmm_prod_oracle_argmax_distance",
        "cpmm_prod_anchor_lipschitz_argmax_distance",
        "witness_per_pool_error_bound",
        "abs_sub_le_max",
        "abs_add_le_max_of_mul_nonpos",
        "cpmmOutputCont_monotone",
        "split_lipschitz_coupled",
        "witness_coupled_lipschitz",
    )
    for theorem in required_theorems:
        assert re.search(
            rf"^(?:theorem|lemma)\s+{re.escape(theorem)}\b",
            source,
            re.MULTILINE,
        ), f"{theorem} theorem/lemma is missing from {target}"

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
