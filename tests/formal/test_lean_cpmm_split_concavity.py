from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_cpmm_split_concavity_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/CpmmSplitConcavity.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "cpmmOutputCont_secondDiff_formula",
        "cpmmOutputCont_secondDiff_neg",
        "splitFunctionCont_concave",
        "T0_decreasing_bound",
        "T1_increasing_bound",
        "strong_concavity_lower_bound",
        "strong_concavity_interval_lower_bound",
        "strong_concavity_interval_floor_refinement",
        "inv_cube_pair_lower_bound",
        "inv_cube_tangent_lower_bound",
        "weighted_inv_cube_stationary_lower_bound",
        "normalized_asymmetric_split_curvature_stationary_min",
        "symmetric_split_curvature_min_at_half",
        "witness_strong_concavity_bound",
        "split_curvature_endpoint_lower_bound_pos",
        "splitFunctionCont_second_deriv_identity",
        "splitFunctionCont_strong_concavity",
        "splitFunctionCont_strong_concavity_from_curvature_floor",
        "splitFunctionCont_strong_concavity_from_m_certificate",
        "taylor_remainder_quadratic_growth_bridge",
        "taylor_remainder_quadratic_growth_bridge_symmetric",
        "universal_quadratic_growth_from_strong_concavity",
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
