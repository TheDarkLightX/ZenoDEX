from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_adaptive_bernstein_region_certificates_typecheck() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/AdaptiveBernsteinRegionCertificates.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    required_theorems = (
        "bernsteinCombination_deCasteljauStep",
        "bernstein_choose_moment",
        "powerToBernsteinCoefficient_eq_lowerRange",
        "powerBasisCombination_eq_bernsteinCombination",
        "unitIntervalMul_ratio_right_eq_affine",
        "leftSubdivisionCoefficient_eq_lowerRange",
        "rightSubdivisionCoefficient_eq_suffixRange",
        "bernsteinCombination_eq_deCasteljauValue",
        "leftSubdivisionCoefficient_eq_deCasteljauValue",
        "rightSubdivisionCoefficient_eq_deCasteljauValue",
        "bernsteinCombination_leftSubdivisionCoefficients",
        "bernsteinCombination_rightSubdivisionCoefficients",
        "leftSubdivisionCoefficients_nonneg",
        "rightSubdivisionCoefficients_nonneg",
        "bernsteinCombination_intervalSubdivisionCoefficients",
        "bernsteinCombination_restrictedSubdivisionCoefficients",
        "restrictedSubdivisionCoefficients_nonneg",
        "powerBasisCombination_eq_deCasteljauValue",
        "powerBasisCombination_mul_eq_leftSubdivision",
        "powerBasisCombination_rightAffine_eq_rightSubdivision",
        "powerBasisCombination_affine_eq_restrictedSubdivision",
        "deCasteljauStep_nonneg",
        "representedTarget_eq_deCasteljauValue",
        "bernsteinCombination_nonneg",
        "representedTarget_nonneg",
        "adaptiveCover_nonneg",
    )
    for theorem in required_theorems:
        assert re.search(
            rf"^theorem\s+{re.escape(theorem)}\b",
            source,
            re.MULTILINE,
        ), f"{theorem} theorem is missing from {target}"

    proc = subprocess.run(
        [lake, "env", "lean", target],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    combined = (proc.stdout + proc.stderr).lower()
    assert "sorry" not in combined, f"sorry placeholder found in {target}"
    assert "error:" not in combined, f"error in {target}: {proc.stderr}"
    assert "warning:" not in combined, f"warning in {target}: {proc.stderr}"
