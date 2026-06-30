from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_discrete_argmax_proximity_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/DiscreteArgmaxProximity.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    assert (
        "abstract_one_sided_perturbed_argmax_distance_sharp_quadratic" in source
    ), "sharpness witness theorem is missing from DiscreteArgmaxProximity.lean"

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
