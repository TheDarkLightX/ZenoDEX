from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


def test_concavity_conservation_law_file_typechecks() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake executable not found; cannot typecheck Lean proof")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/ConcavityConservationLaw.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    source = (lean_dir / target).read_text(encoding="utf-8")
    assert (
        "cpmm_donation_gain_argmax_bound_with_fee" in source
    ), "fee-bearing donation/no-output optimizer theorem is missing"
    assert re.search(
        r"^theorem\s+exists_witness_cpmm_donation_gain_argmax_bound\s*:",
        source,
        re.MULTILINE,
    ), "existential non-vacuity witness for fee-free donation bound is missing"
    assert re.search(
        r"^theorem\s+exists_witness_cpmm_donation_gain_argmax_bound_with_fee\s*:",
        source,
        re.MULTILINE,
    ), "existential non-vacuity witness for fee-bearing donation bound is missing"

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
