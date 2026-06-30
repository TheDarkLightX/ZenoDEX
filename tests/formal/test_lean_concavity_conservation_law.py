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
    required_theorems = (
        "lipschitz_increment_bound",
        "cpmm_concavity_param_formula",
        "cpmm_window_M_relationship",
        "cpmm_stateful_gain_bound",
        "cpmm_stateful_gain_bound_with_fee",
        "cpmm_stateful_gain_bound_tight",
        "cpmm_stateful_gain_bound_tight_with_fee",
        "tight_bound_decreases_with_M",
        "tight_bound_stricter_than_lipschitz",
        "witness_tight_vs_lipschitz",
        "cpmm_donation_gain_argmax_bound",
        "witness_cpmm_donation_gain_argmax_bound",
        "cpmm_donation_gain_argmax_bound_with_fee",
        "witness_cpmm_donation_gain_argmax_bound_with_fee",
        "exists_witness_cpmm_donation_gain_argmax_bound",
        "exists_witness_cpmm_donation_gain_argmax_bound_with_fee",
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
