from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXBuybackPriceSafetyV1.lean"


def _pinned_lean_executable() -> Path:
    toolchain = (LEAN_PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected_version = toolchain.rsplit(":v", maxsplit=1)[-1]
    resolved = subprocess.run(
        ["elan", "which", "lean"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    )
    lean = Path(resolved.stdout.strip())
    version = subprocess.run(
        [str(lean), "--version"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert lean.is_file()
    assert f"version {expected_version}" in version
    return lean


def test_buyback_price_safety_proof_has_required_surface() -> None:
    # Arrange / Act.
    source = PROOF.read_text(encoding="utf-8")

    # Assert.
    assert "import Mathlib" not in source
    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for declaration in (
        "structure Accepted",
        "def routeSafeQuoteLimit",
        "def oracleMinimumOutput",
        "theorem accepted_implies_fresh_deep_observation",
        "theorem accepted_spend_within_derived_limit",
        "theorem accepted_meets_derived_minimum_output",
        "theorem accepted_implies_execution_envelopes",
        "theorem nonvacuity_witness_is_accepted",
    ):
        assert declaration in source
    assert "Nonclaims:" in source


def test_buyback_price_safety_proof_checks_with_pinned_lean() -> None:
    # Arrange.
    lean = _pinned_lean_executable()

    # Act / Assert.
    subprocess.run([str(lean), str(PROOF)], cwd=LEAN_PROJECT, check=True)
