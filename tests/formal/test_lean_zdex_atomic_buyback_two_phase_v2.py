from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXAtomicBuybackTwoPhaseV2.lean"


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


def test_two_phase_proof_has_the_required_surface_and_claim_ceiling() -> None:
    # Arrange
    source = PROOF.read_text(encoding="utf-8")

    # Act / Assert
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    for declaration in (
        "def phaseAFirstReject",
        "def phaseA",
        "def phaseBFirstReject",
        "def phaseB",
        "theorem phase_a_prepared_uses_committed_fee",
        "theorem phase_a_is_non_applicable",
        "theorem rejected_phase_b_is_exact_noop",
        "theorem accepted_two_phase_accounting",
        "theorem accepted_fee_conservation",
        "theorem duplicate_route_rejects",
        "theorem nonvacuity_accepts",
    ):
        assert declaration in source
    assert "canonical-byte encoding" in source
    assert "Python/Rust refinement" in source
    assert "RISC0 validity" in source
    assert "production authority" in source


def test_two_phase_proof_checks_with_pinned_lean() -> None:
    # Arrange
    lean = _pinned_lean_executable()

    # Act / Assert
    subprocess.run([str(lean), str(PROOF)], cwd=LEAN_PROJECT, check=True)
