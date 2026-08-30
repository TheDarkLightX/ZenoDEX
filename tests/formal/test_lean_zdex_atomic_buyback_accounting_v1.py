from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXAtomicBuybackAccountingV1.lean"
TRANSITION_PROOF = LEAN_PROJECT / "Proofs" / "ZDEXAtomicBuybackTransitionV1.lean"


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


def test_atomic_buyback_accounting_proof_has_required_surface() -> None:
    source = PROOF.read_text(encoding="utf-8")

    assert "import Init.Omega" in source
    assert "import Mathlib" not in source
    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for required_declaration in (
        "def deriveFeeCommand",
        "theorem derived_fee_command_equals_committed_ingress",
        "structure AtomicBuybackAssumptions",
        "theorem quote_conservation",
        "theorem spot_zdex_reduction_by_exact_burn",
        "theorem live_supply_reduction_by_exact_burn",
        "theorem live_supply_post_eq_pre_sub_burn",
        "theorem atomic_equations_compose",
        "theorem nonvacuity_witness_satisfies_assumptions",
    ):
        assert required_declaration in source
    assert "Nonclaims:" in source


def test_atomic_buyback_accounting_proof_checks_with_pinned_lean() -> None:
    lean = _pinned_lean_executable()

    subprocess.run(
        [str(lean), str(PROOF)],
        cwd=LEAN_PROJECT,
        check=True,
    )


def test_atomic_buyback_transition_proof_retains_coordination_obligation() -> None:
    source = TRANSITION_PROOF.read_text(encoding="utf-8")

    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for required_declaration in (
        "def transition",
        "theorem transition_is_total",
        "theorem rejected_is_exact_noop",
        "theorem duplicate_occurrence_rejects_replay",
        "theorem accepted_safety",
        "theorem nonvacuity_accepts",
    ):
        assert required_declaration in source
    assert "effects.burnReceiptClosed = true" in source
    assert "effects.laneCoordinationPending = true" in source
    assert "Nonclaims:" in source


def test_atomic_buyback_transition_proof_checks_with_pinned_lean() -> None:
    lean = _pinned_lean_executable()

    subprocess.run(
        [str(lean), str(TRANSITION_PROOF)],
        cwd=LEAN_PROJECT,
        check=True,
    )
