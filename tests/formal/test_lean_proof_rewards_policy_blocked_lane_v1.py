from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ProofRewardsPolicyBlockedLaneV1.lean"


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


def test_policy_blocked_proof_reward_proof_has_required_surface() -> None:
    source = PROOF.read_text(encoding="utf-8")

    assert "import Mathlib" not in source
    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for declaration in (
        "inductive ProofRewardCapability",
        "def allCapabilities",
        "theorem all_capabilities_length",
        "theorem all_capabilities_complete",
        "theorem every_capability_rejects_policy",
        "theorem rejection_preserves_exact_state",
        "theorem rejection_has_no_effects",
    ):
        assert declaration in source
    assert "Nonclaims:" in source


def test_policy_blocked_proof_reward_proof_checks_with_pinned_lean() -> None:
    lean = _pinned_lean_executable()
    subprocess.run([str(lean), str(PROOF)], cwd=LEAN_PROJECT, check=True)
