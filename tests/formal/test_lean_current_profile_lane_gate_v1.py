from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "CurrentProfileLaneGateV1.lean"
REGISTRY_PROOF = LEAN_PROJECT / "Proofs" / "LaneCapabilityRegistryV1.lean"


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


def test_current_profile_lane_gate_proof_has_required_surface() -> None:
    source = PROOF.read_text(encoding="utf-8")

    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for declaration in (
        "def transition",
        "theorem every_capability_rejects",
        "theorem rejection_preserves_exact_state",
        "theorem rejection_has_no_effects",
        "theorem external_capabilities_are_disabled",
        "theorem non_external_capabilities_are_policy_blocked",
    ):
        assert declaration in source
    assert "Nonclaims:" in source


def test_current_profile_lane_gate_proof_checks_with_pinned_lean(tmp_path: Path) -> None:
    lean = _pinned_lean_executable()
    proof_cache = tmp_path / "lean"
    registry_olean = proof_cache / "Proofs" / "LaneCapabilityRegistryV1.olean"
    registry_olean.parent.mkdir(parents=True)
    subprocess.run(
        [
            str(lean),
            "-R",
            str(LEAN_PROJECT),
            "-o",
            str(registry_olean),
            str(REGISTRY_PROOF),
        ],
        cwd=LEAN_PROJECT,
        check=True,
    )
    env = dict(os.environ)
    env["LEAN_PATH"] = str(proof_cache)
    subprocess.run(
        [str(lean), "-R", str(LEAN_PROJECT), str(PROOF)],
        cwd=LEAN_PROJECT,
        check=True,
        env=env,
    )
