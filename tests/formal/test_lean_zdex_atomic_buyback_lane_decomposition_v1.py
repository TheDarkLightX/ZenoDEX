from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXAtomicBuybackTransitionV1.lean"


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


def test_lane_decomposition_proof_has_exact_port_and_refinement_surface() -> None:
    source = PROOF.read_text(encoding="utf-8")

    assert re.search(r"\b(?:sorry|admit|axiom)\b", source) is None
    for required_declaration in (
        "structure TokenomicsPost",
        "structure SpotPost",
        "structure RoutePorts",
        "def ExactlyPaired",
        "theorem route_ports_exactly_paired",
        "theorem decomposition_recomposes_atomic_post",
        "theorem paired_lane_accounting",
        "theorem accepted_transition_has_exact_lane_decomposition",
        "theorem nonvacuity_lane_decomposition",
    ):
        assert required_declaration in source
    assert "tokenomicsQuoteOut = ports.spotQuoteIn" in source
    assert "spotZdexOut = ports.tokenomicsBurnIn" in source
    assert "Nonclaims:" in source


def test_lane_decomposition_proof_checks_with_pinned_lean() -> None:
    lean = _pinned_lean_executable()

    subprocess.run([str(lean), str(PROOF)], cwd=LEAN_PROJECT, check=True)
