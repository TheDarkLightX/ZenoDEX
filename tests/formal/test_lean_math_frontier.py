from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"


def _compile(relative_path: str) -> None:
    subprocess.run(
        ["lake", "env", "lean", relative_path],
        cwd=LEAN_ROOT,
        check=True,
    )


def test_fee_aware_routing_nonconcavity_builds() -> None:
    _compile("Proofs/FeeAwareRoutingNonconcavity.lean")


def test_routing_affine_envelope_certificate_builds() -> None:
    _compile("Proofs/RoutingAffineEnvelopeCertificate.lean")
