from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_lean_exact_in_route_true_key_interpretation_packet_compiles() -> None:
    proc = subprocess.run(
        ["lake", "build", "Proofs.ZenoDEXExactInRouteTrueKeyInterpretationPacket"],
        cwd=ROOT / "lean-mathlib",
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
