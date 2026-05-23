from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_intent_sender_boundary_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXIntentSenderBoundary.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
