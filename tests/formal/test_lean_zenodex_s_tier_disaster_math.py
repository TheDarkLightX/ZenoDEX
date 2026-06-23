from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_zenodex_s_tier_disaster_math_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXSTierDisasterMath.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
