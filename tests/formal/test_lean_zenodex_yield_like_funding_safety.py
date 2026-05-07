from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_zenodex_yield_like_funding_safety_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXYieldLikeFundingSafety.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
