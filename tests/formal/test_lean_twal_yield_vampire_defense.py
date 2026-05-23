from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_twal_yield_vampire_defense_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/TWALYieldVampireDefense.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
        timeout=120,
    )
