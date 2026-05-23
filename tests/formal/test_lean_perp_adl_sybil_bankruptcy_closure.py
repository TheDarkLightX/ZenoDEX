from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_perp_adl_sybil_bankruptcy_closure_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/PerpADLSybilBankruptcyClosure.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
        timeout=120,
    )
