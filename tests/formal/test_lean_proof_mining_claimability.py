from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_proof_mining_claimability_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXProofMiningClaimability.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
