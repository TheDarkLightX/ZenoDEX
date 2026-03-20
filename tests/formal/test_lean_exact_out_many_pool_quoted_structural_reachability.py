from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_exact_out_many_pool_quoted_structural_reachability_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXExactOutManyPoolQuotedStructuralReachability.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
