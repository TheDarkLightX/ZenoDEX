from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_lean_exact_out_many_pool_concrete_recursion_branch_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXExactOutManyPoolConcreteRecursionBranch.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
