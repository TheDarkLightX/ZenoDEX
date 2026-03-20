from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def test_lean_exact_out_many_pool_prefilter_support_bridge_builds() -> None:
    subprocess.run(
        ["lake", "env", "lean", "Proofs/ZenoDEXExactOutManyPoolPrefilterSupportBridge.lean"],
        cwd=ROOT / "lean-mathlib",
        check=True,
    )
