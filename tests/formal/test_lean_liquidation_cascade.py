from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "internal" / "proofs" / "ZenoProofLiquidationCascade.lean"
MATHLIB = Path("/home/trevormoc/deps/mathlib4")


def test_liquidation_cascade_lean_compiles() -> None:
    if not MATHLIB.exists():
        import pytest

        pytest.skip("mathlib4 not available at /home/trevormoc/deps/mathlib4")
    if shutil.which("lake") is None:
        import pytest

        pytest.skip("lake not on PATH")
    subprocess.run(
        ["lake", "env", "lean", str(PROOF)],
        cwd=str(MATHLIB),
        check=True,
        timeout=300,
        capture_output=True,
        text=True,
    )
