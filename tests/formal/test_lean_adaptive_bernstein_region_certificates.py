from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_lean_adaptive_bernstein_region_certificates_typecheck() -> None:
    lake = shutil.which("lake")
    if not lake:
        return

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = "Proofs/AdaptiveBernsteinRegionCertificates.lean"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    proc = subprocess.run(
        [lake, "env", "lean", target],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
