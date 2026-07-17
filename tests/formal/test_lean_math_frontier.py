from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
TARGETS = [
    "Proofs.FeeAwareRoutingNonconcavity",
    "Proofs.RoutingAffineEnvelopeCertificate",
]


@pytest.mark.parametrize("target", TARGETS)
def test_math_frontier_module_builds_without_warnings(target: str) -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")
    if not (ROOT / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    proc = subprocess.run(
        [lake, "--wfail", "build", target],
        cwd=LEAN_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
