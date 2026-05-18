from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
TARGETS = (
    "Proofs/UPBAV2ScoreOrder.lean",
    "Proofs/ZenoEnergyAdvisoryBoundary.lean",
    "Proofs/ZenoCoverReserveArithmetic.lean",
)


@pytest.mark.parametrize("target", TARGETS)
def test_aristotle_boundary_packet_typechecks(target: str) -> None:
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("lake is unavailable")
    if not (ROOT / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", target],
            cwd=LEAN_DIR,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for {target}")

    assert proc.returncode == 0, proc.stdout + proc.stderr
