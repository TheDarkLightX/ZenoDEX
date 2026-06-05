from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


def _lean_dir() -> Path:
    return Path(__file__).resolve().parents[2] / "lean-mathlib"


def _require_lake() -> str:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")
    if not (_lean_dir().parent / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")
    return lake


def test_settlement_conservation_live_proof_builds() -> None:
    lake = _require_lake()
    proc = subprocess.run(
        [lake, "build", "Proofs.SettlementConservationLive"],
        cwd=_lean_dir(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_settlement_conservation_live_exports_and_axioms() -> None:
    lake = _require_lake()
    smoke = (
        "import Proofs.SettlementConservationLive\n"
        "#check Proofs.SettlementConservationLive.assetMove_totalDelta_zero\n"
        "#check Proofs.SettlementConservationLive.applyMoves_preserves_total\n"
        "#check Proofs.SettlementConservationLive.list_totalDelta_sum_zero\n"
        "#check Proofs.SettlementConservationLive.witness_mixed_live_batch\n"
        "#print axioms Proofs.SettlementConservationLive.applyMoves_preserves_total\n"
    )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=_lean_dir(), delete=False) as handle:
        handle.write(smoke)
        smoke_path = Path(handle.name)
    try:
        proc = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", smoke_path.name],
            cwd=_lean_dir(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
        )
    finally:
        smoke_path.unlink(missing_ok=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "sorryAx" not in proc.stdout, proc.stdout + proc.stderr
    assert "Classical.choice" not in proc.stdout, proc.stdout + proc.stderr
    assert "depends on axioms:" in proc.stdout, proc.stdout + proc.stderr
