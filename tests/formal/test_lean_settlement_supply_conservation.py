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


def test_settlement_supply_conservation_proof_builds() -> None:
    lake = _require_lake()
    proc = subprocess.run(
        [lake, "build", "Proofs.SettlementSupplyConservation"],
        cwd=_lean_dir(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_settlement_supply_conservation_exports_and_axioms() -> None:
    lake = _require_lake()
    smoke = (
        "import Proofs.SettlementSupplyConservation\n"
        "#check Proofs.SettlementSupplyConservation.supply_applyDeltas\n"
        "#check Proofs.SettlementSupplyConservation.accepted_preserves_supply\n"
        "#check Proofs.SettlementSupplyConservation.supply_changed_implies_not_accepted\n"
        "#check Proofs.SettlementSupplyConservation.witness_accepted_preserves_noncanceling\n"
        "#check Proofs.SettlementSupplyConservation.witness_unbalanced_creates_supply\n"
        "#print axioms Proofs.SettlementSupplyConservation.accepted_preserves_supply\n"
        "#print axioms Proofs.SettlementSupplyConservation.witness_accepted_preserves_noncanceling\n"
        "#print axioms Proofs.SettlementSupplyConservation.witness_unbalanced_creates_supply\n"
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
    output = proc.stdout + proc.stderr
    assert proc.returncode == 0, output
    assert "sorryAx" not in output, output
    assert "Lean.trustCompiler" not in output, output
    assert "Lean.ofReduceBool" not in output, output
    assert "depends on axioms:" in output, output
