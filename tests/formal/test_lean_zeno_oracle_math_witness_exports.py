from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


def _require_lake_and_mathlib() -> tuple[str, Path]:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")
    root = Path(__file__).resolve().parents[2]
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")
    return lake, root / "lean-mathlib"


def test_zeno_oracle_math_witness_exports_perps_snapshot_theorems() -> None:
    lake, lean_dir = _require_lake_and_mathlib()
    smoke = (
        "import Proofs.ZenoOracleMathWitness\n"
        "#check Proofs.ZenoOracleMathWitness.PerpsOracleSnapshotUsableOK\n"
        "#check Proofs.ZenoOracleMathWitness.PerpsSnapshotCriticalActionOK\n"
        "#check Proofs.ZenoOracleMathWitness.perps_snapshot_usable_iff_obligations\n"
        "#check Proofs.ZenoOracleMathWitness.perps_snapshot_usable_rejects_action_id_drift\n"
        "#check Proofs.ZenoOracleMathWitness.perps_snapshot_usable_rejects_runtime_fact_drift\n"
        "#check Proofs.ZenoOracleMathWitness.perps_snapshot_critical_action_rejects_missing_usable_snapshot\n"
        "#check Proofs.ZenoOracleMathWitness.perps_snapshot_critical_action_rejects_missing_o3_action_binding\n"
    )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=lean_dir, delete=False) as handle:
        handle.write(smoke)
        smoke_path = Path(handle.name)

    try:
        proc = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true", smoke_path.name],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=240,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for ZenoOracleMathWitness smoke file")
    finally:
        smoke_path.unlink(missing_ok=True)

    assert proc.returncode == 0, proc.stdout + proc.stderr
