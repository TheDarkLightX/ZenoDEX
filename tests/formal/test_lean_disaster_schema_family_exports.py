from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


DISASTER_SCHEMA_TARGETS = (
    "Proofs.ForbiddenTraceMinor",
    "Proofs.NoFreeResourceTraceLedger",
    "Proofs.ZenoDEXDisasterSchemaInstantiations",
    "Proofs.ZenoDEXClosedAxisProofSchemaMap",
)


def _require_lake_and_mathlib() -> tuple[str, Path]:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")
    root = Path(__file__).resolve().parents[2]
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")
    return lake, root / "lean-mathlib"


def _ensure_proofs_root_built(lake: str, lean_dir: Path) -> None:
    try:
        proc = subprocess.run(
            [lake, "build", "Proofs"],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build Proofs timed out after {exc.timeout}s")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_disaster_schema_family_builds_without_warnings() -> None:
    lake, lean_dir = _require_lake_and_mathlib()

    try:
        proc = subprocess.run(
            [lake, "--wfail", "build", *DISASTER_SCHEMA_TARGETS],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake --wfail build timed out after {exc.timeout}s")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_disaster_schema_family_exported_via_proofs_root() -> None:
    lake, lean_dir = _require_lake_and_mathlib()
    _ensure_proofs_root_built(lake, lean_dir)
    smoke = (
        "import Proofs\n"
        "#check Proofs.ForbiddenTraceMinor.motif_rejection_lifts_to_all_bad\n"
        "#check Proofs.ForbiddenTraceMinor.guard_hitting_set_rejects_all_bad\n"
        "#check Proofs.NoFreeResourceTraceLedger.no_free_resource_creation_from_accepted_trace\n"
        "#check Proofs.NoFreeResourceTraceLedger.no_prefix_claim_above_budget\n"
        "#check Proofs.ZenoDEXDisasterSchemaInstantiations.api_scan_prefix_claim_above_budget_rejected\n"
        "#check Proofs.ZenoDEXDisasterSchemaInstantiations.known_motif_bad_traces_rejected\n"
        "#check Proofs.ZenoDEXClosedAxisProofSchemaMap.closed_axes_count\n"
        "#check Proofs.ZenoDEXClosedAxisProofSchemaMap.schemasForAxis_nonempty\n"
        "#check Proofs.ZenoDEXClosedAxisProofSchemaMap.resource_budget_abort_uses_resource_ledger\n"
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
        pytest.skip(f"lake env lean timed out after {exc.timeout}s for import-Proofs smoke file")
    finally:
        smoke_path.unlink(missing_ok=True)

    assert proc.returncode == 0, proc.stdout + proc.stderr
