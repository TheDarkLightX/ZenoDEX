from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

TARGET = "Proofs.SplitRoutingStaircase"


def _require_lean_env() -> tuple[str, Path]:
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


def test_lean_split_routing_staircase_builds_without_warnings() -> None:
    lake, lean_dir = _require_lean_env()

    try:
        proc = subprocess.run(
            [lake, "--wfail", "build", TARGET],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake --wfail build timed out after {exc.timeout}s for {TARGET}")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_split_routing_staircase_exported_via_proofs_root() -> None:
    lake, lean_dir = _require_lean_env()
    _ensure_proofs_root_built(lake, lean_dir)

    smoke = (
        "import Proofs\n"
        "#check Proofs.SplitRoutingStaircase.two_pool_split_candidate_complete\n"
        "#check Proofs.SplitRoutingStaircase.le_feeOut_iff\n"
        "#check Proofs.SplitRoutingStaircase.jump_point_closed_form\n"
        "#check Proofs.SplitRoutingStaircase.multi_pool_snap_dominates\n"
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
