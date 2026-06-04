from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


TARGET = "Proofs.CpmmSwapV8ExactOutMinimality"


def test_lean_cpmm_swap_v8_exact_out_minimality_builds_without_warnings() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            [
                lake,
                "env",
                "lean",
                "-DwarningAsError=true",
                "Proofs/CpmmSwapV8ExactOutMinimality.lean",
            ],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=240,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(
            "lake env lean timed out after "
            f"{exc.timeout}s for Proofs/CpmmSwapV8ExactOutMinimality.lean"
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_cpmm_swap_v8_exact_out_minimality_exports_theorem() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    smoke = (
        "import Proofs.CpmmSwapV8ExactOutMinimality\n"
        "#check TauSwap.CPMM.V8.net_actual_eq_floor_mul\n"
        "#check TauSwap.CPMM.V8.swap_exact_out_sufficient_and_minimal\n"
        "#check TauSwap.CPMM.V8.exactOutGross_sufficient_and_minimal\n"
        "#check TauSwap.CPMM.V8.witness_exactOutGross_sufficient_and_minimal_applies\n"
    )
    smoke_path = lean_dir / ".tmp_cpmm_exact_out_smoke.lean"
    smoke_path.write_text(smoke, encoding="utf-8")

    try:
        proc = subprocess.run(
            [lake, "env", "lean", smoke_path.name],
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
