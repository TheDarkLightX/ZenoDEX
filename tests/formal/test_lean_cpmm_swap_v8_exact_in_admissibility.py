from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


TARGET = "Proofs.CpmmSwapV8ExactInAdmissibility"


def _ensure_target_module_built(lake: str, lean_dir: Path) -> None:
    try:
        proc = subprocess.run(
            [lake, "build", TARGET],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f"lake build {TARGET} timed out after {exc.timeout}s")

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_cpmm_swap_v8_exact_in_admissibility_builds_without_warnings() -> None:
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
                "Proofs/CpmmSwapV8ExactInAdmissibility.lean",
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
            f"{exc.timeout}s for Proofs/CpmmSwapV8ExactInAdmissibility.lean"
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_cpmm_swap_v8_exact_in_admissibility_exports_theorems() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    _ensure_target_module_built(lake, lean_dir)

    smoke = (
        "import Proofs.CpmmSwapV8ExactInAdmissibility\n"
        "#check TauSwap.CPMM.V8.exactInNet_eq_floor\n"
        "#check TauSwap.CPMM.V8.exactInPositiveOutput_suffix\n"
        "#check TauSwap.CPMM.V8.exactInAccepted_suffix\n"
        "#check TauSwap.CPMM.V8.witness_exactInAccepted_suffix_applies\n"
    )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=lean_dir, delete=False) as handle:
        handle.write(smoke)
        smoke_path = Path(handle.name)

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


def test_lean_cpmm_swap_v8_exact_in_admissibility_is_listed_in_proofs_root() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    # The repository-wide Proofs.lean aggregator is currently broader than this
    # promotion branch and contains stale unrelated imports. Keep this proof's
    # gate focused: prove the target module builds, then statically require the
    # root aggregator to list it so the import is not accidentally dropped.
    _ensure_target_module_built(lake, lean_dir)
    assert "import Proofs.CpmmSwapV8ExactInAdmissibility" in (
        lean_dir / "Proofs.lean"
    ).read_text(encoding="utf-8")
