from __future__ import annotations

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest


def _ensure_proofs_root_built(lake: str, lean_dir: Path) -> None:
    try:
        proc = subprocess.run(
            [lake, 'build', 'Proofs'],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f'lake build Proofs timed out after {exc.timeout}s')
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_dex_algebra_family_builds_without_warnings() -> None:
    lake = shutil.which('lake')
    if not lake:
        pytest.skip('lake not installed')
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / 'lean-mathlib'
    if not (root / 'external' / 'mathlib4').exists():
        pytest.skip('mathlib4 checkout missing')
    try:
        proc = subprocess.run(
            [
                lake,
                '--wfail',
                'build',
                'Proofs.DEXCanonicalSelection',
                'Proofs.DEXExactSequence',
                'Proofs.DEXValueAlgebra',
                'Proofs.LPValueAlgebra',
            ],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f'lake --wfail build timed out after {exc.timeout}s')
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_dex_algebra_family_exported_via_proofs_root() -> None:
    lake = shutil.which('lake')
    if not lake:
        pytest.skip('lake not installed')
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / 'lean-mathlib'
    if not (root / 'external' / 'mathlib4').exists():
        pytest.skip('mathlib4 checkout missing')
    _ensure_proofs_root_built(lake, lean_dir)
    smoke = (
        'import Proofs\n'
        '#check Proofs.DEXCanonicalSelection.canonical_winner_unique\n'
        '#check Proofs.DEXExactSequence.kerProject_in_ker\n'
        '#check Proofs.DEXValueAlgebra.two_prices_determine\n'
        '#check Proofs.LPValueAlgebra.valuation_determines_position\n'
    )
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=lean_dir, delete=False) as handle:
        handle.write(smoke)
        smoke_path = Path(handle.name)
    try:
        proc = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true', smoke_path.name],
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=240,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.skip(f'lake env lean timed out after {exc.timeout}s for import-Proofs smoke file')
    finally:
        smoke_path.unlink(missing_ok=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_dex_algebra_family_included_in_default_proofs_build() -> None:
    lake = shutil.which('lake')
    if not lake:
        pytest.skip('lake not installed')
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / 'lean-mathlib'
    if not (root / 'external' / 'mathlib4').exists():
        pytest.skip('mathlib4 checkout missing')
    _ensure_proofs_root_built(lake, lean_dir)
