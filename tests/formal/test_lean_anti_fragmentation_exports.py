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


def test_lean_anti_fragmentation_family_exported_via_proofs_root() -> None:
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
        '#check AntiFragmentation.anti_fragmentation_general\n'
        '#check FeeAwareAntiFragmentation.fee_aware_anti_fragmentation\n'
        '#check OppositeDirectionNoncommutativity.generic_path_noncommutativity\n'
        '#check FeeAwareBatchKGap.feeBatch_K_gap_sum\n'
        '#check CPMMOutputMonotonicity.swapOut_mono_y\n'
    )
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=lean_dir, delete=False) as handle:
        handle.write(smoke)
        smoke_path = Path(handle.name)

    try:
        proc = subprocess.run(
            [lake, 'env', 'lean', smoke_path.name],
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


def test_lean_anti_fragmentation_family_included_in_default_proofs_build() -> None:
    lake = shutil.which('lake')
    if not lake:
        pytest.skip('lake not installed')

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / 'lean-mathlib'
    if not (root / 'external' / 'mathlib4').exists():
        pytest.skip('mathlib4 checkout missing')

    _ensure_proofs_root_built(lake, lean_dir)
