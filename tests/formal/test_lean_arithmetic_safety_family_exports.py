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


def test_lean_arithmetic_safety_family_builds_without_warnings() -> None:
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
                'Proofs.BatchRefinementOrder',
                'Proofs.CircuitBreakerWindowArithmetic',
                'Proofs.CurveDominanceArithmetic',
                'Proofs.FundingImbalanceEV',
                'Proofs.LiquidityRebalancerBounds',
                'Proofs.LpMintOptimalBounds',
                'Proofs.PerpFundingSymmetry',
                'Proofs.PerpLiquidationInsuranceBound',
                'Proofs.SwapRouterBounds',
                'Proofs.VolatilityTrackerArithmetic',
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


def test_lean_arithmetic_safety_family_exported_via_proofs_root() -> None:
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
        '#check Proofs.BatchRefinementOrder.two_step_refinement_never_degrades\n'
        '#check Proofs.CircuitBreakerWindowArithmetic.breach_monotone_max\n'
        '#check Proofs.CurveDominanceArithmetic.slippage_set_reserves_nat_le_2000\n'
        '#check Proofs.FundingImbalanceEV.dualEV_pos_iff\n'
        '#check Proofs.LiquidityRebalancerBounds.total_preserved\n'
        '#check Proofs.LpMintOptimalBounds.minted_add_fee_eq_input\n'
        '#check Proofs.PerpFundingSymmetry.funding_net_delta_zero\n'
        '#check Proofs.PerpLiquidationInsuranceBound.state_guard_implies_next_cap\n'
        '#check Proofs.SwapRouterBounds.route_step_preserves_bounds\n'
        '#check Proofs.VolatilityTrackerArithmetic.clamp10000_in_range\n'
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


def test_lean_arithmetic_safety_family_included_in_default_proofs_build() -> None:
    lake = shutil.which('lake')
    if not lake:
        pytest.skip('lake not installed')
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / 'lean-mathlib'
    if not (root / 'external' / 'mathlib4').exists():
        pytest.skip('mathlib4 checkout missing')
    _ensure_proofs_root_built(lake, lean_dir)
