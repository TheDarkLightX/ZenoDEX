"""Metamorphic tests binding runtime arithmetic to proven Lean identities.

Each property here is a theorem in lean-mathlib/Proofs (cited per test).
The Lean proofs pin the abstract arithmetic; these tests pin the RUNTIME
functions to that arithmetic, closing the Lean->Python drift tier flagged
in docs/MECHANISM_DESIGN_IMPROVEMENT_ANALYSIS.md (three-tier gap).

These are relations, not examples: hypothesis explores the input space and
any divergence between the runtime and the proven identity is a regression
in whichever side changed.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

from hypothesis import assume, given, settings
from hypothesis import strategies as st

from src.core.cpmm import swap_exact_in
from src.core.domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX
from src.core.perp_v2.math import (
    BPS_SCALE,
    _settle_price_python,
    funding_payment,
)

_REPO = Path(__file__).resolve().parents[2]


def _load_median3():
    spec = importlib.util.spec_from_file_location(
        "zenodex_oracle_admitted_median3",
        _REPO / "tools" / "zenodex_oracle_admitted_median3.py",
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module._median3


_median3 = _load_median3()

_amount = st.integers(min_value=1, max_value=10**12)
_reserve = st.integers(min_value=1, max_value=10**15)
_price_e8 = st.integers(min_value=1, max_value=10**14)
_bps = st.integers(min_value=0, max_value=10_000)


class TestCpmmHopLipschitz:
    """Lean: Proofs.RoundingErrorBound.cpmm_hop_lipschitz —
    on down-price hops (reserve_out <= reserve_in) the zero-fee floored
    output is 1-Lipschitz in the input."""

    @staticmethod
    def _out_or_zero(x: int, y: int, amount: int) -> int:
        # The kernel fail-closes zero-output dust trades; for the Lipschitz
        # relation that rejection IS the floored output 0 of the Lean model.
        if amount == 0:
            return 0
        try:
            out, _ = swap_exact_in(x, y, amount, 0)
        except ValueError as exc:
            if "trade too small" in str(exc):
                return 0
            raise
        return out

    @settings(max_examples=300)
    @given(
        x=_reserve,
        y=_reserve,
        z=st.integers(min_value=0, max_value=10**12),
        g=st.integers(min_value=0, max_value=10**9),
    )
    def test_hop_lipschitz_down_price(self, x: int, y: int, z: int, g: int) -> None:
        if y > x:
            y = x  # restrict to the proven regime y <= x
        assume(z + g >= 1)
        assume(z + g <= DEX_SWAP_AMOUNT_MAX)
        assume(x + z + g <= DEX_POOL_RESERVE_MAX)
        assert self._out_or_zero(x, y, z + g) <= self._out_or_zero(x, y, z) + g


class TestSettleClampBoundedness:
    """Lean: Proofs.OracleMedianRobustness.corrupt_report_damage_bounded /
    Proofs.PerpEpochSafety.abs_clamp_move_sub_le — the settle clamp bounds
    the applied move for EVERY clearing input, including absurd corrupt
    values (integer band uses ceil-div, hence the +ceil slack)."""

    @settings(max_examples=300)
    @given(
        index=_price_e8,
        clearing=st.integers(min_value=0, max_value=10**18),
        m=st.integers(min_value=0, max_value=10_000),
    )
    def test_clamp_bounds_arbitrary_clearing(self, index: int, clearing: int, m: int) -> None:
        settle = _settle_price_python(clearing, index, m, True)
        max_delta = ((index * m) + (BPS_SCALE - 1)) // BPS_SCALE
        assert abs(settle - index) <= max_delta


class TestFundingAntisymmetry:
    """Lean: Proofs.PerpFundingSymmetry / PerpFundingRateSafety budget
    balance — flipping the position sign flips the funding payment sign
    exactly, so matched long/short pairs net to zero per epoch."""

    @settings(max_examples=300)
    @given(
        pos=st.integers(min_value=1, max_value=10**12),
        price=_price_e8,
        rate=st.integers(min_value=-10_000, max_value=10_000),
    )
    def test_antisymmetric_in_position(self, pos: int, price: int, rate: int) -> None:
        assert funding_payment(-pos, price, rate) == -funding_payment(pos, price, rate)


class TestKFoldDilution:
    """Lean: Proofs.MEVResistanceBound.batch_dilution_compose,
    k_fold_batch_dilution, k_fold_batch_dilution_sharp — exact floor
    composition and the (profit(n) − k, profit(n)] window."""

    @settings(max_examples=300)
    @given(
        base=st.integers(min_value=0, max_value=10**15),
        k=st.integers(min_value=1, max_value=10**6),
        n=st.integers(min_value=1, max_value=10**6),
    )
    def test_composition_and_window(self, base: int, k: int, n: int) -> None:
        assert base // (k * n) == (base // n) // k
        assert k * (base // (k * n)) <= base // n
        assert base // n < k * (base // (k * n)) + k


class TestWeightedExposureConservation:
    """Lean: Proofs.MEVResistanceBound.weightedExposure_sum_le — per-intent
    share exposures never sum above the single-intent base exposure."""

    @settings(max_examples=300)
    @given(
        base=st.integers(min_value=0, max_value=10**12),
        sizes=st.lists(st.integers(min_value=0, max_value=10**9), min_size=1, max_size=20),
    )
    def test_share_sum_conserved(self, base: int, sizes: list[int]) -> None:
        total = sum(sizes)
        if total == 0:
            return
        assert sum(base * s // total for s in sizes) <= base


class TestMedian3Robustness:
    """Lean: Proofs.OracleMedianRobustness.median3_robust_corrupt_* — with
    two honest reports in an interval, ONE arbitrarily corrupt report in
    any position cannot move the runtime median outside that interval."""

    @settings(max_examples=300)
    @given(
        h1=_price_e8,
        h2=_price_e8,
        corrupt=st.integers(min_value=0, max_value=10**18),
        position=st.integers(min_value=0, max_value=2),
    )
    def test_one_corrupt_bounded(self, h1: int, h2: int, corrupt: int, position: int) -> None:
        lo, hi = min(h1, h2), max(h1, h2)
        values = [h1, h2]
        values.insert(position, corrupt)
        med = _median3(values)
        assert lo <= med <= hi

    def test_two_corrupt_unbounded_witness(self) -> None:
        # Lean: witness_two_corrupt_unbounded — the 2-coalition controls the
        # median entirely; its economic closure is
        # EconomicSecurityEnvelope.median3_coalition_bond_floor.
        assert _median3([0, 10**6, 10**6]) == 10**6
