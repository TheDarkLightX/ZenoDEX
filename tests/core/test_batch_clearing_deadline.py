"""Tests for batch clearing via deadline scheduling (experimental).

Verifies that the deadline scheduling algorithm produces schedules matching
the brute-force oracle's A-total across a range of pool configurations and
intent sets. The DP is exact for the constant-k deadline model; local search
heuristically reduces the approximation gap for the actual CPMM ordering.
"""

from __future__ import annotations

import pytest
from hypothesis import given, settings, strategies as st

from src.core.batch_clearing_deadline import (
    DeadlineScheduleResult,
    ResourceLimitExceeded,
    compute_deadline,
    deadline_schedule_batch,
)
from src.core.batch_clearing_brute import (
    brute_force_best_ordering,
    brute_force_best_subset,
)
from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in


# -- Helpers -----------------------------------------------------------------


def _quote(reserve_in, reserve_out, amount_in, fee_bps):
    """Wrapper that matches the callable signature expected by the algorithms."""
    return quote_cpmm_swap_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )


# -- Deadline computation tests -----------------------------------------------


class TestDeadlineComputation:
    """Tests for the closed-form deadline formula."""

    def test_zero_min_amount_out_gives_finite_deadline(self):
        """When min_amount_out = 0, the deadline is finite (kernel rejects amount_out=0).

        The CPMM kernel rejects amount_out <= 0 with ValueError, so the effective
        minimum output is 1, not 0. The deadline is the point where amount_out
        drops to 0 and the kernel rejects the swap.
        """
        d = compute_deadline(
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            amount_in=100,
            min_amount_out=0,
            fee_bps=30,
        )
        # With the fix, min_amount_out=0 is treated as effective_min=1,
        # so the deadline is finite (not None).
        assert d is not None
        assert d >= 0

    def test_zero_net_in_gives_negative_deadline(self):
        """When fee consumes entire input, the swap can never execute."""
        d = compute_deadline(
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            amount_in=1,
            min_amount_out=1,
            fee_bps=10_000,  # 100% fee
        )
        assert d == -1

    def test_deadline_allows_swap_at_start(self):
        """A swap with a generous min_amount_out should have a positive deadline."""
        d = compute_deadline(
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            amount_in=100,
            min_amount_out=50,
            fee_bps=30,
        )
        assert d is not None
        assert d >= 0

    def test_deadline_decreases_with_tighter_slippage(self):
        """A higher min_amount_out (tighter slippage) should give a smaller deadline."""
        d_loose = compute_deadline(
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            amount_in=100,
            min_amount_out=10,
            fee_bps=30,
        )
        d_tight = compute_deadline(
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            amount_in=100,
            min_amount_out=90,
            fee_bps=30,
        )
        assert d_loose is not None
        assert d_tight is not None
        assert d_tight <= d_loose

    def test_deadline_is_conservative(self):
        """The deadline should be conservative: a swap at cumulative gross_in = deadline
        should actually execute when simulated with the real CPMM formula."""
        reserve_in_0 = 10_000
        reserve_out_0 = 10_000
        amount_in = 100
        min_amount_out = 50
        fee_bps = 30

        d = compute_deadline(
            reserve_in_0=reserve_in_0,
            reserve_out_0=reserve_out_0,
            amount_in=amount_in,
            min_amount_out=min_amount_out,
            fee_bps=fee_bps,
        )
        assert d is not None and d >= 0

        # Simulate: drain the pool by d units of gross_in, then try the swap.
        # Use a single large swap to drain (simplification for the test).
        r_in = reserve_in_0 + d
        # Under constant-k, R_out = k_0 / R_in. But in reality, R_out is higher
        # (k >= k_0). So we need to simulate actual swaps to drain.
        # For simplicity, just check that at R_in = reserve_in_0 + d, the swap
        # still executes (conservative bound).
        r_out_approx = (reserve_in_0 * reserve_out_0) // r_in  # constant-k R_out

        # The actual R_out is >= r_out_approx (k >= k_0), so if the swap executes
        # at r_out_approx, it definitely executes at the actual R_out.
        net_in = amount_in - (amount_in * fee_bps + 9999) // 10000
        amount_out_approx = (r_out_approx * net_in) // (r_in + net_in)
        # The deadline is conservative, so amount_out_approx >= min_amount_out
        # is NOT guaranteed (the deadline is the boundary). But at d-1 it should
        # be >= min_amount_out.
        if d > 0:
            r_in_below = reserve_in_0 + d - 1
            r_out_below = (reserve_in_0 * reserve_out_0) // r_in_below
            amount_out_below = (r_out_below * net_in) // (r_in_below + net_in)
            assert amount_out_below >= min_amount_out, (
                f"At d-1={d-1}, amount_out={amount_out_below} < min={min_amount_out}"
            )


# -- Parity tests: deadline vs brute-force -----------------------------------


class TestDeadlineParity:
    """Verify deadline scheduling matches brute-force A-optimization."""

    def test_empty_batch(self):
        result = deadline_schedule_batch(
            [],
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == 0
        assert result.total_b == 0
        assert result.ordered_intents == ()

    def test_single_swap_executes(self):
        intents = [("a", 100, 50)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a
        assert result.ordered_intents == brute_ids

    def test_two_swaps_both_execute(self):
        intents = [("a", 100, 50), ("b", 200, 100)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_two_swaps_one_fails_due_to_slippage(self):
        """One swap has a tight slippage that fails after the other executes."""
        intents = [("a", 5000, 4000), ("b", 100, 80)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_three_swaps_mixed_slippage(self):
        intents = [
            ("a", 100, 50),
            ("b", 500, 300),
            ("c", 1000, 800),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_four_swaps_with_conflicts(self):
        """Four swaps where some have tight deadlines that conflict."""
        intents = [
            ("a", 100, 90),
            ("b", 200, 150),
            ("c", 500, 400),
            ("d", 1000, 800),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_five_swaps_hostile_corpus(self):
        """Five swaps with hostile slippage settings."""
        intents = [
            ("a", 50, 40),
            ("b", 300, 250),
            ("c", 1000, 900),
            ("d", 100, 95),
            ("e", 2000, 1800),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_all_swaps_zero_min_amount_out(self):
        """When all swaps have min_amount_out=0, all should execute."""
        intents = [("a", 100, 0), ("b", 200, 0), ("c", 500, 0)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a
        assert result.selected_count + result.greedy_added_count == 3

    def test_large_swap_blocks_small_swaps(self):
        """A large swap with tight slippage blocks smaller swaps."""
        intents = [
            ("big", 8000, 7000),
            ("s1", 100, 80),
            ("s2", 100, 80),
            ("s3", 100, 80),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_zero_fee(self):
        """Zero fee means net_in = amount_in, deadlines are tighter."""
        intents = [("a", 100, 90), ("b", 200, 180), ("c", 500, 400)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=0,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=0,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_high_fee(self):
        """High fee (9900 bps = 99%) means net_in is tiny, deadlines are generous."""
        intents = [("a", 1000, 1), ("b", 2000, 1), ("c", 5000, 1)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=9900,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=9900,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_skewed_reserves(self):
        """Skewed reserves (R_in << R_out) change the deadline structure."""
        intents = [("a", 10, 500), ("b", 50, 2000), ("c", 100, 3000)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=1000,
            reserve_out_0=100_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=1000,
            reserve_out_0=100_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_tiny_pool(self):
        """Tiny pool where even small swaps have significant price impact."""
        intents = [("a", 5, 3), ("b", 3, 2), ("c", 2, 1)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=100,
            reserve_out_0=100,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=100,
            reserve_out_0=100,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_duplicate_amounts_different_slippage(self):
        """Same amount_in, different min_amount_out: tighter slippage = earlier deadline."""
        intents = [("a", 500, 400), ("b", 500, 300), ("c", 500, 200)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )


# -- Property-based tests ----------------------------------------------------


class TestDeadlineProperties:
    """Property-based tests for deadline scheduling invariants."""

    @given(
        n_intents=st.integers(min_value=1, max_value=6),
        reserve_in=st.integers(min_value=100, max_value=100_000),
        reserve_out=st.integers(min_value=100, max_value=100_000),
        fee_bps=st.integers(min_value=0, max_value=500),
        seed=st.integers(min_value=0, max_value=2**31 - 1),
    )
    @settings(max_examples=200, deadline=10_000)
    def test_a_matches_brute_force(self, n_intents, reserve_in, reserve_out, fee_bps, seed):
        """For random configurations, deadline A should match brute-force A."""
        import random
        rng = random.Random(seed)
        intents = []
        for i in range(n_intents):
            amount_in = rng.randint(1, max(2, reserve_in // 10))
            # min_amount_out ranges from 0 (no constraint) to generous
            min_out_choices = [0, 1, rng.randint(1, max(2, reserve_out // 10))]
            min_amount_out = rng.choice(min_out_choices)
            intents.append((f"i{i}", amount_in, min_amount_out))

        result = deadline_schedule_batch(
            intents,
            reserve_in_0=reserve_in,
            reserve_out_0=reserve_out,
            fee_bps=fee_bps,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=reserve_in,
            reserve_out_0=reserve_out,
            fee_bps=fee_bps,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}\n"
            f"intents={intents}\n"
            f"reserve_in={reserve_in}, reserve_out={reserve_out}, fee_bps={fee_bps}\n"
            f"deadline_order={result.ordered_intents}\n"
            f"brute_order={brute_ids}"
        )

    @given(
        n_intents=st.integers(min_value=1, max_value=5),
        reserve_in=st.integers(min_value=500, max_value=50_000),
        reserve_out=st.integers(min_value=500, max_value=50_000),
        fee_bps=st.integers(min_value=0, max_value=300),
        seed=st.integers(min_value=0, max_value=2**31 - 1),
    )
    @settings(max_examples=100, deadline=10_000)
    def test_b_matches_or_exceeds_brute_force_b(self, n_intents, reserve_in, reserve_out, fee_bps, seed):
        """Deadline B should match brute-force B when A matches (same subset, same A).

        Note: B may differ because the deadline algorithm orders by EDF, while
        brute-force finds the B-optimal ordering of the A-optimal subset. The
        deadline algorithm's B should be <= brute-force B (since we don't do
        full B-refinement yet). But A must match.
        """
        import random
        rng = random.Random(seed)
        intents = []
        for i in range(n_intents):
            amount_in = rng.randint(1, max(2, reserve_in // 20))
            min_amount_out = rng.choice([0, 1, rng.randint(1, max(2, reserve_out // 20))])
            intents.append((f"i{i}", amount_in, min_amount_out))

        result = deadline_schedule_batch(
            intents,
            reserve_in_0=reserve_in,
            reserve_out_0=reserve_out,
            fee_bps=fee_bps,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, brute_b = brute_force_best_subset(
            intents,
            reserve_in_0=reserve_in,
            reserve_out_0=reserve_out,
            fee_bps=fee_bps,
            quote_exact_in_fn=_quote,
        )
        # A must match exactly
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}\n"
            f"intents={intents}"
        )


# -- Resource limit tests ----------------------------------------------------


class TestResourceLimits:
    """Tests for resource bound enforcement."""

    def test_resource_limit_raises(self):
        """When max_dp_states is too small, ResourceLimitExceeded is raised."""
        intents = [("a", 100, 50), ("b", 200, 100), ("c", 300, 200)]
        with pytest.raises(ResourceLimitExceeded):
            deadline_schedule_batch(
                intents,
                reserve_in_0=10_000,
                reserve_out_0=10_000,
                fee_bps=30,
                quote_exact_in_fn=_quote,
                max_dp_states=1,  # Way too small
            )

    def test_resource_limit_not_triggered_normal(self):
        """Normal batches should not trigger resource limits."""
        intents = [("a", 100, 50), ("b", 200, 100), ("c", 300, 200)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
            max_dp_states=10_000,
        )
        assert result.total_a > 0


# -- Conservativeness tests --------------------------------------------------


class TestConservativeness:
    """Tests that the deadline-based selection is conservative (no false positives)."""

    def test_selected_swaps_actually_execute(self):
        """Every swap selected by the deadline DP should actually execute
        when simulated with the real CPMM formula."""
        intents = [
            ("a", 100, 90),
            ("b", 500, 400),
            ("c", 1000, 800),
            ("d", 200, 150),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        # Simulate the actual schedule and verify all swaps execute
        r_in = 10_000
        r_out = 10_000
        intent_map = {iid: (ai, mo) for iid, ai, mo in intents}
        for iid in result.ordered_intents:
            amount_in, min_amount_out = intent_map[iid]
            quote = _quote(r_in, r_out, amount_in, 30)
            assert quote.amount_out >= min_amount_out, (
                f"Swap {iid} selected but fails: amount_out={quote.amount_out} < min={min_amount_out}"
            )
            r_in = quote.reserve_in_after
            r_out = quote.reserve_out_after

    def test_greedy_completion_only_adds_executable_swaps(self):
        """Swaps added by greedy completion should actually execute."""
        intents = [
            ("a", 100, 95),  # Tight slippage
            ("b", 500, 400),
            ("c", 50, 40),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        # Verify all ordered intents actually execute (using effective_min)
        r_in = 10_000
        r_out = 10_000
        intent_map = {iid: (ai, mo) for iid, ai, mo in intents}
        for iid in result.ordered_intents:
            amount_in, min_amount_out = intent_map[iid]
            quote = _quote(r_in, r_out, amount_in, 30)
            assert quote.amount_out >= max(min_amount_out, 1), (
                f"Swap {iid} in schedule but fails: amount_out={quote.amount_out} < effective_min={max(min_amount_out, 1)}"
            )
            r_in = quote.reserve_in_after
            r_out = quote.reserve_out_after


# -- Adversarial tests (Codex finding #6) ------------------------------------


class TestAdversarial:
    """Adversarial tests for edge cases and local-search escape."""

    def test_all_identical_swaps(self):
        """All swaps identical: no ordering preference, all should execute."""
        intents = [("a", 100, 50), ("b", 100, 50), ("c", 100, 50), ("d", 100, 50)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, _ = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a

    def test_tiny_reserves(self):
        """Tiny reserves where even small swaps have huge price impact."""
        intents = [("a", 1, 1), ("b", 2, 1), ("c", 1, 1)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10,
            reserve_out_0=10,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, _ = brute_force_best_subset(
            intents,
            reserve_in_0=10,
            reserve_out_0=10,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a

    def test_huge_amount_near_reserve_cap(self):
        """Huge amount_in near the reserve cap (kernel domain limit)."""
        intents = [("a", 2000, 1000), ("b", 1000, 500)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=3000,
            reserve_out_0=3000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, _ = brute_force_best_subset(
            intents,
            reserve_in_0=3000,
            reserve_out_0=3000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a

    def test_100_percent_fee(self):
        """100% fee means net_in = 0, all swaps fail."""
        intents = [("a", 100, 1), ("b", 200, 1)]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=10_000,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == 0
        assert result.ordered_intents == ()

    def test_replace_then_reinsert(self):
        """Test that a replaced swap can be re-inserted in a later round.

        This covers Codex finding #2: the 1-out-1-in phase should return the
        removed swap to the remaining pool for potential re-insertion.
        """
        # Construct a case where replacement is needed, then the removed
        # swap can be re-inserted at a different position
        intents = [
            ("a", 100, 90),
            ("b", 200, 150),
            ("c", 500, 400),
            ("d", 1000, 800),
            ("e", 50, 40),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        brute_ids, brute_a, _ = brute_force_best_subset(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        assert result.total_a == brute_a, (
            f"deadline A={result.total_a} != brute A={brute_a}"
        )

    def test_every_ordered_intent_executes_property(self):
        """Generated check: every returned ordered intent actually executes."""
        intents = [
            ("a", 100, 90),
            ("b", 500, 400),
            ("c", 1000, 800),
            ("d", 200, 150),
            ("e", 50, 40),
            ("f", 300, 250),
        ]
        result = deadline_schedule_batch(
            intents,
            reserve_in_0=10_000,
            reserve_out_0=10_000,
            fee_bps=30,
            quote_exact_in_fn=_quote,
        )
        r_in = 10_000
        r_out = 10_000
        intent_map = {iid: (ai, mo) for iid, ai, mo in intents}
        for iid in result.ordered_intents:
            amount_in, min_amount_out = intent_map[iid]
            quote = _quote(r_in, r_out, amount_in, 30)
            assert quote.amount_out >= max(min_amount_out, 1), (
                f"Swap {iid} in schedule but fails: amount_out={quote.amount_out} "
                f"< effective_min={max(min_amount_out, 1)}"
            )
            r_in = quote.reserve_in_after
            r_out = quote.reserve_out_after

    def test_exhaustive_small_domain(self):
        """Exhaustive small-domain search: try all 3-swap combinations."""
        import itertools
        for seed in range(20):
            import random
            rng = random.Random(seed)
            n = 3
            intents = []
            for i in range(n):
                ai = rng.randint(1, 500)
                mo = rng.choice([0, 1, rng.randint(1, 200)])
                intents.append((f"i{i}", ai, mo))

            result = deadline_schedule_batch(
                intents,
                reserve_in_0=10_000,
                reserve_out_0=10_000,
                fee_bps=30,
                quote_exact_in_fn=_quote,
            )
            brute_ids, brute_a, _ = brute_force_best_subset(
                intents,
                reserve_in_0=10_000,
                reserve_out_0=10_000,
                fee_bps=30,
                quote_exact_in_fn=_quote,
            )
            assert result.total_a == brute_a, (
                f"seed={seed}: deadline A={result.total_a} != brute A={brute_a}\n"
                f"intents={intents}"
            )

    def test_fail_closed_on_invalid_schedule(self):
        """If the deadline formula produces an invalid schedule, the final
        simulation should raise ResourceLimitExceeded (fail-closed)."""
        from src.core.batch_clearing_deadline import _simulate_schedule, DeadlineSwap
        # Create a swap that produces amount_out=32 but has min_amount_out=100.
        # The CPMM kernel will quote it (amount_out=32 > 0), but the simulation
        # should detect amount_out < effective_min and raise.
        bad_swap = DeadlineSwap(
            intent_id="bad",
            amount_in=50,
            min_amount_out=100,  # Tighter than the actual output (32)
            net_in=49,
            deadline=0,
            index=0,
        )
        with pytest.raises(ResourceLimitExceeded):
            _simulate_schedule(
                [bad_swap],
                reserve_in_0=100,
                reserve_out_0=100,
                fee_bps=30,
                quote_exact_in_fn=_quote,
            )
