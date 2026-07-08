from __future__ import annotations

from random import Random

import pytest

from src.core.cross_pool_subset_dp import (
    SubsetDPLimits,
    TwoPoolCPMM,
    brute_force_k_pool_cpmm_batch,
    brute_force_two_pool_cpmm_batch,
    compressed_state_pruning_margin,
    cpmm_exact_in_output_allow_zero,
    replay_k_pool_cpmm_executions,
    replay_two_pool_cpmm_executions,
    solve_k_pool_cpmm_subset_dp,
    solve_two_pool_cpmm_full_state_dp,
    solve_two_pool_cpmm_multiset_dp,
    solve_two_pool_cpmm_subset_dp,
    solve_k_pool_cpmm_multiset_dp,
)


def test_subset_dp_matches_known_cpss_bc_counterexamples() -> None:
    cases = (
        ((TwoPoolCPMM(1, 2, 0), TwoPoolCPMM(2, 2, 0), [1, 1, 2]), 2),
        ((TwoPoolCPMM(1, 2, 0), TwoPoolCPMM(1, 6, 0), [1, 2, 4]), 6),
    )
    for (pool0, pool1, intents), expected_out in cases:
        result = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents)
        assert result.amount_out_total == expected_out
        assert replay_two_pool_cpmm_executions(pool0, pool1, result.executions) == expected_out


def test_subset_dp_matches_factorial_bruteforce_on_seeded_small_corpus() -> None:
    rng = Random(20260626)
    reserves = [1, 2, 3, 5, 10, 50, 100]
    fees = [0, 1, 10, 30, 100, 500, 1000, 5000, 9999]
    for _ in range(200):
        n = rng.choice([1, 2, 3, 4])
        amount_max = {1: 14, 2: 12, 3: 8, 4: 5}[n]
        pool0 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        pool1 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        intents = [rng.randint(1, amount_max) for _ in range(n)]

        expected = brute_force_two_pool_cpmm_batch(pool0, pool1, intents)
        actual = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents)

        assert actual.amount_out_total == expected.amount_out_total
        assert replay_two_pool_cpmm_executions(pool0, pool1, actual.executions) == actual.amount_out_total


def test_compressed_subset_dp_matches_full_state_oracle_with_state_collisions() -> None:
    # This case was found by an adversarial collision search. The compressed
    # key hides many y1 reserves, so it directly pressures the pruning rule.
    pool0 = TwoPoolCPMM(5, 10, 5000)
    pool1 = TwoPoolCPMM(2, 1000, 5000)
    intents = [4, 6, 5, 3, 7]

    compressed = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents)
    full = solve_two_pool_cpmm_full_state_dp(pool0, pool1, intents)

    assert compressed.amount_out_total == full.amount_out_total == 780
    assert compressed.max_states_per_subset < full.max_states_per_subset
    assert full.max_compressed_collision > 1
    assert replay_two_pool_cpmm_executions(pool0, pool1, compressed.executions) == compressed.amount_out_total


def test_subset_dp_matches_full_state_oracle_on_seeded_medium_corpus() -> None:
    rng = Random(20260627)
    reserves = [1, 2, 3, 4, 5, 10, 50, 100, 500, 1000]
    fees = [0, 1, 10, 30, 100, 500, 1000, 5000, 9999]
    for _ in range(150):
        n = rng.choice([3, 4, 5])
        amount_max = {3: 14, 4: 9, 5: 6}[n]
        pool0 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        pool1 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        intents = [rng.randint(1, amount_max) for _ in range(n)]

        compressed = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents)
        full = solve_two_pool_cpmm_full_state_dp(pool0, pool1, intents)

        assert compressed.amount_out_total == full.amount_out_total


def test_multiset_dp_matches_subset_dp_on_seeded_duplicate_corpus() -> None:
    rng = Random(20260628)
    reserves = [1, 2, 3, 5, 10, 50, 100, 500, 1000]
    fees = [0, 1, 10, 30, 100, 500, 1000, 5000, 9999]
    for _ in range(200):
        n = rng.choice([4, 5, 6, 7])
        alphabet = [rng.randint(1, 8) for _ in range(rng.choice([1, 2, 3]))]
        intents = [rng.choice(alphabet) for _ in range(n)]
        pool0 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        pool1 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))

        subset = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents, trace_mode="none")
        multiset = solve_two_pool_cpmm_multiset_dp(pool0, pool1, intents, trace_mode="none")

        assert multiset.amount_out_total == subset.amount_out_total


def test_multiset_dp_compresses_equal_amount_intents() -> None:
    pool0 = TwoPoolCPMM(5, 10, 5000)
    pool1 = TwoPoolCPMM(2, 1000, 5000)
    intents = [4, 4, 4, 4, 4, 4]

    subset = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents, trace_mode="none")
    multiset = solve_two_pool_cpmm_multiset_dp(pool0, pool1, intents, trace_mode="none")

    assert multiset.amount_out_total == subset.amount_out_total == 773
    assert multiset.ordering_count_upper_bound == 1
    assert subset.ordering_count_upper_bound == 720
    assert multiset.states_visited < subset.states_visited
    assert multiset.transitions_evaluated < subset.transitions_evaluated


def test_k_pool_subset_dp_matches_two_pool_subset_dp() -> None:
    rng = Random(20260629)
    reserves = [1, 2, 3, 5, 10, 50, 100]
    fees = [0, 1, 10, 30, 100, 1000, 9999]
    for _ in range(75):
        pool0 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        pool1 = TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
        intents = [rng.randint(1, 8) for _ in range(rng.choice([1, 2, 3, 4]))]

        two_pool = solve_two_pool_cpmm_subset_dp(pool0, pool1, intents, trace_mode="none")
        k_pool = solve_k_pool_cpmm_subset_dp([pool0, pool1], intents, trace_mode="none")

        assert k_pool.pool_count == 2
        assert k_pool.amount_out_total == two_pool.amount_out_total


def test_k_pool_subset_dp_matches_bruteforce_on_seeded_small_corpus() -> None:
    rng = Random(20260630)
    reserves = [1, 2, 3, 5, 10, 50, 100]
    fees = [0, 1, 10, 30, 100, 1000, 9999]
    configs = ((3, 3, 40, 4), (4, 2, 40, 4), (5, 2, 30, 3))
    for pool_count, intent_count, trials, amount_max in configs:
        for _ in range(trials):
            pools = tuple(
                TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
                for _ in range(pool_count)
            )
            intents = [rng.randint(1, amount_max) for _ in range(intent_count)]

            subset = solve_k_pool_cpmm_subset_dp(pools, intents)
            brute = brute_force_k_pool_cpmm_batch(pools, intents)

            assert subset.amount_out_total == brute.amount_out_total
            assert replay_k_pool_cpmm_executions(pools, subset.executions) == subset.amount_out_total


def test_k_pool_multiset_dp_matches_subset_dp_on_seeded_duplicate_corpus() -> None:
    rng = Random(20260631)
    reserves = [1, 2, 3, 5, 10, 50, 100]
    fees = [0, 1, 10, 30, 100, 1000, 5000, 9999]
    configs = ((3, 4, 35, 4), (3, 5, 20, 3), (4, 3, 25, 3), (4, 4, 12, 2))
    for pool_count, intent_count, trials, amount_max in configs:
        for _ in range(trials):
            alphabet = [rng.randint(1, amount_max) for _ in range(rng.choice([1, 2]))]
            intents = [rng.choice(alphabet) for _ in range(intent_count)]
            pools = tuple(
                TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
                for _ in range(pool_count)
            )

            subset = solve_k_pool_cpmm_subset_dp(pools, intents, trace_mode="none")
            multiset = solve_k_pool_cpmm_multiset_dp(pools, intents, trace_mode="none")

            assert multiset.amount_out_total == subset.amount_out_total


def test_k_pool_multiset_dp_matches_bruteforce_on_seeded_small_corpus() -> None:
    rng = Random(20260632)
    reserves = [1, 2, 3, 5, 10]
    fees = [0, 1, 10, 30, 100, 1000, 5000, 9999]
    configs = ((3, 4, 14, 2), (4, 3, 10, 2))
    for pool_count, intent_count, trials, amount_max in configs:
        for _ in range(trials):
            alphabet = [rng.randint(1, amount_max) for _ in range(rng.choice([1, 2]))]
            intents = [rng.choice(alphabet) for _ in range(intent_count)]
            pools = tuple(
                TwoPoolCPMM(rng.choice(reserves), rng.choice(reserves), rng.choice(fees))
                for _ in range(pool_count)
            )

            multiset = solve_k_pool_cpmm_multiset_dp(pools, intents)
            brute = brute_force_k_pool_cpmm_batch(pools, intents)

            assert multiset.amount_out_total == brute.amount_out_total
            assert replay_k_pool_cpmm_executions(pools, multiset.executions) == multiset.amount_out_total


def test_k_pool_multiset_dp_compresses_equal_amount_intents() -> None:
    pools = (
        TwoPoolCPMM(5, 10, 5000),
        TwoPoolCPMM(2, 1000, 5000),
        TwoPoolCPMM(7, 300, 30),
    )
    intents = [4, 4, 4, 4, 4, 4]

    subset = solve_k_pool_cpmm_subset_dp(pools, intents, trace_mode="none")
    multiset = solve_k_pool_cpmm_multiset_dp(pools, intents, trace_mode="none")

    assert multiset.amount_out_total == subset.amount_out_total == 861
    assert multiset.ordering_count_upper_bound == 1
    assert subset.ordering_count_upper_bound == 720
    assert multiset.states_visited < subset.states_visited
    assert multiset.transitions_evaluated < subset.transitions_evaluated


def test_cpmm_output_is_one_lipschitz_in_output_reserve_for_future_advantage_bound() -> None:
    fees = [0, 1, 10, 30, 100, 500, 1000, 5000, 9999]
    for x in range(1, 12):
        for y in range(1, 16):
            for delta_y in range(0, 8):
                for amount_in in range(0, 16):
                    for fee_bps in fees:
                        low = cpmm_exact_in_output_allow_zero(TwoPoolCPMM(x, y, fee_bps), amount_in)
                        high = cpmm_exact_in_output_allow_zero(TwoPoolCPMM(x, y + delta_y, fee_bps), amount_in)
                        assert high - low <= delta_y


def test_compressed_collision_margin_matches_conservation_identity() -> None:
    # For a compressed-state collision, the retained path's extra banked output
    # equals the discarded path's extra pool1 y-reserve. This is the tight case
    # for the Lipschitz proof obligation.
    assert compressed_state_pruning_margin(banked_output_delta=17, y_reserve_delta=17) == 0
    assert compressed_state_pruning_margin(banked_output_delta=18, y_reserve_delta=17) == 1


def test_limits_and_input_validation_fail_closed() -> None:
    pool0 = TwoPoolCPMM(10, 10, 0)
    pool1 = TwoPoolCPMM(10, 10, 0)
    assert solve_two_pool_cpmm_subset_dp(pool0, pool1, [2], trace_mode="none").executions == tuple()
    with pytest.raises(ValueError, match="trace_mode"):
        solve_two_pool_cpmm_subset_dp(pool0, pool1, [2], trace_mode="verbose")
    with pytest.raises(ValueError, match="fee_bps out of range"):
        solve_two_pool_cpmm_subset_dp(TwoPoolCPMM(10, 10, 10_001), pool1, [1])
    with pytest.raises(ValueError, match="intent count exceeds"):
        solve_two_pool_cpmm_subset_dp(pool0, pool1, [1, 1], limits=SubsetDPLimits(max_intents=1))
    with pytest.raises(ValueError, match="total input exceeds"):
        solve_two_pool_cpmm_subset_dp(pool0, pool1, [10], limits=SubsetDPLimits(max_total_input=9))
    with pytest.raises(ValueError, match="must be positive"):
        solve_two_pool_cpmm_subset_dp(pool0, pool1, [0])
