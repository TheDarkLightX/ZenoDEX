from __future__ import annotations

from src.core.batch_clearing import (
    _SWAP_ORDERING_MCI_AB_GLOBAL,
    _eval_ordering_ab,
    _order_swaps_mci_ab,
    _order_swaps_optimal_ab_bounded,
    _refine_ab_ordering_global,
    compute_settlement,
    validate_settlement,
)
from src.core.batch_clearing_ordering import _OptimalAbBoundedRequest
from src.state.lp import LPTable
from tools.metamuse_batch_ordering_lane import (
    BATCH_MCI_CURATED_CASES,
    build_case_balances,
    build_case_pool_and_intents,
)


def test_mci_global_matches_bounded_optimum_on_curated_corpus() -> None:
    for case in BATCH_MCI_CURATED_CASES:
        pool, intents = build_case_pool_and_intents(case)
        balances = build_case_balances(case)
        reserves = (pool.reserve0, pool.reserve1)

        mci_seed = _order_swaps_mci_ab(intents, pool_state=pool, reserves=reserves)
        mci_order = _refine_ab_ordering_global(mci_seed, pool_state=pool, reserves=reserves)
        optimal_order = _order_swaps_optimal_ab_bounded(
            _OptimalAbBoundedRequest(
                intents=intents,
                pool_state=pool,
                balances=balances,
                reserves=reserves,
            )
        )

        assert _eval_ordering_ab(mci_order, pool, reserves) == case.expected_ab
        assert _eval_ordering_ab(optimal_order, pool, reserves) == case.expected_ab


def test_mci_global_improves_known_witness_over_greedy_global_baseline() -> None:
    case = BATCH_MCI_CURATED_CASES[5]
    pool, intents = build_case_pool_and_intents(case)
    reserves = (pool.reserve0, pool.reserve1)

    mci_seed = _order_swaps_mci_ab(intents, pool_state=pool, reserves=reserves)
    mci_order = _refine_ab_ordering_global(mci_seed, pool_state=pool, reserves=reserves)

    assert _eval_ordering_ab(mci_order, pool, reserves) == case.expected_ab
    assert case.expected_ab > case.baseline_ab


def test_mci_global_mode_is_accepted_and_settlement_valid() -> None:
    case = BATCH_MCI_CURATED_CASES[0]
    pool, intents = build_case_pool_and_intents(case)
    pools = {pool.pool_id: pool}
    balances = build_case_balances(case)
    lp = LPTable()

    settlement = compute_settlement(
        intents,
        pools,
        balances,
        lp,
        swap_ordering=_SWAP_ORDERING_MCI_AB_GLOBAL,
    )
    ok, err = validate_settlement(settlement, balances, pools, lp)
    assert ok, err
