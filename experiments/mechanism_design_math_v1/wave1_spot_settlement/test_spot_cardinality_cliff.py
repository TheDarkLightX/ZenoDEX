"""Wave 1 spot-settlement cardinality-cliff evidence (O-SS-05).

`_order_swaps_optimal_ab_bounded` in `src/core/batch_clearing.py` brute-forces
the (A, B)-optimal execution order only while the batch holds at most
`_MAX_SWAP_ORDERING_BRUTE_FORCE_N` swaps; one intent past the bound it
    silently falls back to limit-price ordering. These tests bind two hypotheses
    to that branch transition:

- H-MD-SS-005 / O-SS-05: adding one dust intent across the bound can strictly
  lower a victim's fill (here: fill 47619 -> REJECT), while the same dust
  intent added below the bound is harmless.
- H-MD-SS-006 / O-SS-05: the same crossing strictly lowers the global (A, B)
  settlement objective, and the regime switch is driven by cardinality alone.

Replay honesty note. The production bound is 12, so the literal 12 -> 13
instance pair would need the brute-force side to enumerate 12! = 479_001_600
orderings, which is not replayable as a test. The evidence is therefore
layered:

1. The cliff mechanism is replayed end to end on the live
   `compute_settlement` path with the module bound monkeypatched from 12 to
   3 (only the integer bound changes; every ordering and settlement line is
   production code).
2. Both regimes are then bound at the untouched production constant: a
   3-intent batch exercises the brute-force branch (chosen order differs
   from, and beats, limit-price ordering), and a 13-intent batch exercises
   the real fallback branch (returned order equals limit-price ordering
   exactly, and the victim is rejected in full settlement).

These tests are research evidence only. They do not change settlement
behavior.
"""

from __future__ import annotations

import src.core.batch_clearing as bc
from src.core.batch_clearing import (
    _MAX_SWAP_ORDERING_BRUTE_FORCE_N,
    _order_swaps_limit_price,
    _order_swaps_optimal_ab_bounded,
    compute_settlement,
    validate_settlement,
)
from src.core.settlement import FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pool() -> PoolState:
    return PoolState(
        pool_id="pool_ab",
        asset0="A",
        asset1="B",
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=0,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _swap(intent_n: int, sender: str, *, amount_in: int, min_amount_out: int) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_n),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _victim() -> Intent:
    # Executable only near the fresh pool: one-shot quote is
    # floor(1_000_000 * 50_000 / 1_050_000) = 47_619 >= 47_000, but after the
    # rival's 10_000 fill the quote drops to
    # floor(990_100 * 50_000 / 1_060_000) = 46_702 < 47_000.
    return _swap(1, "victim", amount_in=50_000, min_amount_out=47_000)


def _rival() -> Intent:
    # Limit price 9_800/10_000 = 0.98 beats the victim's 0.94, so limit-price
    # ordering executes the rival first and starves the victim.
    return _swap(2, "rival", amount_in=10_000, min_amount_out=9_800)


def _dust(intent_n: int) -> Intent:
    # 1-unit input quotes amount_out == 0 and is itself rejected; its only
    # settlement effect is raising the batch cardinality.
    return _swap(intent_n, f"dust_{intent_n}", amount_in=1, min_amount_out=0)


def _balances(n_dust: int) -> BalanceTable:
    balances = BalanceTable()
    balances.set("victim", "A", 100_000)
    balances.set("rival", "A", 100_000)
    for k in range(3, 3 + n_dust):
        balances.set(f"dust_{k}", "A", 10)
    return balances


def _settle(intents: list[Intent], balances: BalanceTable):
    pools = {"pool_ab": _pool()}
    lp_balances = LPTable()
    settlement = compute_settlement(
        intents,
        pools,
        balances,
        lp_balances,
        swap_ordering="optimal_ab_bounded",
    )
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err
    return settlement


def _fill(settlement, intent_n: int):
    matches = [f for f in settlement.fills if f.intent_id == _iid(intent_n)]
    assert len(matches) == 1
    return matches[0]


def _global_ab(settlement, intents: list[Intent]) -> tuple[int, int]:
    """Recompute the (A, B) objective exactly from settled fills."""
    min_out_by_id = {it.intent_id: it.get_field("min_amount_out") for it in intents}
    a_total = 0
    b_total = 0
    for fill in settlement.fills:
        if fill.action != FillAction.FILL:
            continue
        a_total += fill.amount_in_filled
        b_total += fill.amount_out_filled - min_out_by_id[fill.intent_id]
    return a_total, b_total


# ---------------------------------------------------------------------------
# H-MD-SS-005 / O-SS-05: one dust intent across the bound rejects the victim.
# ---------------------------------------------------------------------------


def test_h_md_ss_005_dust_intent_across_bound_rejects_victim(monkeypatch) -> None:
    """Crossing the brute-force bound flips the victim from 47619 to REJECT.

    Live `compute_settlement` path; only the module bound is reduced 12 -> 3
    so the crossing is replayable (see module docstring).
    """
    monkeypatch.setattr(bc, "_MAX_SWAP_ORDERING_BRUTE_FORCE_N", 3)

    at_bound = _settle([_victim(), _rival(), _dust(3)], _balances(1))
    assert _fill(at_bound, 1).action == FillAction.FILL
    assert _fill(at_bound, 1).amount_out_filled == 47_619
    assert _fill(at_bound, 2).action == FillAction.REJECT  # rival loses the slot
    assert _fill(at_bound, 3).action == FillAction.REJECT  # dust quotes zero out

    past_bound = _settle(
        [_victim(), _rival(), _dust(3), _dust(4)], _balances(2)
    )
    assert _fill(past_bound, 1).action == FillAction.REJECT
    assert _fill(past_bound, 1).reason == "SLIPPAGE"
    assert _fill(past_bound, 2).action == FillAction.FILL
    assert _fill(past_bound, 2).amount_out_filled == 9_900
    assert _fill(past_bound, 4).action == FillAction.REJECT  # the added intent
    # itself executes nothing; it harms the victim purely via cardinality.


def test_h_md_ss_005_dust_intent_below_bound_is_harmless(monkeypatch) -> None:
    """The same dust intent added while staying below the bound changes nothing
    for the victim, isolating the harm to the bound crossing."""
    monkeypatch.setattr(bc, "_MAX_SWAP_ORDERING_BRUTE_FORCE_N", 3)

    without_dust = _settle([_victim(), _rival()], _balances(0))
    with_dust = _settle([_victim(), _rival(), _dust(3)], _balances(1))
    assert _fill(without_dust, 1).amount_out_filled == 47_619
    assert _fill(with_dust, 1).amount_out_filled == 47_619


def test_h_md_ss_005_production_bound_regimes_are_live() -> None:
    """Both cliff regimes fire at the untouched production constant.

    The 13-intent side replays the real fallback branch; the brute-force side
    is replayed at n=3 because n=12 would enumerate 12! = 479_001_600 orders.
    """
    assert _MAX_SWAP_ORDERING_BRUTE_FORCE_N == 12

    pool_state = _pool()
    reserves = (pool_state.reserve0, pool_state.reserve1)

    # Below the bound the optimizer is active: it reorders away from
    # limit-price ordering to put the victim first.
    small = [_victim(), _rival(), _dust(3)]
    small_order = _order_swaps_optimal_ab_bounded(
        small, pool_state=pool_state, balances=_balances(1), reserves=reserves
    )
    small_limit = _order_swaps_limit_price(small)
    assert [i.intent_id for i in small_order] == [_iid(1), _iid(2), _iid(3)]
    assert [i.intent_id for i in small_limit] == [_iid(2), _iid(1), _iid(3)]

    # One intent past the bound the fallback branch returns exactly the
    # limit-price order.
    large = [_victim(), _rival()] + [_dust(k) for k in range(3, 14)]
    assert len(large) == _MAX_SWAP_ORDERING_BRUTE_FORCE_N + 1
    large_order = _order_swaps_optimal_ab_bounded(
        large, pool_state=pool_state, balances=_balances(11), reserves=reserves
    )
    assert [i.intent_id for i in large_order] == [
        i.intent_id for i in _order_swaps_limit_price(large)
    ]

    # Full settlement at n=13 (real constant, real fallback): victim rejected.
    settled_large = _settle(large, _balances(11))
    assert _fill(settled_large, 1).action == FillAction.REJECT
    assert _fill(settled_large, 1).reason == "SLIPPAGE"
    assert _fill(settled_large, 2).amount_out_filled == 9_900

    # Full settlement at n=3 (real constant, real brute force): victim fills.
    settled_small = _settle(small, _balances(1))
    assert _fill(settled_small, 1).amount_out_filled == 47_619


# ---------------------------------------------------------------------------
# H-MD-SS-006 / O-SS-05: the global (A, B) objective drops across the bound.
# ---------------------------------------------------------------------------


def test_h_md_ss_006_global_ab_objective_drops_across_bound(monkeypatch) -> None:
    """Adding one dust intent across the (reduced) bound strictly lowers the
    global objective from (A, B) = (50000, 619) to (10000, 100)."""
    monkeypatch.setattr(bc, "_MAX_SWAP_ORDERING_BRUTE_FORCE_N", 3)

    small = [_victim(), _rival(), _dust(3)]
    settled_small = _settle(small, _balances(1))
    assert _global_ab(settled_small, small) == (50_000, 619)

    large = [_victim(), _rival(), _dust(3), _dust(4)]
    settled_large = _settle(large, _balances(2))
    assert _global_ab(settled_large, large) == (10_000, 100)


def test_h_md_ss_006_fallback_regime_cost_at_production_bound() -> None:
    """At the untouched production constant the two regimes price the same
    core instance differently: brute force settles (50000, 619), limit-price
    ordering settles (10000, 100). Cardinality alone selects between them."""
    assert _MAX_SWAP_ORDERING_BRUTE_FORCE_N == 12

    pools = {"pool_ab": _pool()}
    lp_balances = LPTable()
    small = [_victim(), _rival(), _dust(3)]

    by_mode: dict[str, tuple[int, int]] = {}
    for mode in ("optimal_ab_bounded", "limit_price"):
        balances = _balances(1)
        settlement = compute_settlement(
            small, pools, balances, lp_balances, swap_ordering=mode
        )
        ok, err = validate_settlement(settlement, balances, pools, lp_balances)
        assert ok, err
        by_mode[mode] = _global_ab(settlement, small)

    assert by_mode["optimal_ab_bounded"] == (50_000, 619)
    assert by_mode["limit_price"] == (10_000, 100)

    # n=13 under optimal_ab_bounded settles at the limit-price objective:
    # the fallback regime, entered by cardinality alone.
    large = [_victim(), _rival()] + [_dust(k) for k in range(3, 14)]
    settled_large = _settle(large, _balances(11))
    assert _global_ab(settled_large, large) == (10_000, 100)
