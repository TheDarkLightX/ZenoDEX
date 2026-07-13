"""Correctness lock for the polynomial exact CoW matcher.

`_cow_pair_netting_exact_in_v1` matched opposite-direction swaps with a
super-exponential brute force CAPPED at 8 candidates, falling back to a NON-optimal
O(n^2) greedy beyond the cap. The versioned exact profile uses
`_cow_exact_match_uncoupled` for the uncoupled case (no per-sender balance constraint
binds): max-weight bipartite matching (Kuhn-Munkres, O(n^3)) for the (A, B) optimum,
plus an ascending-ban pass for the lex-max-of-ascending-pair-ids tie-break. The
legacy `cow_pair_netting_v1` profile keeps its prior fallback semantics for replay
stability.

This module proves it (a) is BIT-IDENTICAL to the brute-force objective on inputs
within the brute-verifiable range, and (b) beyond the cap is a VALID matching whose
(A, B) is >= the greedy's (and usually strictly better -- the greedy left value on the
table). The objective mirrors the brute force exactly:
  feasible(x,y): y.in >= x.min_out and x.in >= y.min_out
  A_xy = x.in + y.in ; B_xy = (y.in - x.min_out) + (x.in - y.min_out)
  maximize (A, B, sorted-tuple-of-(x_id,y_id)) lexicographically.
"""

from __future__ import annotations

import random
import sys
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import src.core.batch_clearing as batch_clearing_module  # noqa: E402
from src.core.batch_clearing import (  # noqa: E402
    _COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2,
    _MAX_COW_EXACT_MATCH_TOTAL_CANDIDATES,
    _cow_exact_match_uncoupled,
    _cow_exact_match_work_within_cap,
    _cow_feasible,
    _cow_pair_ab,
    _cow_pair_netting_exact_in_v1,
    _CowCandidateExactIn,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import PoolState, PoolStatus, compute_pool_id  # noqa: E402


def _cand(cid: str, amount_in: int, min_out: int, sender: str) -> _CowCandidateExactIn:
    return _CowCandidateExactIn(
        intent=types.SimpleNamespace(intent_id=cid),
        amount_in=amount_in,
        min_amount_out=min_out,
        sender=sender,
        recipient=sender,
        asset_in="A",
        asset_out="B",
    )


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pk(n: int) -> str:
    return "0x" + f"{n:096x}"


def _brute(s01, s10):
    """Reference exact (A, B, lex) matching by full enumeration (uncoupled inputs)."""
    best_key = None
    best: list = []

    def rec(i, used, acc):
        nonlocal best_key, best
        if i >= len(s01):
            a = sum(_cow_pair_ab(x, y)[0] for x, y in acc)
            b = sum(_cow_pair_ab(x, y)[1] for x, y in acc)
            pids = tuple(sorted((x.intent.intent_id, y.intent.intent_id) for x, y in acc))
            key = (a, b, pids)
            if best_key is None or key > best_key:
                best_key = key
                best = list(acc)
            return
        rec(i + 1, used, acc)
        x = s01[i]
        for j, y in enumerate(s10):
            if j in used or not _cow_feasible(x, y):
                continue
            acc.append((x, y))
            rec(i + 1, used | {j}, acc)
            acc.pop()

    rec(0, set(), [])
    return best


def _greedy(s01, s10):
    """Reference of the prior non-optimal greedy fallback."""
    s01s = sorted(s01, key=lambda c: (-c.min_amount_out, c.intent.intent_id))
    pool = list(s10)
    pairs = []
    usedj: set = set()
    for x in s01s:
        bj = by = None
        for j, y in enumerate(pool):
            if j in usedj or not _cow_feasible(x, y):
                continue
            if by is None or (y.amount_in, y.intent.intent_id) < (by.amount_in, by.intent.intent_id):
                bj, by = j, y
        if bj is None:
            continue
        usedj.add(bj)
        pairs.append((x, by))
    return pairs


def _pairset(pairs):
    return tuple(sorted((x.intent.intent_id, y.intent.intent_id) for x, y in pairs))


def _ab(pairs):
    return (sum(_cow_pair_ab(x, y)[0] for x, y in pairs),
            sum(_cow_pair_ab(x, y)[1] for x, y in pairs))


def _is_valid(pairs):
    xs = [x.intent.intent_id for x, _ in pairs]
    ys = [y.intent.intent_id for _, y in pairs]
    return (len(xs) == len(set(xs)) and len(ys) == len(set(ys))
            and all(_cow_feasible(x, y) for x, y in pairs))


def _random_sides(rng, n0, n1):
    # Vary the magnitude up to ~1e12 so the edge weights A*scale+B span the range that
    # exposed a fixed-sentinel overflow in the matching solver (regression coverage).
    big = rng.choice([50, 10 ** 6, 10 ** 9, 3 * 10 ** 9, 10 ** 12])
    s01 = [_cand(f"a{i:02d}", rng.randint(1, big), rng.randint(0, big), f"s01_{i}") for i in range(n0)]
    s10 = [_cand(f"b{i:02d}", rng.randint(1, big), rng.randint(0, big), f"s10_{i}") for i in range(n1)]
    return s01, s10


def _divergent_pair_netting_case():
    """Case found during review: exact uncoupled improves the objective, so it must
    stay behind a versioned profile and must not silently change cow_pair_netting_v1."""
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id=compute_pool_id(asset0, asset1, 30),
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000_000_000,
        reserve1=1_000_000_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    side_01 = [
        ("a00", 1_635_320_117, 859_317_502),
        ("a01", 2_574_571_356, 767_950_141),
        ("a02", 988_970_881, 1_067_004_398),
        ("a03", 572_280_321, 371_851_742),
        ("a04", 1_078_685_360, 1_645_262_724),
    ]
    side_10 = [
        ("b00", 2_279_822_771, 2_939_083_229),
        ("b01", 2_313_394_523, 385_843_939),
        ("b02", 2_679_714_517, 2_101_419_947),
        ("b03", 856_709_067, 1_810_926_946),
        ("b04", 2_633_742_916, 2_527_189_548),
    ]
    labels: dict[str, str] = {}
    intents: list[Intent] = []
    balances = BalanceTable()
    for offset, (label, amount_in, min_out) in enumerate(side_01, start=1):
        intent_id = _iid(offset)
        sender = _pk(offset)
        labels[label] = intent_id
        balances.set(sender, asset0, amount_in)
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=intent_id,
                sender_pubkey=sender,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset0,
                    "asset_out": asset1,
                    "amount_in": amount_in,
                    "min_amount_out": min_out,
                },
            )
        )
    for offset, (label, amount_in, min_out) in enumerate(side_10, start=101):
        intent_id = _iid(offset)
        sender = _pk(offset)
        labels[label] = intent_id
        balances.set(sender, asset1, amount_in)
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=intent_id,
                sender_pubkey=sender,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset1,
                    "asset_out": asset0,
                    "amount_in": amount_in,
                    "min_amount_out": min_out,
                },
            )
        )
    return pool, balances, intents, labels


def _filled_ids(fills):
    return {fill.intent_id for fill in fills}


def test_exact_matcher_work_cap_rejects_large_uncoupled_batches():
    n = (_MAX_COW_EXACT_MATCH_TOTAL_CANDIDATES // 2) + 1
    s01 = [_cand(f"a{i:02d}", 10, 0, f"s01_{i}") for i in range(n)]
    s10 = [_cand(f"b{i:02d}", 10, 0, f"s10_{i}") for i in range(n)]
    assert not _cow_exact_match_work_within_cap(s01, s10)


def test_pair_netting_falls_back_when_exact_uncoupled_work_is_over_cap(monkeypatch):
    """Large uncoupled batches must not enter the exact matcher.

    The exact matcher re-solves an assignment problem during lex tie-breaking, so
    the public helper must preserve the old bounded fallback behavior above the
    local cap.
    """
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool = PoolState(
        pool_id=compute_pool_id(asset0, asset1, 30),
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    intents = []
    n = (_MAX_COW_EXACT_MATCH_TOTAL_CANDIDATES // 2) + 1
    for i in range(n):
        sender = "0x" + f"{i + 1:096x}"
        balances.set(sender, asset0, 10)
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(i + 1),
                sender_pubkey=sender,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset0,
                    "asset_out": asset1,
                    "amount_in": 10,
                    "min_amount_out": 0,
                },
            )
        )
    for i in range(n):
        sender = "0x" + f"{100 + i + 1:096x}"
        balances.set(sender, asset1, 10)
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(100 + i + 1),
                sender_pubkey=sender,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": asset1,
                    "asset_out": asset0,
                    "amount_in": 10,
                    "min_amount_out": 0,
                },
            )
        )

    def _unexpected_exact_call(*_args, **_kwargs):
        raise AssertionError("exact matcher should be capped for this batch")

    monkeypatch.setattr(batch_clearing_module, "_cow_exact_match_uncoupled", _unexpected_exact_call)
    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)

    assert not remaining
    assert len(fills) == 2 * n
    assert all(fill.reason == "COW_NETTED" for fill in fills)


def test_cow_v1_keeps_legacy_greedy_fallback_and_v2_uses_exact_profile():
    pool, balances, intents, labels = _divergent_pair_netting_case()
    legacy_fills, legacy_remaining = _cow_pair_netting_exact_in_v1(
        intents,
        pool_state=pool,
        balances=balances,
    )
    assert _filled_ids(legacy_fills) == {
        labels["a01"],
        labels["b03"],
        labels["a04"],
        labels["b01"],
    }
    assert _filled_ids(legacy_fills).isdisjoint({it.intent_id for it in legacy_remaining})

    pool, balances, intents, labels = _divergent_pair_netting_case()
    exact_fills, exact_remaining = _cow_pair_netting_exact_in_v1(
        intents,
        pool_state=pool,
        balances=balances,
        matching_profile=_COW_PAIR_NETTING_MATCH_EXACT_UNCOUPLED_V2,
    )
    assert _filled_ids(exact_fills) == {
        labels["a00"],
        labels["b01"],
        labels["a01"],
        labels["b02"],
    }
    assert _filled_ids(exact_fills).isdisjoint({it.intent_id for it in exact_remaining})


def test_exact_matcher_large_value_overflow_regression():
    """Regression (caught in review): with large amounts the edge weights A*scale+B
    exceeded a fixed 1<<62 Hungarian sentinel and the matcher returned a SUBOPTIMAL
    matching. The sentinels are now derived from the actual weights (Python big ints)."""
    s01 = [_cand("a0", 1_000_000, 1000, "sa0"), _cand("a1", 2, 1, "sa1")]
    s10 = [_cand("b0", 3_000_000_000, 1, "sb0"), _cand("b1", 10, 0, "sb1"),
           _cand("b2", 10, 3_000_000_000, "sb2")]
    got = _pairset(_cow_exact_match_uncoupled(s01, s10))
    assert got == _pairset(_brute(s01, s10))
    assert got == (("a0", "b0"), ("a1", "b1"))


def test_exact_matcher_bit_identical_to_brute_within_cap():
    """On inputs within the brute-verifiable range, the exact matcher reproduces the
    brute force's (A, B, lex) choice EXACTLY -- proving the objective is preserved."""
    rng = random.Random(20260614)
    checked = nontrivial = 0
    for _ in range(3000):
        n0, n1 = rng.randint(0, 4), rng.randint(0, 4)
        s01, s10 = _random_sides(rng, n0, n1)
        exact = _cow_exact_match_uncoupled(s01, s10)
        brute = _brute(s01, s10)
        assert _pairset(exact) == _pairset(brute), (n0, n1, _pairset(exact), _pairset(brute))
        checked += 1
        if brute:
            nontrivial += 1
    assert checked >= 3000
    assert nontrivial >= 800, f"too few nontrivial matches ({nontrivial}) -- vacuous"


def test_exact_matcher_valid_and_at_least_greedy_beyond_cap():
    """Beyond the brute cap, the exact matcher is a VALID matching whose (A, B) is never
    worse than the greedy's and is strictly better in the large majority of cases."""
    rng = random.Random(99)
    tested = strictly_better = 0
    for _ in range(1500):
        n0, n1 = rng.randint(5, 13), rng.randint(5, 13)
        s01, s10 = _random_sides(rng, n0, n1)
        exact = _cow_exact_match_uncoupled(s01, s10)
        assert _is_valid(exact), "exact matcher produced an invalid matching"
        ab_e = _ab(exact)
        ab_g = _ab(_greedy(s01, s10))
        assert ab_e >= ab_g, f"exact {ab_e} worse than greedy {ab_g}"
        tested += 1
        if ab_e > ab_g:
            strictly_better += 1
    assert tested >= 1000
    # The whole point of the optimization: it routinely beats the greedy beyond the cap.
    assert strictly_better >= tested // 2, f"only {strictly_better}/{tested} strictly better"


def test_exact_matcher_deterministic():
    rng = random.Random(7)
    for _ in range(200):
        s01, s10 = _random_sides(rng, rng.randint(0, 8), rng.randint(0, 8))
        r1 = _pairset(_cow_exact_match_uncoupled(s01, s10))
        r2 = _pairset(_cow_exact_match_uncoupled(s01, s10))
        assert r1 == r2
