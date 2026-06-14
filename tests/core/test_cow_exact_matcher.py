"""Correctness lock for the polynomial exact CoW matcher.

`_cow_pair_netting_exact_in_v1` previously matched opposite-direction swaps with a
super-exponential brute force CAPPED at 8 candidates, falling back to a NON-optimal
O(n^2) greedy beyond the cap. `_cow_exact_match_uncoupled` replaces both for the
uncoupled case (no per-sender balance constraint binds) with a polynomial exact
solver: max-weight bipartite matching (Kuhn-Munkres, O(n^3)) for the (A, B) optimum,
plus an ascending-ban pass for the lex-max-of-ascending-pair-ids tie-break.

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

from src.core.batch_clearing import (  # noqa: E402
    _CowCandidateExactIn,
    _cow_exact_match_uncoupled,
    _cow_feasible,
    _cow_pair_ab,
)


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
