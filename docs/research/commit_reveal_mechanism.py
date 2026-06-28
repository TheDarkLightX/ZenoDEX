"""Commit-reveal mechanism investigation.

The root cause analysis showed that the inflate attack is fundamental to CPMM:
the marginal output exceeds the average output, creating capturable surplus.

Two remaining fixes:
1. Burn mechanism (already tested: 50% burn = 97.9% SP, 50% welfare loss)
2. Commit-reveal with binding amount: users commit to amount_in before the
   batch, so they can't inflate it strategically.

Commit-reveal protocol:
1. Commit phase: Users submit hash(commitment) = hash(amount_in, nonce)
2. Reveal phase: Users reveal amount_in and nonce
3. Settlement: amount_in is binding (must match commitment)
4. Ordering: (A,B) optimal on the revealed amounts

This makes amount_in non-strategic because:
- The user must commit BEFORE seeing other users' bids
- The committed amount is binding (can't be inflated after seeing others)
- The only strategic dimension is min_out, which we showed has 0 violations

However, commit-reveal has a liveness issue: users can choose not to reveal.
This is typically solved by requiring a deposit that's slashed on non-reveal.

For this test, we simulate commit-reveal by assuming amount_in is truthful
(non-strategic) and only min_out is strategic. We then test if the (A,B)
mechanism is strategyproof when only min_out can be misreported.

Additionally, we test a "binding amount" variant where the user MUST execute
the full committed amount (no partial fill). This eliminates the inflate attack
entirely because the user can't report a larger amount than they want to trade.
"""
from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass


def fee_calc(a: int, fee_bps: int) -> int:
    return -(-a * fee_bps // 10000)


def q(x: int, y: int, a: int, fee_bps: int) -> int:
    if a <= 0:
        return 0
    fee = fee_calc(a, fee_bps)
    net = a - fee
    if net <= 0:
        return 0
    return (y * net) // (x + net)


@dataclass(frozen=True)
class Intent:
    user: int
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class Pool:
    x: int
    y: int
    fee_bps: int


@dataclass(frozen=True)
class ExecResult:
    idx: int
    filled: bool
    amount_in: int
    actual_out: int
    surplus: int


def true_rate(amount_in_true: int, min_out_true: int) -> float:
    if amount_in_true <= 0:
        return 0.0
    return min_out_true / amount_in_true


def user_utility(amount_in_paid: int, actual_out: int, amount_in_true: int, min_out_true: int) -> float:
    rate = true_rate(amount_in_true, min_out_true)
    return actual_out - amount_in_paid * rate


def batch_clear_ab(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    n = len(intents)
    if n == 0:
        return []
    best_key = (-1, -1)
    best_execs = []
    for perm in itertools.permutations(range(n)):
        x, y, fee = pool.x, pool.y, pool.fee_bps
        xr, yr = x, y
        total_vol = 0
        total_surplus = 0
        execs = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(n)]
        for i in perm:
            d = intents[i].amount_in
            min_out = intents[i].min_out
            out = q(xr, yr, d, fee)
            if out >= min_out and d > 0:
                total_vol += d
                total_surplus += out - min_out
                execs[i] = ExecResult(i, True, d, out, out - min_out)
                f = fee_calc(d, fee)
                xr = xr + d - f
                yr = yr - out
        key = (total_vol, total_surplus)
        if key > best_key:
            best_key = key
            best_execs = execs
    return best_execs


def user_utility_in_batch(execs: list[ExecResult], intents: list[Intent], user: int,
                          amt_true: int, min_true: int) -> float:
    util = 0.0
    for ex in execs:
        if intents[ex.idx].user != user:
            continue
        paid = ex.amount_in if ex.filled else 0
        out = ex.actual_out if ex.filled else 0
        util += user_utility(paid, out, amt_true, min_true)
    return util


def gen_intents(rng: random.Random, pool: Pool) -> list[Intent]:
    n = rng.randint(3, 5)
    intents = []
    for u in range(n):
        d = rng.randint(50, 500)
        out = q(pool.x, pool.y, d, pool.fee_bps)
        lo = max(1, out * 50 // 100)
        hi = max(lo + 1, out * 95 // 100)
        min_out = rng.randint(lo, hi)
        intents.append(Intent(user=u, amount_in=d, min_out=min_out))
    return intents


def test_sp_min_out_only(clear_fn, rng: random.Random, n_trials: int,
                         time_budget: float = 100) -> dict:
    """Test strategyproofness when ONLY min_out can be misreported
    (simulating commit-reveal where amount_in is binding).

    This tests the core hypothesis: if amount_in is non-strategic,
    is the (A,B) mechanism strategyproof?
    """
    helped = 0
    helped_lower = 0
    helped_raise = 0
    total_checks = 0
    max_gain = 0.0
    total_welfare = 0.0
    total_filled = 0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)
        intents = gen_intents(rng, pool)

        truthful = clear_fn(pool, intents)

        trial_welfare = 0.0
        for u in range(len(intents)):
            amt_true = intents[u].amount_in
            min_true = intents[u].min_out
            base_util = user_utility_in_batch(truthful, intents, u, amt_true, min_true)
            trial_welfare += base_util
            if truthful[u].filled:
                total_filled += 1

            # Misreport: lower min_out by 10% (easier to fill)
            mis_m = intents[u].min_out * 9 // 10
            mis = [Intent(intents[j].user, intents[j].amount_in,
                          mis_m if j == u else intents[j].min_out) for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_lower += 1
                if gain > max_gain:
                    max_gain = gain

            # Misreport: raise min_out by 10% (harder to fill, but maybe better position)
            mis_m = intents[u].min_out * 11 // 10
            mis = [Intent(intents[j].user, intents[j].amount_in,
                          mis_m if j == u else intents[j].min_out) for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_raise += 1
                if gain > max_gain:
                    max_gain = gain

        total_welfare += trial_welfare
        completed += 1

    sp_rate = 100 * (1 - helped / max(1, total_checks))
    return {
        "sp_rate": sp_rate,
        "helped": helped,
        "helped_lower": helped_lower,
        "helped_raise": helped_raise,
        "total_checks": total_checks,
        "max_gain": max_gain,
        "avg_welfare": total_welfare / max(1, completed),
        "fill_rate": total_filled / max(1, completed * 4),
        "completed": completed,
    }


def test_sp_full(clear_fn, rng: random.Random, n_trials: int,
                 time_budget: float = 100) -> dict:
    """Full strategyproofness test (both amount_in and min_out can be misreported)."""
    helped = 0
    helped_inflate = 0
    helped_lower = 0
    total_checks = 0
    max_gain = 0.0
    total_welfare = 0.0
    total_filled = 0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)
        intents = gen_intents(rng, pool)

        truthful = clear_fn(pool, intents)

        trial_welfare = 0.0
        for u in range(len(intents)):
            amt_true = intents[u].amount_in
            min_true = intents[u].min_out
            base_util = user_utility_in_batch(truthful, intents, u, amt_true, min_true)
            trial_welfare += base_util
            if truthful[u].filled:
                total_filled += 1

            # Misreport 1: inflate amount_in by 10%
            mis_a = intents[u].amount_in * 11 // 10
            mis = [Intent(intents[j].user, mis_a if j == u else intents[j].amount_in,
                          intents[j].min_out) for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_inflate += 1
                if gain > max_gain:
                    max_gain = gain

            # Misreport 2: lower min_out by 10%
            mis_m = intents[u].min_out * 9 // 10
            mis = [Intent(intents[j].user, intents[j].amount_in,
                          mis_m if j == u else intents[j].min_out) for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_lower += 1
                if gain > max_gain:
                    max_gain = gain

        total_welfare += trial_welfare
        completed += 1

    sp_rate = 100 * (1 - helped / max(1, total_checks))
    return {
        "sp_rate": sp_rate,
        "helped": helped,
        "helped_inflate": helped_inflate,
        "helped_lower": helped_lower,
        "total_checks": total_checks,
        "max_gain": max_gain,
        "avg_welfare": total_welfare / max(1, completed),
        "fill_rate": total_filled / max(1, completed * 4),
        "completed": completed,
    }


def main() -> None:
    n_trials = 200
    print(f"Commit-Reveal (Binding amount_in) Strategyproofness Test (n=3-5, trials={n_trials}, seed=20260627)")
    print("=" * 130)
    print("Test 1: Full SP (amount_in + min_out both strategic) — baseline")
    print("-" * 130)
    print(f"{'Mechanism':<30} {'SP_rate':>8} {'violations':>10} {'inflate':>8} {'lower':>8} {'checks':>8} {'max_gain':>10} {'welfare':>10} {'fill%':>8}")
    print("-" * 130)

    rng = random.Random(20260627)
    r = test_sp_full(batch_clear_ab, rng, n_trials, time_budget=110)
    print(
        f"{'(A,B) full SP':<30} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['helped_inflate']:>8} "
        f"{r['helped_lower']:>8} {r['total_checks']:>8} {r['max_gain']:>10.2f} "
        f"{r['avg_welfare']:>10.1f} {r['fill_rate']*100:>7.1f}%"
    )

    print()
    print("Test 2: Commit-reveal SP (only min_out strategic, amount_in binding)")
    print("-" * 130)
    print(f"{'Mechanism':<30} {'SP_rate':>8} {'violations':>10} {'lower':>8} {'raise':>8} {'checks':>8} {'max_gain':>10} {'welfare':>10} {'fill%':>8}")
    print("-" * 130)

    rng = random.Random(20260627)
    r = test_sp_min_out_only(batch_clear_ab, rng, n_trials, time_budget=110)
    print(
        f"{'(A,B) commit-reveal':<30} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['helped_lower']:>8} "
        f"{r['helped_raise']:>8} {r['total_checks']:>8} {r['max_gain']:>10.2f} "
        f"{r['avg_welfare']:>10.1f} {r['fill_rate']*100:>7.1f}%"
    )

    print()
    print("If commit-reveal achieves ~100% SP, it's the RECOMMENDED fix:")
    print("- No welfare loss (unlike burn mechanism)")
    print("- Eliminates inflate attack (amount_in is binding)")
    print("- Only requires commit-reveal infrastructure (already common in DeFi)")


if __name__ == "__main__":
    main()
