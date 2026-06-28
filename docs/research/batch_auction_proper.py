"""Proper batch auction (CoWSwap-style) strategyproofness test.

The key insight: in a proper batch auction, the clearing price is determined by
the intersection of supply and demand, NOT by ordering. All filled trades get
the same price. Inflating amount_in doesn't change the clearing price (for
small inflations), so there's no incentive to misreport.

Previous UCP test was flawed because it still used (A,B) ordering to decide
which trades to include. A proper batch auction:

1. Each user submits (amount_in, min_out) = (max input, min output)
2. The mechanism finds the uniform clearing price P* = max price such that
   total output at P* >= sum of min_out for all willing traders
3. All trades with min_out/amount_in >= P* are filled at P*
4. Each filled trade gets output = amount_in * P*

This should be strategyproof because:
- Inflating amount_in doesn't change your price limit (min_out/amount_in decreases)
- Lowering min_out makes you easier to fill but doesn't change the clearing price
- The only way to profit is to change the clearing price, which requires a
  large enough bid to move the market
"""
from __future__ import annotations

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


# ---------- Proper batch auction ----------

def batch_auction_uniform(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    """Proper batch auction with uniform clearing price.

    Algorithm:
    1. Sort users by price limit (min_out / amount_in) descending
    2. For each prefix of k users, compute the uniform price if all k trade:
       - Total input = sum of amount_in for first k users
       - Total output = q(pool, total_input)
       - Uniform price = total_output / total_input
    3. Find the largest k where uniform price >= min_out/amount_in for all k users
    4. All k users get output = amount_in * uniform_price
    """
    n = len(intents)
    if n == 0:
        return []

    # Sort by price limit (min_out / amount_in) descending
    # Use cross-multiplication to avoid floats: a.min_out * b.amount_in > b.min_out * a.amount_in
    indexed = list(enumerate(intents))
    indexed.sort(key=lambda pair: (-pair[1].min_out * 1000000 // pair[1].amount_in, pair[0]))

    # Try each prefix size k = n, n-1, ..., 1
    for k in range(n, 0, -1):
        prefix = indexed[:k]
        total_in = sum(intent.amount_in for _, intent in prefix)
        total_out = q(pool.x, pool.y, total_in, pool.fee_bps)
        if total_in <= 0 or total_out <= 0:
            continue

        # Uniform price (as integer ratio: total_out / total_in)
        # Check all k users meet their min_out at this price
        all_ok = True
        for _, intent in prefix:
            user_out = (total_out * intent.amount_in) // total_in
            if user_out < intent.min_out:
                all_ok = False
                break

        if all_ok:
            # Fill these k users at uniform price
            results = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(n)]
            remaining = total_out
            for j, (idx, intent) in enumerate(prefix):
                if j == k - 1:
                    out = remaining
                else:
                    out = (total_out * intent.amount_in) // total_in
                    remaining -= out
                results[idx] = ExecResult(idx, True, intent.amount_in, out, out - intent.min_out)
            return results

    # No trades can be filled
    return [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(n)]


# ---------- (A,B) baseline for comparison ----------

def batch_clear_ab(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    import itertools

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


# ---------- Strategyproofness test ----------

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


def test_strategyproofness(clear_fn, rng: random.Random, n_trials: int,
                           time_budget: float = 100) -> dict:
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
        "fill_rate": total_filled / max(1, completed * 4),  # avg 4 intents/trial
        "completed": completed,
    }


def main() -> None:
    n_trials = 100
    print(f"Proper Batch Auction Strategyproofness Test (n=3-5, trials={n_trials}, seed=20260627)")
    print("=" * 120)
    print(f"{'Mechanism':<25} {'SP_rate':>8} {'violations':>10} {'inflate':>8} {'lower':>8} {'checks':>8} {'max_gain':>10} {'welfare':>10} {'fill%':>8}")
    print("-" * 120)

    mechanisms = [
        ("(A,B) baseline", batch_clear_ab),
        ("Proper batch auction", batch_auction_uniform),
    ]

    for name, fn in mechanisms:
        rng = random.Random(20260627)
        r = test_strategyproofness(fn, rng, n_trials, time_budget=110)
        print(
            f"{name:<25} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['helped_inflate']:>8} "
            f"{r['helped_lower']:>8} {r['total_checks']:>8} {r['max_gain']:>10.2f} "
            f"{r['avg_welfare']:>10.1f} {r['fill_rate']*100:>7.1f}%"
        )

    print()
    print("If the proper batch auction achieves ~100% SP rate, it's the recommended fix")
    print("(no welfare loss unlike the burn mechanism).")


if __name__ == "__main__":
    main()
