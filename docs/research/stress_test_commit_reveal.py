"""Stress test for commit-reveal + fixed ordering mechanism.

The Lean proof (CommitRevealStrategyproof.lean) proves single-user SP:
with fixed ordering and binding amount_in, no single user can profit by
misreporting min_out. But real-world attacks may involve:

1. Multi-user collusion: a group of users coordinate their min_out reports
2. Larger batches (n=6-10): more users means more ordering interactions
3. Extreme parameters: very small/large pools, very high/low fees
4. Adaptive attacks: attacker observes other bids and optimizes response
5. Combined attacks: lower min_out for some users, raise for others

This script tests all these scenarios.
"""
from __future__ import annotations

import random
import time
from dataclasses import dataclass, replace


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


def true_rate(amt: int, min_out: int) -> float:
    return min_out / amt if amt > 0 else 0.0


def user_utility(paid: int, out: int, amt_true: int, min_true: int) -> float:
    return out - paid * true_rate(amt_true, min_true)


def execute_fixed_order(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    xr, yr, fee = pool.x, pool.y, pool.fee_bps
    execs = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]
    for i in range(len(intents)):
        d = intents[i].amount_in
        min_out = intents[i].min_out
        out = q(xr, yr, d, fee)
        if out >= min_out and d > 0:
            execs[i] = ExecResult(i, True, d, out, out - min_out)
            f = fee_calc(d, fee)
            xr = xr + d - f
            yr = yr - out
    return execs


def batch_clear_ab(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    import itertools
    n = len(intents)
    if n == 0:
        return []
    best_key = (-1, -1)
    best_execs = []
    for perm in itertools.permutations(range(n)):
        xr, yr, fee = pool.x, pool.y, pool.fee_bps
        total_vol, total_surplus = 0, 0
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


def group_utility(execs: list[ExecResult], intents: list[Intent],
                  users: set[int], truths: dict[int, tuple[int, int]]) -> float:
    util = 0.0
    for ex in execs:
        if intents[ex.idx].user not in users:
            continue
        amt_true, min_true = truths[intents[ex.idx].user]
        paid = ex.amount_in if ex.filled else 0
        out = ex.actual_out if ex.filled else 0
        util += user_utility(paid, out, amt_true, min_true)
    return util


def gen_intents(rng: random.Random, pool: Pool, n: int) -> list[Intent]:
    intents = []
    for u in range(n):
        d = rng.randint(50, 500)
        out = q(pool.x, pool.y, d, pool.fee_bps)
        lo = max(1, out * 50 // 100)
        hi = max(lo + 1, out * 95 // 100)
        min_out = rng.randint(lo, hi)
        intents.append(Intent(user=u, amount_in=d, min_out=min_out))
    return intents


def gen_extreme_intents(rng: random.Random, pool: Pool, n: int) -> list[Intent]:
    """Generate intents with extreme min_out values (1% to 99% of output)."""
    intents = []
    for u in range(n):
        d = rng.randint(10, 1000)
        out = q(pool.x, pool.y, d, pool.fee_bps)
        lo = max(1, out * 1 // 100)
        hi = max(lo + 1, out * 99 // 100)
        min_out = rng.randint(lo, hi)
        intents.append(Intent(user=u, amount_in=d, min_out=min_out))
    return intents


def gen_extreme_pool(rng: random.Random) -> Pool:
    """Generate pools with extreme parameters."""
    x = rng.choice([1000, 5000, 10000, 50000, 100000, 500000, 1_000_000, 10_000_000])
    y = rng.choice([1000, 5000, 10000, 50000, 100000, 500000, 1_000_000, 10_000_000])
    fee = rng.choice([0, 1, 3, 10, 30, 100, 300, 1000, 3000])
    return Pool(x, y, fee)


# ---------- Test 1: Single-user SP with larger batches ----------

def test_single_user_sp(clear_fn, rng: random.Random, n_trials: int, n_users: int,
                        time_budget: float, extreme: bool = False) -> dict:
    helped = 0
    total_checks = 0
    max_gain = 0.0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        if extreme:
            pool = gen_extreme_pool(rng)
            intents = gen_extreme_intents(rng, pool, n_users)
        else:
            x = rng.randint(50_000, 500_000)
            y = rng.randint(50_000, 500_000)
            fee = rng.choice([0, 10, 30, 100, 300])
            pool = Pool(x, y, fee)
            intents = gen_intents(rng, pool, n_users)

        truthful = clear_fn(pool, intents)
        truths = {intents[i].user: (intents[i].amount_in, intents[i].min_out)
                  for i in range(len(intents))}

        for u in range(len(intents)):
            amt_true, min_true = truths[u]
            base_util = group_utility(truthful, intents, {u}, truths)

            # Try 5 misreport levels: 50%, 75%, 90%, 110%, 125%, 200%
            for factor_num, factor_den in [(1,2), (3,4), (9,10), (11,10), (5,4), (2,1)]:
                mis_m = intents[u].min_out * factor_num // factor_den
                if mis_m < 0:
                    mis_m = 0
                mis = [Intent(intents[j].user, intents[j].amount_in,
                              mis_m if j == u else intents[j].min_out)
                       for j in range(len(intents))]
                res = clear_fn(pool, mis)
                gain = group_utility(res, mis, {u}, truths) - base_util
                total_checks += 1
                if gain > 1e-9:
                    helped += 1
                    if gain > max_gain:
                        max_gain = gain

        completed += 1

    return {
        "sp_rate": 100 * (1 - helped / max(1, total_checks)),
        "helped": helped,
        "total_checks": total_checks,
        "max_gain": max_gain,
        "completed": completed,
    }


# ---------- Test 2: Multi-user collusion ----------

def test_collusion_sp(clear_fn, rng: random.Random, n_trials: int, n_users: int,
                      time_budget: float) -> dict:
    """Test if a group of colluding users can profit by coordinating min_out reports."""
    helped = 0
    total_checks = 0
    max_gain = 0.0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)
        intents = gen_intents(rng, pool, n_users)

        truthful = clear_fn(pool, intents)
        truths = {intents[i].user: (intents[i].amount_in, intents[i].min_out)
                  for i in range(len(intents))}

        # Collusion group: first half of users coordinate
        colluders = set(range(n_users // 2))
        base_group_util = group_utility(truthful, intents, colluders, truths)

        # Try coordinated misreport: all colluders lower min_out by 10%
        mis = list(intents)
        for j in range(len(intents)):
            if intents[j].user in colluders:
                mis[j] = Intent(intents[j].user, intents[j].amount_in,
                                intents[j].min_out * 9 // 10)
        res = clear_fn(pool, mis)
        gain = group_utility(res, mis, colluders, truths) - base_group_util
        total_checks += 1
        if gain > 1e-9:
            helped += 1
            if gain > max_gain:
                max_gain = gain

        # Try coordinated misreport: all colluders raise min_out by 10%
        mis = list(intents)
        for j in range(len(intents)):
            if intents[j].user in colluders:
                mis[j] = Intent(intents[j].user, intents[j].amount_in,
                                intents[j].min_out * 11 // 10)
        res = clear_fn(pool, mis)
        gain = group_utility(res, mis, colluders, truths) - base_group_util
        total_checks += 1
        if gain > 1e-9:
            helped += 1
            if gain > max_gain:
                max_gain = gain

        # Try mixed: first half of colluders lower, second half raise
        colluder_list = sorted(colluders)
        half = len(colluder_list) // 2
        mis = list(intents)
        for j in range(len(intents)):
            if intents[j].user in colluders:
                idx = colluder_list.index(intents[j].user)
                if idx < half:
                    mis[j] = Intent(intents[j].user, intents[j].amount_in,
                                    intents[j].min_out * 9 // 10)
                else:
                    mis[j] = Intent(intents[j].user, intents[j].amount_in,
                                    intents[j].min_out * 11 // 10)
        res = clear_fn(pool, mis)
        gain = group_utility(res, mis, colluders, truths) - base_group_util
        total_checks += 1
        if gain > 1e-9:
            helped += 1
            if gain > max_gain:
                max_gain = gain

        completed += 1

    return {
        "sp_rate": 100 * (1 - helped / max(1, total_checks)),
        "helped": helped,
        "total_checks": total_checks,
        "max_gain": max_gain,
        "completed": completed,
    }


# ---------- Test 3: Adaptive attack (best response) ----------

def test_adaptive_attack(clear_fn, rng: random.Random, n_trials: int, n_users: int,
                         time_budget: float) -> dict:
    """Test if an attacker can find ANY profitable misreport by exhaustive search
    over min_out levels. This simulates an adaptive attacker who observes other
    bids and optimizes their response."""
    helped = 0
    total_checks = 0
    max_gain = 0.0
    completed = 0

    # min_out levels to try (as fraction of truthful min_out)
    levels = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.5, 2.0, 0.01, 0.99]

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)
        intents = gen_intents(rng, pool, n_users)

        truthful = clear_fn(pool, intents)
        truths = {intents[i].user: (intents[i].amount_in, intents[i].min_out)
                  for i in range(len(intents))}

        for u in range(len(intents)):
            amt_true, min_true = truths[u]
            base_util = group_utility(truthful, intents, {u}, truths)

            best_gain = 0.0
            for level in levels:
                mis_m = max(0, int(intents[u].min_out * level))
                mis = [Intent(intents[j].user, intents[j].amount_in,
                              mis_m if j == u else intents[j].min_out)
                       for j in range(len(intents))]
                res = clear_fn(pool, mis)
                gain = group_utility(res, mis, {u}, truths) - base_util
                if gain > best_gain:
                    best_gain = gain

            total_checks += 1
            if best_gain > 1e-9:
                helped += 1
                if best_gain > max_gain:
                    max_gain = best_gain

        completed += 1

    return {
        "sp_rate": 100 * (1 - helped / max(1, total_checks)),
        "helped": helped,
        "total_checks": total_checks,
        "max_gain": max_gain,
        "completed": completed,
    }


def main() -> None:
    print("Commit-Reveal + Fixed Ordering: Stress Test")
    print("=" * 120)
    print()

    # Test 1: Single-user SP with larger batches
    print("Test 1: Single-user SP (6 misreport levels, standard params)")
    print("-" * 120)
    print(f"{'Mechanism':<30} {'n':>4} {'SP_rate':>8} {'violations':>10} {'checks':>8} {'max_gain':>10} {'trials':>8}")
    print("-" * 120)

    for n in [3, 5, 7, 10]:
        rng = random.Random(20260627)
        r = test_single_user_sp(execute_fixed_order, rng, 200, n, time_budget=60)
        print(f"{'Fixed order (n=' + str(n) + ')':<30} {n:>4} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['total_checks']:>8} {r['max_gain']:>10.2f} {r['completed']:>8}")

    print()

    # Test 2: Extreme parameters
    print("Test 2: Single-user SP (extreme params: pools 1K-10M, fees 0-30%, min_out 1-99%)")
    print("-" * 120)
    print(f"{'Mechanism':<30} {'n':>4} {'SP_rate':>8} {'violations':>10} {'checks':>8} {'max_gain':>10} {'trials':>8}")
    print("-" * 120)

    for n in [3, 5, 7]:
        rng = random.Random(20260627)
        r = test_single_user_sp(execute_fixed_order, rng, 200, n, time_budget=60, extreme=True)
        print(f"{'Fixed order ext (n=' + str(n) + ')':<30} {n:>4} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['total_checks']:>8} {r['max_gain']:>10.2f} {r['completed']:>8}")

    print()

    # Test 3: Multi-user collusion
    print("Test 3: Multi-user collusion (coordinated min_out misreport)")
    print("-" * 120)
    print(f"{'Mechanism':<30} {'n':>4} {'SP_rate':>8} {'violations':>10} {'checks':>8} {'max_gain':>10} {'trials':>8}")
    print("-" * 120)

    for n in [4, 6, 8, 10]:
        rng = random.Random(20260627)
        r = test_collusion_sp(execute_fixed_order, rng, 200, n, time_budget=60)
        print(f"{'Collusion (n=' + str(n) + ')':<30} {n:>4} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['total_checks']:>8} {r['max_gain']:>10.2f} {r['completed']:>8}")

    print()

    # Test 4: Adaptive attack (exhaustive min_out search)
    print("Test 4: Adaptive attack (12 min_out levels, best response)")
    print("-" * 120)
    print(f"{'Mechanism':<30} {'n':>4} {'SP_rate':>8} {'violations':>10} {'checks':>8} {'max_gain':>10} {'trials':>8}")
    print("-" * 120)

    for n in [3, 5, 7]:
        rng = random.Random(20260627)
        r = test_adaptive_attack(execute_fixed_order, rng, 200, n, time_budget=90)
        print(f"{'Adaptive (n=' + str(n) + ')':<30} {n:>4} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['total_checks']:>8} {r['max_gain']:>10.2f} {r['completed']:>8}")

    print()
    print("If all tests show 100% SP, the commit-reveal + fixed ordering mechanism")
    print("is robust to collusion, adaptive attacks, and extreme parameters.")


if __name__ == "__main__":
    main()
