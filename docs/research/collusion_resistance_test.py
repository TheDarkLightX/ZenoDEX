"""Collusion resistance test for various commit-reveal variants.

The targeted search found that commit-reveal + fixed ordering is NOT
collusion-proof (22.5% trial-level violation rate = 77.5% trial-level SP).
User A can sacrifice themselves by raising min_out to not fill, benefiting
user B.

This script tests:
1. (A,B) optimal ordering + commit-reveal (amount_in binding)
   - Does the optimizer prevent the sacrifice attack?
2. Burn mechanism + commit-reveal + fixed ordering
   - Does taxing B's gain prevent the collusion?
3. (A,B) + commit-reveal + burn
   - Combined approach

Note: CR (both params) prevents ADAPTIVE attacks but NOT precommit collusion.
See precommit_collusion_test.py for the precommit sacrifice attack against
CR (both params), which has a 42.1% trial-level violation rate via
off-protocol side payments. CR (both params) is NOT included in this
script because it has no adaptive dimension to test.
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


def true_rate(amt: int, min_out: int) -> float:
    return min_out / amt if amt > 0 else 0.0


def user_utility(paid: int, out: int, amt_true: int, min_true: int) -> float:
    return out - paid * true_rate(amt_true, min_true)


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


# ---------- Mechanisms ----------

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


def execute_fixed_order_burn(pool: Pool, intents: list[Intent], burn_pct: int) -> list[ExecResult]:
    """Fixed order with burn: burn_pct of output is burned (not given to user)."""
    xr, yr, fee = pool.x, pool.y, pool.fee_bps
    execs = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]
    for i in range(len(intents)):
        d = intents[i].amount_in
        min_out = intents[i].min_out
        out = q(xr, yr, d, fee)
        user_out = out * (100 - burn_pct) // 100
        if user_out >= min_out and d > 0:
            execs[i] = ExecResult(i, True, d, user_out, user_out - min_out)
            f = fee_calc(d, fee)
            xr = xr + d - f
            yr = yr - out  # full output removed from pool
    return execs


def batch_clear_ab(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
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


def batch_clear_ab_burn(pool: Pool, intents: list[Intent], burn_pct: int) -> list[ExecResult]:
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
            user_out = out * (100 - burn_pct) // 100
            if user_out >= min_out and d > 0:
                total_vol += d
                total_surplus += user_out - min_out
                execs[i] = ExecResult(i, True, d, user_out, user_out - min_out)
                f = fee_calc(d, fee)
                xr = xr + d - f
                yr = yr - out
        key = (total_vol, total_surplus)
        if key > best_key:
            best_key = key
            best_execs = execs
    return best_execs


# ---------- Collusion test (targeted: sacrifice attack) ----------

def test_collusion_targeted(clear_fn, rng: random.Random, n_trials: int,
                            time_budget: float, n_users: int = 2) -> dict:
    """Targeted collusion test: user A raises min_out to not fill,
    benefiting user B. Tests aggressive min_out raising."""
    helped_checks = 0
    total_checks = 0
    helped_trials = 0
    total_trials = 0
    max_gain = 0.0
    total_welfare = 0.0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(1_000, 100_000)
        y = rng.randint(1_000, 100_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)

        # Generate 2 users: A (small) and B (large)
        a_amt = rng.randint(10, 200)
        b_amt = rng.randint(500, 5000)
        a_out = q(pool.x, pool.y, a_amt, fee)
        if a_out <= 1:
            continue
        a_min = rng.randint(a_out * 50 // 100, a_out * 95 // 100)
        b_out_with_a = q(pool.x + a_amt - fee_calc(a_amt, fee),
                         pool.y - a_out, b_amt, fee)
        if b_out_with_a <= 1:
            continue
        b_min = rng.randint(b_out_with_a * 50 // 100, b_out_with_a * 95 // 100)

        intents = [Intent(0, a_amt, a_min), Intent(1, b_amt, b_min)]
        truths = {0: (a_amt, a_min), 1: (b_amt, b_min)}

        truthful = clear_fn(pool, intents)
        base_group = group_utility(truthful, intents, {0, 1}, truths)
        total_welfare += base_group

        # Sacrifice attack: A raises min_out to not fill
        # Try multiple levels: just above output, 2x output, 10x output
        trial_helped = False
        for factor in [1.01, 1.1, 1.5, 2.0, 10.0]:
            mis_a_min = int(a_out * factor)
            mis = [Intent(0, a_amt, mis_a_min), Intent(1, b_amt, b_min)]
            res = clear_fn(pool, mis)
            gain = group_utility(res, mis, {0, 1}, truths) - base_group
            total_checks += 1
            if gain > 1e-9:
                helped_checks += 1
                trial_helped = True
                if gain > max_gain:
                    max_gain = gain

        total_trials += 1
        if trial_helped:
            helped_trials += 1
        completed += 1

    return {
        "sp_rate_checks": 100 * (1 - helped_checks / max(1, total_checks)),
        "sp_rate_trials": 100 * (1 - helped_trials / max(1, total_trials)),
        "helped_checks": helped_checks,
        "helped_trials": helped_trials,
        "total_checks": total_checks,
        "total_trials": total_trials,
        "max_gain": max_gain,
        "avg_welfare": total_welfare / max(1, completed),
        "completed": completed,
    }


def main() -> None:
    print("Collusion Resistance Test: Sacrifice Attack")
    print("=" * 130)
    print("Attack: User A (small) raises min_out to not fill, benefiting User B (large)")
    print()
    print(f"{'Mechanism':<40} {'SP(trial)':>9} {'SP(check)':>9} {'viol(T)':>7} {'viol(C)':>7} {'trials':>7} {'checks':>7} {'max_gain':>10} {'welfare':>10}")
    print("-" * 130)

    mechanisms = [
        ("Fixed order + CR (amount_in)", lambda p, i: execute_fixed_order(p, i)),
        ("(A,B) + CR (amount_in)", lambda p, i: batch_clear_ab(p, i)),
        ("Fixed + CR + burn 10%", lambda p, i: execute_fixed_order_burn(p, i, 10)),
        ("Fixed + CR + burn 30%", lambda p, i: execute_fixed_order_burn(p, i, 30)),
        ("Fixed + CR + burn 50%", lambda p, i: execute_fixed_order_burn(p, i, 50)),
        ("(A,B) + CR + burn 10%", lambda p, i: batch_clear_ab_burn(p, i, 10)),
        ("(A,B) + CR + burn 30%", lambda p, i: batch_clear_ab_burn(p, i, 30)),
        ("(A,B) + CR + burn 50%", lambda p, i: batch_clear_ab_burn(p, i, 50)),
    ]

    for name, fn in mechanisms:
        rng = random.Random(20260627)
        r = test_collusion_targeted(fn, rng, 500, time_budget=90)
        print(
            f"{name:<40} {r['sp_rate_trials']:>8.1f}% {r['sp_rate_checks']:>8.1f}% "
            f"{r['helped_trials']:>7} {r['helped_checks']:>7} "
            f"{r['total_trials']:>7} {r['total_checks']:>7} "
            f"{r['max_gain']:>10.2f} {r['avg_welfare']:>10.1f}"
        )

    print()
    print("SP(trial) = % of trials where NO sacrifice factor helped the group")
    print("SP(check) = % of individual (trial, factor) checks with no gain")
    print("viol(T)   = trials where at least one sacrifice factor helped")
    print("viol(C)   = individual (trial, factor) checks with positive gain")
    print()
    print("Note: CR (both params) prevents adaptive attacks but NOT precommit")
    print("      collusion. See precommit_collusion_test.py for the precommit")
    print("      sacrifice attack (42.1% trial-level violation rate).")
    print("      Welfare is not directly comparable across burn levels.")


if __name__ == "__main__":
    main()
