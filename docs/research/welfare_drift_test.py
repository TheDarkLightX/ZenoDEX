"""Welfare impact of committing min_out before seeing pool state.

In the commit-reveal (both params) protocol, users commit both amount_in
and min_out BEFORE the batch is revealed. In practice, users observe the
pool state to set min_out (e.g., min_out = 95% of expected output).

If the pool state changes between commitment and settlement (e.g., other
batches settle first, or LPs add/remove liquidity), the committed min_out
might be:
- Too high: trade doesn't fill (welfare loss)
- Too low: user gets a worse price (welfare loss)
- Just right: trade fills at a good price (no loss)

This script simulates pool state uncertainty and measures the welfare impact.

Test setup:
1. User observes pool state S0 and sets min_out = f(S0) (e.g., 95% of expected output)
2. Pool state changes to S1 (random drift) before settlement
3. Batch settles at S1 with the committed min_out
4. Compare welfare to the counterfactual where user sets min_out at S1

Drift model: pool reserves change by ±delta% between observation and settlement.
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
                  truths: dict[int, tuple[int, int]]) -> float:
    util = 0.0
    for ex in execs:
        amt_true, min_true = truths[intents[ex.idx].user]
        paid = ex.amount_in if ex.filled else 0
        out = ex.actual_out if ex.filled else 0
        util += user_utility(paid, out, amt_true, min_true)
    return util


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


def gen_intents_at_pool(rng: random.Random, pool: Pool, n: int,
                        min_out_pct: int) -> list[Intent]:
    """Generate intents where min_out = min_out_pct% of expected output at pool."""
    intents = []
    for u in range(n):
        d = rng.randint(50, 500)
        out = q(pool.x, pool.y, d, pool.fee_bps)
        min_out = out * min_out_pct // 100
        intents.append(Intent(user=u, amount_in=d, min_out=min_out))
    return intents


def drift_pool(rng: random.Random, pool: Pool, drift_pct: int) -> Pool:
    """Drift pool reserves by ±drift_pct%."""
    dx = pool.x * rng.randint(-drift_pct, drift_pct) // 100
    dy = pool.y * rng.randint(-drift_pct, drift_pct) // 100
    return Pool(max(100, pool.x + dx), max(100, pool.y + dy), pool.fee_bps)


def test_welfare_with_drift(rng: random.Random, n_trials: int,
                            drift_pct: int, min_out_pct: int,
                            n_users: int = 3) -> dict:
    """Test welfare impact of committing min_out before pool drift.

    Scenario:
    1. User observes pool S0, sets min_out = min_out_pct% of output at S0
    2. Pool drifts to S1 (±drift_pct%)
    3. Batch settles at S1 with committed min_out
    4. Compare to counterfactual: user sets min_out at S1
    """
    total_welfare_committed = 0.0
    total_welfare_counterfactual = 0.0
    total_filled_committed = 0
    total_filled_counterfactual = 0
    completed = 0

    for _ in range(n_trials):
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool_s0 = Pool(x, y, fee)
        pool_s1 = drift_pool(rng, pool_s0, drift_pct)

        # User sets min_out based on S0
        intents_committed = gen_intents_at_pool(rng, pool_s0, n_users, min_out_pct)
        truths = {intents_committed[i].user: (intents_committed[i].amount_in,
                                               intents_committed[i].min_out)
                  for i in range(len(intents_committed))}

        # Settle at S1 with committed min_out
        result_committed = batch_clear_ab(pool_s1, intents_committed)
        welfare_committed = group_utility(result_committed, intents_committed, truths)
        filled_committed = sum(1 for r in result_committed if r.filled)

        # Counterfactual: user sets min_out at S1 (deterministic, same amount_in)
        # Compute min_out as min_out_pct% of expected output at S1 for each user
        intents_counterfactual = [
            Intent(intents_committed[i].user,
                   intents_committed[i].amount_in,
                   q(pool_s1.x, pool_s1.y, intents_committed[i].amount_in, pool_s1.fee_bps)
                   * min_out_pct // 100)
            for i in range(len(intents_committed))
        ]
        result_counterfactual = batch_clear_ab(pool_s1, intents_counterfactual)
        welfare_counterfactual = group_utility(result_counterfactual, intents_counterfactual, truths)
        filled_counterfactual = sum(1 for r in result_counterfactual if r.filled)

        # Identity check at drift=0: committed and counterfactual must match
        if drift_pct == 0:
            assert abs(welfare_committed - welfare_counterfactual) < 1e-9, \
                f"Identity check failed at drift=0: {welfare_committed} vs {welfare_counterfactual}"
            assert filled_committed == filled_counterfactual, \
                f"Fill rate identity check failed at drift=0"

        total_welfare_committed += welfare_committed
        total_welfare_counterfactual += welfare_counterfactual
        total_filled_committed += filled_committed
        total_filled_counterfactual += filled_counterfactual
        completed += 1

    return {
        "drift_pct": drift_pct,
        "min_out_pct": min_out_pct,
        "welfare_committed": total_welfare_committed / max(1, completed),
        "welfare_counterfactual": total_welfare_counterfactual / max(1, completed),
        "welfare_ratio": total_welfare_committed / max(1, total_welfare_counterfactual),
        "fill_rate_committed": total_filled_committed / max(1, completed * n_users),
        "fill_rate_counterfactual": total_filled_counterfactual / max(1, completed * n_users),
        "completed": completed,
    }


def main() -> None:
    print("Welfare Impact of Committing min_out Before Pool Drift")
    print("=" * 130)
    print("Scenario: User observes pool S0, commits min_out = X% of output at S0.")
    print("Pool drifts ±D% to S1. Batch settles at S1 with committed min_out.")
    print("Counterfactual: user sets min_out at S1 (no commit-reveal for min_out).")
    print()
    print(f"{'Drift%':>7} {'min_out%':>9} {'Welfare(comm)':>14} {'Welfare(cf)':>12} {'Ratio':>7} {'Fill%(comm)':>12} {'Fill%(cf)':>10} {'Trials':>8}")
    print("-" * 130)

    for drift_pct in [0, 1, 2, 5, 10, 20, 50]:
        for min_out_pct in [50, 75, 90, 95]:
            rng = random.Random(20260627)
            r = test_welfare_with_drift(rng, 200, drift_pct, min_out_pct)
            print(
                f"{r['drift_pct']:>6}% {r['min_out_pct']:>8}% "
                f"{r['welfare_committed']:>14.1f} {r['welfare_counterfactual']:>12.1f} "
                f"{r['welfare_ratio']:>6.3f} {r['fill_rate_committed']*100:>11.1f}% "
                f"{r['fill_rate_counterfactual']*100:>9.1f}% {r['completed']:>8}"
            )
        print()

    print()
    print("Key: Ratio = welfare(committed) / welfare(counterfactual)")
    print("      Ratio = 1.000 means no welfare loss from committing min_out early")
    print("      Ratio < 1 means welfare loss from stale min_out")
    print()
    print("If ratio is close to 1 for small drift (1-5%), the commit-reveal (both params)")
    print("mechanism has negligible welfare cost in practice (pool state changes little")
    print("between blocks).")


if __name__ == "__main__":
    main()
