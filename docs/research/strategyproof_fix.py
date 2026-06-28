"""Strategyproofness fix investigation for ZenoDEX batch clearing.

Tests 4 alternative mechanisms to fix the 35.72% strategyproofness violation.
Uses quasilinear utility (actual_out - amount_in_paid * true_rate) with min_out
limits, matching the original mechanism_design.py methodology.

Mechanisms:
  1. (A,B) baseline (volume then surplus)
  2. B-only (surplus only)
  3. Uniform clearing price (UCP)
  4. Burn (fraction f of surplus burned)
  5. VCG payments
"""
from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass
from typing import Sequence


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


@dataclass(frozen=True)
class BatchResult:
    perm: tuple[int, ...]
    total_vol: int
    total_surplus: int
    execs: list[ExecResult]


def _simulate_perm(
    pool: Pool, intents: Sequence[Intent], perm: Sequence[int]
) -> tuple[int, int, list[ExecResult]]:
    x, y, fee = pool.x, pool.y, pool.fee_bps
    xr, yr = x, y
    total_vol = 0
    total_surplus = 0
    execs = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]
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
    return total_vol, total_surplus, execs


def batch_clear_ab(pool: Pool, intents: Sequence[Intent]) -> BatchResult:
    """(A,B) optimal: maximize (total_vol, total_surplus), tie-break lex smallest perm."""
    n = len(intents)
    if n == 0:
        return BatchResult((), 0, 0, [])
    best = None
    for perm in itertools.permutations(range(n)):
        vol, surp, execs = _simulate_perm(pool, intents, perm)
        key = (vol, surp)
        cand = (key, perm, vol, surp, execs)
        if best is None:
            best = cand
        elif key > best[0] or (key == best[0] and perm < best[1]):
            best = cand
    assert best is not None
    return BatchResult(best[1], best[2], best[3], best[4])


def batch_clear_b_only(pool: Pool, intents: Sequence[Intent]) -> BatchResult:
    """B-only: maximize total_surplus, tie-break lex smallest perm."""
    n = len(intents)
    if n == 0:
        return BatchResult((), 0, 0, [])
    best = None
    for perm in itertools.permutations(range(n)):
        vol, surp, execs = _simulate_perm(pool, intents, perm)
        key = (surp, vol)  # surplus first
        cand = (key, perm, vol, surp, execs)
        if best is None:
            best = cand
        elif key > best[0] or (key == best[0] and perm < best[1]):
            best = cand
    assert best is not None
    return BatchResult(best[1], best[2], best[3], best[4])


def batch_clear_ucp(pool: Pool, intents: Sequence[Intent]) -> BatchResult:
    """Uniform clearing price: all filled trades get pro-rated output at marginal price.

    Find the largest prefix (by some ordering) where all min_out constraints are met
    at the uniform price. We try all permutations and pick the one that fills the most
    volume with all min_out constraints satisfied at the uniform clearing price.
    """
    n = len(intents)
    if n == 0:
        return BatchResult((), 0, 0, [])

    best = None
    for perm in itertools.permutations(range(n)):
        # Try filling intents in this order, computing uniform price after each addition
        x, y, fee = pool.x, pool.y, pool.fee_bps
        filled_indices: list[int] = []
        total_in = 0
        execs = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(n)]

        for i in perm:
            d = intents[i].amount_in
            min_out = intents[i].min_out
            # Compute uniform price if we add this intent
            new_total_in = total_in + d
            fee_total = fee_calc(new_total_in, fee)
            net = new_total_in - fee_total
            if net <= 0:
                break
            total_out = (y * net) // (x + net)
            # Check all filled intents meet min_out at uniform price
            all_ok = True
            temp_execs = list(execs)
            remaining = total_out
            for j_idx, j in enumerate(filled_indices + [i]):
                if j_idx == len(filled_indices):
                    share = remaining
                else:
                    share = (total_out * intents[j].amount_in) // new_total_in
                    remaining -= share
                if share < intents[j].min_out:
                    all_ok = False
                    break
                temp_execs[j] = ExecResult(j, True, intents[j].amount_in, share, share - intents[j].min_out)
            if all_ok:
                filled_indices.append(i)
                total_in = new_total_in
                execs = temp_execs

        vol = sum(intents[i].amount_in for i in filled_indices)
        surp = sum(execs[i].surplus for i in filled_indices)
        key = (vol, surp)
        cand = (key, perm, vol, surp, execs)
        if best is None:
            best = cand
        elif key > best[0] or (key == best[0] and perm < best[1]):
            best = cand

    assert best is not None
    return BatchResult(best[1], best[2], best[3], best[4])


def batch_clear_burn(pool: Pool, intents: Sequence[Intent], burn_frac: float) -> BatchResult:
    """(A,B) allocation but user output reduced by burn_frac * surplus."""
    base = batch_clear_ab(pool, intents)
    new_execs = []
    for ex in base.execs:
        if ex.filled:
            burn = int(burn_frac * ex.surplus)
            new_out = ex.actual_out - burn
            new_execs.append(ExecResult(ex.idx, True, ex.amount_in, new_out, new_out - intents[ex.idx].min_out))
        else:
            new_execs.append(ex)
    return BatchResult(base.perm, base.total_vol, sum(e.surplus for e in new_execs if e.filled), new_execs)


def batch_clear_vcg(pool: Pool, intents: Sequence[Intent]) -> BatchResult:
    """VCG: (A,B) allocation, each user pays externality (others' surplus without - with)."""
    n = len(intents)
    full = batch_clear_ab(pool, intents)
    full_surplus = full.total_surplus

    new_execs = list(full.execs)
    for u in range(n):
        # Others' surplus without user u
        others = [intents[j] for j in range(n) if j != u]
        if others:
            others_result = batch_clear_ab(pool, others)
            others_surplus_without = others_result.total_surplus
        else:
            others_surplus_without = 0

        # Others' surplus with user u (in the full batch)
        others_surplus_with = full_surplus - (full.execs[u].surplus if full.execs[u].filled else 0)

        payment = max(0, others_surplus_without - others_surplus_with)
        if full.execs[u].filled:
            new_out = full.execs[u].actual_out - payment
            new_execs[u] = ExecResult(u, True, full.execs[u].amount_in, new_out, new_out - intents[u].min_out)

    return BatchResult(full.perm, full.total_vol, sum(e.surplus for e in new_execs if e.filled), new_execs)


# ---------- Utility ----------

def true_rate(amount_in_true: int, min_out_true: int) -> float:
    if amount_in_true <= 0:
        return 0.0
    return min_out_true / amount_in_true


def user_utility(amount_in_paid: int, actual_out: int, amount_in_true: int, min_out_true: int) -> float:
    rate = true_rate(amount_in_true, min_out_true)
    return actual_out - amount_in_paid * rate


def user_utility_in_batch(result: BatchResult, intents: Sequence[Intent], user: int,
                          amt_true: int, min_true: int) -> float:
    util = 0.0
    for ex in result.execs:
        if intents[ex.idx].user != user:
            continue
        paid = ex.amount_in if ex.filled else 0
        out = ex.actual_out if ex.filled else 0
        util += user_utility(paid, out, amt_true, min_true)
    return util


# ---------- Intent generation ----------

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


def misreport_inflate(intent: Intent) -> Intent:
    return Intent(intent.user, intent.amount_in * 11 // 10, intent.min_out)


def misreport_lower(intent: Intent) -> Intent:
    return Intent(intent.user, intent.amount_in, intent.min_out * 9 // 10)


# ---------- Strategyproofness test ----------

def test_sp_for_mechanism(
    clear_fn,
    rng: random.Random,
    n_trials: int,
    time_budget: float = 100,
) -> dict:
    helped = 0
    helped_inflate = 0
    helped_lower = 0
    total_checks = 0
    total_users = 0
    max_gain = 0.0
    total_welfare = 0.0
    total_budget = 0.0
    completed = 0

    t0 = time.time()
    for trial in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(50_000, 500_000)
        y = rng.randint(50_000, 500_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)
        intents = gen_intents(rng, pool)

        truthful = clear_fn(pool, intents)

        # Welfare = sum of user utilities at truthful reporting
        trial_welfare = 0.0
        for u in range(len(intents)):
            amt_true = intents[u].amount_in
            min_true = intents[u].min_out
            base_util = user_utility_in_batch(truthful, intents, u, amt_true, min_true)
            trial_welfare += base_util
            total_users += 1

            # Misreport 1: inflate amount_in
            mis = [misreport_inflate(intents[j]) if j == u else intents[j] for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_inflate += 1
                if gain > max_gain:
                    max_gain = gain

            # Misreport 2: lower min_out
            mis = [misreport_lower(intents[j]) if j == u else intents[j] for j in range(len(intents))]
            res = clear_fn(pool, mis)
            gain = user_utility_in_batch(res, mis, u, amt_true, min_true) - base_util
            total_checks += 1
            if gain > 1e-9:
                helped += 1
                helped_lower += 1
                if gain > max_gain:
                    max_gain = gain

        total_welfare += trial_welfare

        # Budget = sum of (full_ab_output - mechanism_output) for filled trades
        ab_result = batch_clear_ab(pool, intents)
        trial_budget = 0.0
        for i in range(len(intents)):
            ab_out = ab_result.execs[i].actual_out if ab_result.execs[i].filled else 0
            mech_out = truthful.execs[i].actual_out if truthful.execs[i].filled else 0
            trial_budget += ab_out - mech_out
        total_budget += trial_budget
        completed += 1

    sp_rate = 100 * (1 - helped / max(1, total_checks))
    return {
        "sp_rate": sp_rate,
        "helped": helped,
        "helped_inflate": helped_inflate,
        "helped_lower": helped_lower,
        "total_checks": total_checks,
        "total_users": total_users,
        "max_gain": max_gain,
        "avg_welfare": total_welfare / max(1, completed),
        "avg_budget": total_budget / max(1, completed),
        "completed": completed,
    }


def main() -> None:
    rng = random.Random(20260627)
    n_trials = 100

    mechanisms = [
        ("(A,B) baseline", batch_clear_ab),
        ("B-only", batch_clear_b_only),
        ("UCP", batch_clear_ucp),
        ("Burn 1%", lambda p, i: batch_clear_burn(p, i, 0.01)),
        ("Burn 5%", lambda p, i: batch_clear_burn(p, i, 0.05)),
        ("Burn 10%", lambda p, i: batch_clear_burn(p, i, 0.10)),
        ("Burn 50%", lambda p, i: batch_clear_burn(p, i, 0.50)),
        ("VCG", batch_clear_vcg),
    ]

    print(f"Strategyproofness Fix Investigation (n=3-5, trials={n_trials}, seed=20260627)")
    print("=" * 130)
    print(f"{'Mechanism':<18} {'SP_rate':>8} {'violations':>10} {'inflate':>8} {'lower':>8} {'checks':>8} {'max_gain':>10} {'welfare':>10} {'budget':>10} {'done':>6}")
    print("-" * 130)

    for name, fn in mechanisms:
        # Fresh RNG per mechanism for comparability
        rng = random.Random(20260627)
        r = test_sp_for_mechanism(fn, rng, n_trials, time_budget=110)
        print(
            f"{name:<18} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['helped_inflate']:>8} "
            f"{r['helped_lower']:>8} {r['total_checks']:>8} {r['max_gain']:>10.2f} "
            f"{r['avg_welfare']:>10.1f} {r['avg_budget']:>10.1f} {r['completed']:>6}"
        )

    print()
    print("Key: SP_rate = strategyproofness rate (higher is better, 100% = no misreporting helps)")
    print("     inflate = violations from inflating amount_in by 10%")
    print("     lower = violations from lowering min_out by 10%")
    print("     welfare = average total user utility per trial (quasilinear)")
    print("     budget = average output retained by mechanism vs (A,B) baseline")


if __name__ == "__main__":
    main()
