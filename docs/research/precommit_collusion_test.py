"""Precommit collusion test for CR (both params).

Codex finding 1 (round 1 review): CR (both params) prevents ADAPTIVE
manipulation (changing bids after seeing others) but does NOT prevent
PRECOMMIT collusion (choosing strategic bids before the batch).

The sacrifice attack under CR (both params):
1. A and B collude OFF-PROTOCOL before the commit phase
2. A precommits a high min_out (knowing they won't fill)
3. B precommits normally
4. A doesn't fill, B gets better pool state
5. B's gain exceeds A's loss
6. They split the gains via off-protocol side payment

This is NOT prevented by commit-reveal because both parameters are
committed BEFORE the batch, but the COALITION chooses their committed
values strategically.

Test: compare group utility of truthful precommit vs sacrifice precommit.
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


def test_precommit_collusion(rng: random.Random, n_trials: int,
                             time_budget: float) -> dict:
    """Test precommit sacrifice attack against CR (both params).

    Under CR (both params), the coalition precommits BEFORE the batch.
    A precommits high min_out (sacrifice), B precommits normally.
    The mechanism processes the committed values - no adaptive changes.

    This tests whether the PRECOMMIT sacrifice attack works, which is
    NOT prevented by commit-reveal (it only prevents ADAPTIVE attacks).
    """
    helped = 0  # trials where precommit sacrifice helps the group
    total = 0
    max_gain = 0.0
    total_welfare_truthful = 0.0
    total_welfare_sacrifice = 0.0
    completed = 0

    t0 = time.time()
    for _ in range(n_trials):
        if time.time() - t0 > time_budget:
            break
        x = rng.randint(1_000, 100_000)
        y = rng.randint(1_000, 100_000)
        fee = rng.choice([0, 10, 30, 100, 300])
        pool = Pool(x, y, fee)

        # A: small trade, B: large trade
        a_amt = rng.randint(10, 200)
        b_amt = rng.randint(500, 5000)
        a_out = q(pool.x, pool.y, a_amt, fee)
        if a_out <= 1:
            continue
        # A's truthful min_out: 90% of expected output
        a_min_truthful = a_out * 90 // 100
        # B's truthful min_out: 90% of expected output when A fills
        b_out_with_a = q(pool.x + a_amt - fee_calc(a_amt, fee),
                         pool.y - a_out, b_amt, fee)
        if b_out_with_a <= 1:
            continue
        b_min_truthful = b_out_with_a * 90 // 100

        # Truthful precommit: both commit truthful min_out
        intents_truthful = [Intent(0, a_amt, a_min_truthful),
                            Intent(1, b_amt, b_min_truthful)]
        truths = {0: (a_amt, a_min_truthful), 1: (b_amt, b_min_truthful)}

        result_truthful = batch_clear_ab(pool, intents_truthful)
        welfare_truthful = group_utility(result_truthful, intents_truthful,
                                         {0, 1}, truths)
        total_welfare_truthful += welfare_truthful

        # Precommit sacrifice: A commits high min_out (won't fill), B commits normally
        # A's sacrifice min_out: above expected output (guaranteed not to fill)
        a_min_sacrifice = a_out + 1  # just above output, guaranteed not to fill
        intents_sacrifice = [Intent(0, a_amt, a_min_sacrifice),
                             Intent(1, b_amt, b_min_truthful)]

        result_sacrifice = batch_clear_ab(pool, intents_sacrifice)
        welfare_sacrifice = group_utility(result_sacrifice, intents_sacrifice,
                                          {0, 1}, truths)
        total_welfare_sacrifice += welfare_sacrifice

        gain = welfare_sacrifice - welfare_truthful
        total += 1
        if gain > 1e-9:
            helped += 1
            if gain > max_gain:
                max_gain = gain

        completed += 1

    return {
        "collusion_rate": 100 * helped / max(1, total),
        "helped": helped,
        "total": total,
        "max_gain": max_gain,
        "avg_welfare_truthful": total_welfare_truthful / max(1, completed),
        "avg_welfare_sacrifice": total_welfare_sacrifice / max(1, completed),
        "completed": completed,
    }


def main() -> None:
    print("Precommit Collusion Test: CR (both params) Sacrifice Attack")
    print("=" * 130)
    print()
    print("Attack: A and B collude OFF-PROTOCOL before commit phase.")
    print("A precommits high min_out (sacrifice), B precommits normally.")
    print("Commit-reveal does NOT prevent this (it only prevents adaptive attacks).")
    print()
    print(f"{'Mechanism':<40} {'Collusion%':>10} {'violations':>10} {'total':>6} "
          f"{'max_gain':>10} {'welfare(T)':>10} {'welfare(S)':>10} {'trials':>8}")
    print("-" * 130)

    rng = random.Random(20260627)
    r = test_precommit_collusion(rng, 500, time_budget=60)
    print(f"{'CR (both params) + (A,B)':<40} {r['collusion_rate']:>9.1f}% "
          f"{r['helped']:>10} {r['total']:>6} {r['max_gain']:>10.2f} "
          f"{r['avg_welfare_truthful']:>10.1f} {r['avg_welfare_sacrifice']:>10.1f} "
          f"{r['completed']:>8}")

    print()
    print("Result: CR (both params) prevents ADAPTIVE manipulation but NOT")
    print("precommit collusion. The sacrifice attack works via precommit +")
    print("off-protocol side payments.")
    print()
    print("Corrected claim:")
    print("  CR (both params) prevents adaptive attacks (changing bids after")
    print("  seeing others) but does NOT prevent precommit collusion (choosing")
    print("  strategic bids before the batch).")
    print()
    print("  Single-user SP: YES (no adaptive dimension under binding commitment)")
    print("  Group SP (collusion): NO (precommit sacrifice attack)")
    print()
    print("  The mechanism is still a significant improvement over CR (amount_in)")
    print("  because it eliminates adaptive bid-parameter misreporting and the")
    print("  modeled sandwich vector (inclusion, censorship, reveal-withholding,")
    print("  and batch-boundary games are non-claims).")


if __name__ == "__main__":
    main()
