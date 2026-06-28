"""Posted-price mechanism investigation for ZenoDEX batch clearing.

Hypothesis: If the clearing price is exogenous (determined by an external oracle,
not by the batch's own bids), then users cannot profit by misreporting, because
their bid doesn't affect the price they get.

Three posted-price variants:

1. **TWAP posted price**: Use the pool's spot price before the batch as the
   clearing price. All filled trades get output = amount_in * P_twap. Trades
   with min_out/amount_in >= P_twap are filled.

2. **External oracle price**: Use an external price oracle (simulated as the
   pool's spot price +/- noise). Same filling rule.

3. **Previous-batch price**: Use the clearing price from the previous batch.
   This is the most realistic for a batch-based DEX.

Key question: Does an exogenous price eliminate the strategyproofness gap
WITHOUT sacrificing welfare?

Theoretical prediction:
- Inflating amount_in: User gets more output (amount_in * P) but pays more
  (amount_in * true_rate). Since P is fixed, utility = amount_in * (P - true_rate).
  If P > true_rate, the user profits from inflating, but they would have profited
  anyway. The KEY question is whether inflating changes WHICH trades are filled.
  With a fixed price, inflating amount_in doesn't change the price, so it doesn't
  crowd out other traders (unless there's a capacity constraint).

- Lowering min_out: Makes the trade easier to fill but doesn't change the price.
  If the trade was already fillable at the posted price, this has no effect.
  If it wasn't fillable, lowering min_out might make it fillable, giving the user
  a positive-surplus trade they wouldn't have gotten. This IS a manipulation.

So posted-price should eliminate the inflate attack but might still be vulnerable
to the lower-min_out attack. Let's test.
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


def spot_price(pool: Pool) -> float:
    """Spot price = y/x adjusted for fee."""
    return pool.y * (1 - pool.fee_bps / 10000.0) / pool.x


# ---------- Posted-price mechanisms ----------

def batch_posted_price_twap(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    """Posted price = pool's spot price before batch. All trades with
    min_out/amount_in <= P_spot are filled at P_spot.

    The user's price limit min_out/amount_in is the MINIMUM acceptable price.
    If the posted price P_spot >= this minimum, the user is happy to fill."""
    p = spot_price(pool)
    p_int = int(p * 1000000)  # fixed-point for integer math
    results = []
    for i, intent in enumerate(intents):
        # User's minimum acceptable price
        user_price = intent.min_out * 1000000 // intent.amount_in if intent.amount_in > 0 else 0
        # Fill if posted price >= user's minimum
        if p_int >= user_price:
            out = (intent.amount_in * p_int) // 1000000
            results.append(ExecResult(i, True, intent.amount_in, out, out - intent.min_out))
        else:
            results.append(ExecResult(i, False, intent.amount_in, 0, 0))
    return results


def batch_posted_price_with_capacity(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    """Posted price = spot price, but with pool capacity constraint.

    All fillable trades execute against the pool at the posted price, but the
    total output is capped by the pool's actual output capacity. If total
    demand exceeds capacity, trades are rationed pro-rata.

    This models the realistic case where the pool can't output more than it has.
    """
    p = spot_price(pool)
    p_int = int(p * 1000000)

    # Find fillable trades (posted price >= user's minimum)
    fillable = []
    for i, intent in enumerate(intents):
        user_price = intent.min_out * 1000000 // intent.amount_in if intent.amount_in > 0 else 0
        if p_int >= user_price:
            fillable.append((i, intent))

    if not fillable:
        return [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]

    # Total demanded output at posted price
    total_demanded = sum((intent.amount_in * p_int) // 1000000 for _, intent in fillable)
    # Actual pool output for total input
    total_input = sum(intent.amount_in for _, intent in fillable)
    actual_output = q(pool.x, pool.y, total_input, pool.fee_bps)

    # If pool can satisfy all demand, fill at posted price
    if actual_output >= total_demanded:
        results = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]
        for idx, intent in fillable:
            out = (intent.amount_in * p_int) // 1000000
            results[idx] = ExecResult(idx, True, intent.amount_in, out, out - intent.min_out)
        return results

    # Otherwise, ration pro-rata based on actual output
    results = [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(len(intents))]
    remaining = actual_output
    for j, (idx, intent) in enumerate(fillable):
        if j == len(fillable) - 1:
            out = remaining
        else:
            out = (actual_output * intent.amount_in) // total_input
            remaining -= out
        # Check if rationed output still meets min_out
        if out >= intent.min_out:
            results[idx] = ExecResult(idx, True, intent.amount_in, out, out - intent.min_out)
        else:
            results[idx] = ExecResult(idx, False, intent.amount_in, 0, 0)
    return results


def batch_posted_price_marginal(pool: Pool, intents: list[Intent]) -> list[ExecResult]:
    """Posted price = marginal price after all fillable trades execute.

    This is a hybrid: the price is determined by the batch's composition (endogenous)
    but all trades get the SAME marginal price (not the sequential price).

    Algorithm:
    1. Sort by price limit (min_out/amount_in) descending
    2. Find the largest prefix k where the marginal price (output of total_input / total_input)
       exceeds the k-th user's price limit
    3. All k users get output = amount_in * marginal_price
    """
    n = len(intents)
    if n == 0:
        return []

    indexed = list(enumerate(intents))
    indexed.sort(key=lambda pair: (-pair[1].min_out * 1000000 // pair[1].amount_in, pair[0]))

    for k in range(n, 0, -1):
        prefix = indexed[:k]
        total_in = sum(intent.amount_in for _, intent in prefix)
        total_out = q(pool.x, pool.y, total_in, pool.fee_bps)
        if total_in <= 0 or total_out <= 0:
            continue

        # Marginal price = total_out / total_in
        # Check all k users meet min_out at this price
        all_ok = True
        for _, intent in prefix:
            user_out = (total_out * intent.amount_in) // total_in
            if user_out < intent.min_out:
                all_ok = False
                break

        if all_ok:
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

    return [ExecResult(i, False, intents[i].amount_in, 0, 0) for i in range(n)]


# ---------- (A,B) baseline ----------

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
        "fill_rate": total_filled / max(1, completed * 4),
        "completed": completed,
    }


def main() -> None:
    n_trials = 100
    print(f"Posted-Price Mechanism Strategyproofness Test (n=3-5, trials={n_trials}, seed=20260627)")
    print("=" * 130)
    print(f"{'Mechanism':<30} {'SP_rate':>8} {'violations':>10} {'inflate':>8} {'lower':>8} {'checks':>8} {'max_gain':>10} {'welfare':>10} {'fill%':>8}")
    print("-" * 130)

    mechanisms = [
        ("(A,B) baseline", batch_clear_ab),
        ("Posted price (TWAP spot)", batch_posted_price_twap),
        ("Posted price + capacity", batch_posted_price_with_capacity),
        ("Posted price (marginal)", batch_posted_price_marginal),
    ]

    for name, fn in mechanisms:
        rng = random.Random(20260627)
        r = test_strategyproofness(fn, rng, n_trials, time_budget=110)
        print(
            f"{name:<30} {r['sp_rate']:>7.1f}% {r['helped']:>10} {r['helped_inflate']:>8} "
            f"{r['helped_lower']:>8} {r['total_checks']:>8} {r['max_gain']:>10.2f} "
            f"{r['avg_welfare']:>10.1f} {r['fill_rate']*100:>7.1f}%"
        )

    print()
    print("Key: SP_rate = strategyproofness rate (100% = no misreporting helps)")
    print("     inflate = violations from inflating amount_in by 10%")
    print("     lower = violations from lowering min_out by 10%")
    print("     welfare = average total user utility per trial (quasilinear)")
    print("     fill% = fraction of intents filled")
    print()
    print("Hypothesis: Posted-price (TWAP) should eliminate inflate attacks")
    print("            but may still be vulnerable to lower-min_out attacks.")


if __name__ == "__main__":
    main()
