#!/usr/bin/env python3
"""Adversarial parity corpus for AB dominance-pruned subset DP.

The corpus stresses same-direction exact-in AB ordering with shared sender
balances, high minimum-output cliffs, zero-min-output orders, and shallow
liquidity. It compares dominance-pruned DP against unpruned full-state DP and
brute force. It does not modify production ordering.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.batch_clearing_ab_order import _best_order_by_objective_bruteforce  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_in  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402
from tools.check_ab_subset_dp_dominance_candidate import (  # noqa: E402
    ASSET0,
    ASSET1,
    POOL_ID,
    _context,
    _iid,
    _sender,
)
from tools.check_ab_subset_dp_dominance_pruning import (  # noqa: E402
    _Aggregate,
    _order_ids,
    _ratio,
    _run_subset_dp,
    _summarize,
)


DEFAULT_SEED = 2026062804


@dataclass(frozen=True)
class _GeneratedCase:
    label: str
    pool: PoolState
    intents: list[Intent]
    balances: BalanceTable


def _pool(case_index: int, *, reserve0: int, reserve1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=case_index,
        curve_tag=CURVE_TAG_CPMM,
    )


def _intent(
    intent_no: int,
    *,
    sender_no: int,
    amount_in: int,
    min_amount_out: int,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_no),
        sender_pubkey=_sender(sender_no),
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _quote_at_initial(pool: PoolState, amount_in: int) -> int:
    try:
        quote = quote_cpmm_swap_exact_in(
            reserve_in=int(pool.reserve0),
            reserve_out=int(pool.reserve1),
            amount_in=int(amount_in),
            fee_bps=int(pool.fee_bps),
        )
    except ValueError:
        return 0
    return int(quote.amount_out)


def _balance_table(intents: list[Intent], *, mode: str, rng: random.Random) -> BalanceTable:
    totals: dict[str, int] = {}
    for intent in intents:
        totals[intent.sender_pubkey] = totals.get(intent.sender_pubkey, 0) + int(intent.get_field("amount_in"))

    balances = BalanceTable()
    for sender, total in totals.items():
        if mode == "tight":
            value = max(1, int(total * rng.choice((0.42, 0.55, 0.67))))
        elif mode == "one_short":
            value = max(1, total - rng.randint(1, max(1, total // 3)))
        else:
            value = total + rng.randint(0, 7)
        balances.set(sender, ASSET0, value)
        balances.set(sender, ASSET1, 0)
    return balances


def _min_out_for_pattern(pool: PoolState, amount_in: int, idx: int, pattern: str, rng: random.Random) -> int:
    quote = _quote_at_initial(pool, amount_in)
    if pattern == "zero_min":
        return 0 if idx % 2 == 0 else max(0, quote // 3)
    if pattern == "cliff":
        return max(0, quote - rng.randint(0, max(1, quote // 5 + 1)))
    if pattern == "overconstrained":
        return quote + rng.randint(0, max(2, quote // 4 + 2))
    return max(0, quote // rng.choice((2, 3, 4)) - rng.randint(0, 2))


def _generated_case(case_index: int, *, n: int, pattern: str, rng: random.Random) -> _GeneratedCase:
    reserve0 = rng.randint(75, 260) if pattern in {"cliff", "overconstrained"} else rng.randint(250, 900)
    reserve1 = rng.randint(75, 300) if pattern in {"cliff", "overconstrained"} else rng.randint(260, 1000)
    fee_bps = rng.choice((0, 5, 30, 75))
    pool = _pool(case_index, reserve0=reserve0, reserve1=reserve1, fee_bps=fee_bps)
    sender_count = rng.choice((1, 2, 2, 3))
    base_sender = 1000 + case_index * 20
    intents: list[Intent] = []
    for idx in range(n):
        if pattern == "cliff":
            amount_in = rng.randint(18, 74)
        elif pattern == "overconstrained":
            amount_in = rng.randint(22, 92)
        else:
            amount_in = rng.randint(9, 68)
        min_amount_out = _min_out_for_pattern(pool, amount_in, idx, pattern, rng)
        intents.append(
            _intent(
                200_000 + case_index * 100 + idx,
                sender_no=base_sender + (idx % sender_count),
                amount_in=amount_in,
                min_amount_out=min_amount_out,
            )
        )
    balance_mode = rng.choice(("tight", "one_short", "ample"))
    balances = _balance_table(intents, mode=balance_mode, rng=rng)
    return _GeneratedCase(
        label=f"{pattern}:n{n}:case{case_index}:balances_{balance_mode}",
        pool=pool,
        intents=intents,
        balances=balances,
    )


def _case_summary(case: dict[str, object]) -> dict[str, object]:
    full = case["full"]
    pruned = case["pruned"]
    return {
        "label": case["label"],
        "n": case["n"],
        "ok": case["ok"],
        "same_brute_order": case["same_brute_order"],
        "full_states_inserted": full["states_inserted"],
        "pruned_states_inserted": pruned["states_inserted"],
        "full_transitions": full["transitions_evaluated"],
        "pruned_transitions": pruned["transitions_evaluated"],
        "dominated_insertions_skipped": pruned["dominated_insertions_skipped"],
        "retained_states_removed": pruned["retained_states_removed"],
        "reductions": case["reductions"],
    }


def _check_generated_case(case: _GeneratedCase) -> dict[str, object]:
    context = _context(case.pool, case.intents, case.balances)
    full = _run_subset_dp(case.intents, context, prune=False)
    pruned = _run_subset_dp(case.intents, context, prune=True)
    brute = _best_order_by_objective_bruteforce(case.intents, context)
    brute_ids = _order_ids(brute)

    same_dp_key = full.objective_key == pruned.objective_key
    same_dp_order = full.order_ids == pruned.order_ids
    same_brute = brute_ids == full.order_ids == pruned.order_ids
    return {
        "label": case.label,
        "n": len(case.intents),
        "ok": bool(same_dp_key and same_dp_order and same_brute),
        "same_dp_key": bool(same_dp_key),
        "same_dp_order": bool(same_dp_order),
        "same_brute_order": bool(same_brute),
        "brute_order_ids": brute_ids,
        "full": asdict(full),
        "pruned": asdict(pruned),
        "reductions": {
            "state_insertion": round(_ratio(full.states_inserted, pruned.states_inserted), 6),
            "states_retained": round(_ratio(full.states_retained, pruned.states_retained), 6),
            "transitions": round(_ratio(full.transitions_evaluated, pruned.transitions_evaluated), 6),
            "max_bucket": round(_ratio(full.max_bucket_size, pruned.max_bucket_size), 6),
        },
    }


def _corpus(*, seed: int) -> list[_GeneratedCase]:
    rng = random.Random(seed)
    cases: list[_GeneratedCase] = []
    patterns = ("zero_min", "cliff", "overconstrained", "balanced")
    case_index = 0
    for n in (4, 5, 6, 7):
        for pattern in patterns:
            for _ in range(2):
                cases.append(_generated_case(case_index, n=n, pattern=pattern, rng=rng))
                case_index += 1
    # One n=8 smoke case keeps the corpus aware of the next growth step while
    # preserving a routine replay time.
    cases.append(_generated_case(case_index, n=8, pattern="cliff", rng=rng))
    return cases


def _unsupported_domain_controls() -> list[dict[str, object]]:
    return [
        {
            "domain": "exact-out AB states",
            "status": "excluded",
            "reason": "dominance relation has no proof for max-input constraints or exact-out reserve movement",
        },
        {
            "domain": "mixed-direction AB states",
            "status": "excluded",
            "reason": "single directional reserve order is not monotone across opposite swap directions",
        },
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--include-cases", action="store_true")
    args = parser.parse_args()

    started = time.perf_counter()
    checked_cases = [_check_generated_case(case) for case in _corpus(seed=args.seed)]
    aggregate: _Aggregate = _summarize(checked_cases)
    payload = {
        "schema": "zenodex/ab_subset_dp_dominance_adversarial_check/v1",
        "ok": aggregate.mismatch_count == 0,
        "seed": int(args.seed),
        "summary": asdict(aggregate),
        "aggregate_reductions": {
            "state_insertion": round(
                _ratio(aggregate.total_full_states_inserted, aggregate.total_pruned_states_inserted),
                6,
            ),
            "transitions": round(
                _ratio(aggregate.total_full_transitions, aggregate.total_pruned_transitions),
                6,
            ),
        },
        "first_mismatch": next((case for case in checked_cases if not case["ok"]), None),
        "case_summaries": [_case_summary(case) for case in checked_cases],
        "unsupported_domain_controls": _unsupported_domain_controls(),
        "non_claims": [
            "This is an adversarial research checker, not a production ordering change.",
            "The dominance rule remains scoped to same-direction exact-in AB states.",
            "Exact-out and mixed-direction states are explicit non-claims.",
            "Passing this corpus is not a machine-checked proof.",
            "No settlement authority is derived from this artifact.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }
    if args.include_cases:
        payload["cases"] = checked_cases
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
