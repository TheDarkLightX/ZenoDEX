#!/usr/bin/env python3
"""Bounded refutation checker for AB subset-DP dominance pruning.

This is a research checker. It searches for counterexamples to a proposed
Pareto dominance relation between states in the AB full-state subset DP. It
does not change production ordering or authorize settlement.
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool  # noqa: E402
from src.core.batch_clearing_ab_order import (  # noqa: E402
    _OptimalAbObjectiveContext,
    _OptimalAbOrderingFactories,
    _objective_exact_in_contribution,
    _sender_input_balances,
)
from src.core.batch_clearing_ordering import (  # noqa: E402
    _ab_ordering_key_from_totals,
    _is_better_ab_key,
    _order_swaps_limit_price,
)
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.intents import Intent, IntentKind  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402


ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL_ID = "0x" + "bc" * 32
MAX_SUFFIX_REMAINING = 4
MAX_DOMINANCE_PAIRS_PER_MASK = 12
CASE_SIZES = (4, 5, 6)
VARIANTS_PER_SIZE = 6


@dataclass(frozen=True)
class _AbState:
    r_in: int
    r_out: int
    balances: tuple[int, ...]
    amount_a: int
    surplus_b: int
    order_ids: tuple[str, ...]


@dataclass
class _Stats:
    case_count: int = 0
    reachable_state_count: int = 0
    dominance_pairs_seen: int = 0
    dominance_pairs_checked: int = 0
    suffix_permutations_checked: int = 0
    max_states_for_mask: int = 0
    masks_budget_skipped: int = 0
    dominance_pairs_budget_skipped: int = 0


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _pool(variant: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=420 + variant * 13,
        reserve1=480 + variant * 17,
        fee_bps=30,
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _intent(intent_no: int, *, sender_no: int, amount_in: int, min_amount_out: int) -> Intent:
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


def _case(n: int, variant: int) -> tuple[PoolState, list[Intent], BalanceTable]:
    pool = _pool(variant)
    balances = BalanceTable()
    intents: list[Intent] = []
    sender_count = 2 + (variant % 3)
    for idx in range(n):
        amount_in = 17 + ((idx * 11 + variant * 7) % 37)
        min_amount_out = 9 + ((idx * 19 + variant * 5) % 43)
        sender_no = 1 + (idx % sender_count)
        sender = _sender(sender_no)
        current = int(balances.get(sender, ASSET0))
        balances.set(sender, ASSET0, current + amount_in + (idx % 2) * 3)
        balances.set(sender, ASSET1, 0)
        intents.append(
            _intent(
                10_000 + variant * 100 + idx,
                sender_no=sender_no,
                amount_in=amount_in,
                min_amount_out=min_amount_out,
            )
        )
    return pool, intents, balances


def _context(pool: PoolState, intents: list[Intent], balances: BalanceTable) -> _OptimalAbObjectiveContext:
    return _OptimalAbObjectiveContext(
        pool_state=pool,
        first_asset_in=ASSET0,
        r_in0=int(pool.reserve0),
        r_out0=int(pool.reserve1),
        sender_bal_in=_sender_input_balances(intents, balances, ASSET0),
        factories=_OptimalAbOrderingFactories(
            quote_exact_in_fn=quote_cpmm_swap_exact_in,
            quote_exact_out_fn=quote_cpmm_swap_exact_out,
            swap_exact_in_fn=swap_exact_in_for_pool,
            swap_exact_out_fn=swap_exact_out_for_pool,
            order_limit_price_fn=_order_swaps_limit_price,
            ab_ordering_key_fn=_ab_ordering_key_from_totals,
            is_better_ab_key_fn=_is_better_ab_key,
        ),
    )


def _sender_index(context: _OptimalAbObjectiveContext) -> dict[str, int]:
    return {sender: idx for idx, sender in enumerate(sorted(context.sender_bal_in))}


def _initial_state(context: _OptimalAbObjectiveContext) -> _AbState:
    senders = tuple(sorted(context.sender_bal_in))
    return _AbState(
        r_in=int(context.r_in0),
        r_out=int(context.r_out0),
        balances=tuple(int(context.sender_bal_in[sender]) for sender in senders),
        amount_a=0,
        surplus_b=0,
        order_ids=(),
    )


def _balance_dict(state: _AbState, sender_index: dict[str, int]) -> dict[str, int]:
    return {sender: int(state.balances[idx]) for sender, idx in sender_index.items()}


def _apply_intent(
    state: _AbState,
    intent: Intent,
    context: _OptimalAbObjectiveContext,
    sender_index: dict[str, int],
) -> _AbState:
    contribution = _objective_exact_in_contribution(
        intent,
        context,
        r_in=int(state.r_in),
        r_out=int(state.r_out),
        bal_in=_balance_dict(state, sender_index),
    )
    if contribution is None:
        return _AbState(
            r_in=state.r_in,
            r_out=state.r_out,
            balances=state.balances,
            amount_a=state.amount_a,
            surplus_b=state.surplus_b,
            order_ids=(*state.order_ids, intent.intent_id),
        )

    amount_in, surplus, next_r_in, next_r_out = contribution
    next_balances = list(state.balances)
    idx = sender_index[intent.sender_pubkey]
    next_balances[idx] = int(next_balances[idx]) - int(amount_in)
    return _AbState(
        r_in=int(next_r_in),
        r_out=int(next_r_out),
        balances=tuple(next_balances),
        amount_a=int(state.amount_a) + int(amount_in),
        surplus_b=int(state.surplus_b) + int(surplus),
        order_ids=(*state.order_ids, intent.intent_id),
    )


def _reachable_states_by_mask(
    intents: list[Intent],
    context: _OptimalAbObjectiveContext,
) -> dict[int, list[_AbState]]:
    sender_index = _sender_index(context)
    states_by_mask: dict[int, list[_AbState]] = {0: [_initial_state(context)]}
    n = len(intents)
    for mask in range(1 << n):
        states = states_by_mask.get(mask, [])
        for state in list(states):
            for idx, intent in enumerate(intents):
                bit = 1 << idx
                if mask & bit:
                    continue
                next_mask = mask | bit
                states_by_mask.setdefault(next_mask, []).append(_apply_intent(state, intent, context, sender_index))
    return states_by_mask


def _dominates(candidate: _AbState, dominated: _AbState) -> bool:
    """Candidate dominance relation for exact-in same-direction AB states."""
    if candidate.amount_a < dominated.amount_a:
        return False
    if candidate.surplus_b < dominated.surplus_b:
        return False
    if candidate.r_in > dominated.r_in:
        return False
    if candidate.r_out < dominated.r_out:
        return False
    if any(left < right for left, right in zip(candidate.balances, dominated.balances)):
        return False
    if (
        candidate.amount_a == dominated.amount_a
        and candidate.surplus_b == dominated.surplus_b
        and candidate.order_ids > dominated.order_ids
    ):
        return False
    return True


def _key(state: _AbState, context: _OptimalAbObjectiveContext) -> tuple[int, int, tuple[str, ...]]:
    return context.factories.ab_ordering_key_fn(A_B_order=(state.amount_a, state.surplus_b, state.order_ids))


def _simulate_suffix(
    state: _AbState,
    suffix: Iterable[Intent],
    context: _OptimalAbObjectiveContext,
    sender_index: dict[str, int],
) -> _AbState:
    current = state
    for intent in suffix:
        current = _apply_intent(current, intent, context, sender_index)
    return current


def _counterexample_for_pair(
    *,
    candidate: _AbState,
    dominated: _AbState,
    remaining: list[Intent],
    context: _OptimalAbObjectiveContext,
    sender_index: dict[str, int],
) -> tuple[dict[str, object] | None, int]:
    checked = 0
    for suffix in itertools.permutations(remaining):
        checked += 1
        final_candidate = _simulate_suffix(candidate, suffix, context, sender_index)
        final_dominated = _simulate_suffix(dominated, suffix, context, sender_index)
        candidate_key = _key(final_candidate, context)
        dominated_key = _key(final_dominated, context)
        if context.factories.is_better_ab_key_fn(dominated_key, candidate_key):
            return {
                "suffix": [intent.intent_id for intent in suffix],
                "candidate_state": asdict(candidate),
                "dominated_state": asdict(dominated),
                "candidate_final": asdict(final_candidate),
                "dominated_final": asdict(final_dominated),
                "candidate_key": candidate_key,
                "dominated_key": dominated_key,
            }, checked
    return None, checked


def _check_case(n: int, variant: int, stats: _Stats) -> dict[str, object] | None:
    pool, intents, balances = _case(n, variant)
    context = _context(pool, intents, balances)
    sender_index = _sender_index(context)
    states_by_mask = _reachable_states_by_mask(intents, context)
    stats.case_count += 1
    stats.reachable_state_count += sum(len(states) for states in states_by_mask.values())
    stats.max_states_for_mask = max(stats.max_states_for_mask, max(len(states) for states in states_by_mask.values()))

    for mask, states in states_by_mask.items():
        remaining = [intent for idx, intent in enumerate(intents) if not (mask & (1 << idx))]
        if len(remaining) > MAX_SUFFIX_REMAINING:
            stats.masks_budget_skipped += 1
            continue
        checked_for_mask = 0
        for left_index, left in enumerate(states):
            for right_index, right in enumerate(states):
                if left_index == right_index:
                    continue
                if not _dominates(left, right):
                    continue
                stats.dominance_pairs_seen += 1
                if checked_for_mask >= MAX_DOMINANCE_PAIRS_PER_MASK:
                    stats.dominance_pairs_budget_skipped += 1
                    continue
                stats.dominance_pairs_checked += 1
                checked_for_mask += 1
                counterexample, suffix_checks = _counterexample_for_pair(
                    candidate=left,
                    dominated=right,
                    remaining=remaining,
                    context=context,
                    sender_index=sender_index,
                )
                stats.suffix_permutations_checked += suffix_checks
                if counterexample is not None:
                    return {
                        "n": n,
                        "variant": variant,
                        "mask": mask,
                        "counterexample": counterexample,
                    }
    return None


def main() -> int:
    started = time.perf_counter()
    stats = _Stats()
    first_counterexample: dict[str, object] | None = None
    for n in CASE_SIZES:
        for variant in range(VARIANTS_PER_SIZE):
            first_counterexample = _check_case(n, variant, stats)
            if first_counterexample is not None:
                break
        if first_counterexample is not None:
            break

    payload = {
        "schema": "zenodex/ab_subset_dp_dominance_candidate_check/v1",
        "ok": first_counterexample is None,
        "stats": asdict(stats),
        "first_counterexample": first_counterexample,
        "candidate_rule": {
            "domain": "same-pool, same-direction, exact-in AB subset-DP states",
            "dominance": [
                "candidate amount_a >= dominated amount_a",
                "candidate surplus_b >= dominated surplus_b",
                "candidate r_in <= dominated r_in",
                "candidate r_out >= dominated r_out",
                "candidate remaining sender balances are componentwise >= dominated balances",
                "if objective totals tie, candidate prefix order ids are lexicographically no worse",
            ],
        },
        "bounds": {
            "case_sizes": CASE_SIZES,
            "variants_per_size": VARIANTS_PER_SIZE,
            "max_suffix_remaining": MAX_SUFFIX_REMAINING,
            "max_dominance_pairs_per_mask": MAX_DOMINANCE_PAIRS_PER_MASK,
            "suffix_check": "exhaustive over every remaining-order permutation within the suffix bound",
        },
        "non_claims": [
            "This checker does not prove dominance for exact-out intents.",
            "This checker does not alter production ordering.",
            "No settlement authority is derived from this research artifact.",
            "Passing this bounded corpus is not a machine-checked proof.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
