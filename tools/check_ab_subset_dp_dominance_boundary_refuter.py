#!/usr/bin/env python3
"""Boundary refuter for unsupported AB dominance-pruning domains.

This is a research checker. It demonstrates why the exact-in same-direction
dominance rule must not be reused for exact-out or mixed-direction AB states
without a separate proof and a separate state order.
"""

from __future__ import annotations

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
    _objective_exact_out_contribution,
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
POOL_ID = "0x" + "bd" * 32
SENDER = "0x" + "11" * 48


@dataclass(frozen=True)
class _BoundaryState:
    r_in: int
    r_out: int
    balances: tuple[int, ...]
    amount_a: int
    surplus_b: int
    order_ids: tuple[str, ...]


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pool(*, reserve0: int, reserve1: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=30,
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _factories() -> _OptimalAbOrderingFactories:
    return _OptimalAbOrderingFactories(
        quote_exact_in_fn=quote_cpmm_swap_exact_in,
        quote_exact_out_fn=quote_cpmm_swap_exact_out,
        swap_exact_in_fn=swap_exact_in_for_pool,
        swap_exact_out_fn=swap_exact_out_for_pool,
        order_limit_price_fn=_order_swaps_limit_price,
        ab_ordering_key_fn=_ab_ordering_key_from_totals,
        is_better_ab_key_fn=_is_better_ab_key,
    )


def _context(pool: PoolState, intent: Intent, balance: int) -> _OptimalAbObjectiveContext:
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, int(balance))
    return _OptimalAbObjectiveContext(
        pool_state=pool,
        first_asset_in=ASSET0,
        r_in0=int(pool.reserve0),
        r_out0=int(pool.reserve1),
        sender_bal_in={intent.sender_pubkey: balances.get(intent.sender_pubkey, ASSET0)},
        factories=_factories(),
    )


def _state_dominates(candidate: _BoundaryState, dominated: _BoundaryState) -> bool:
    """The exact-in same-direction candidate relation, reused intentionally here."""
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


def _key(state: _BoundaryState) -> tuple[int, int, tuple[str, ...]]:
    return _ab_ordering_key_from_totals(
        A_B_order=(state.amount_a, state.surplus_b, state.order_ids)
    )


def _exact_out_intent() -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(100),
        sender_pubkey=SENDER,
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_out": 200,
            "max_amount_in": 2_000,
        },
    )


def _apply_exact_out_suffix(
    state: _BoundaryState,
    intent: Intent,
    context: _OptimalAbObjectiveContext,
) -> _BoundaryState:
    balance_by_sender = {SENDER: int(state.balances[0])}
    contribution = _objective_exact_out_contribution(
        intent,
        context,
        r_in=int(state.r_in),
        r_out=int(state.r_out),
        bal_in=balance_by_sender,
    )
    if contribution is None:
        return _BoundaryState(
            r_in=state.r_in,
            r_out=state.r_out,
            balances=state.balances,
            amount_a=state.amount_a,
            surplus_b=state.surplus_b,
            order_ids=(*state.order_ids, intent.intent_id),
        )

    amount_in, next_r_in, next_r_out = contribution
    return _BoundaryState(
        r_in=int(next_r_in),
        r_out=int(next_r_out),
        balances=(int(state.balances[0]) - int(amount_in),),
        amount_a=int(state.amount_a) + int(amount_in),
        surplus_b=int(state.surplus_b),
        order_ids=(*state.order_ids, intent.intent_id),
    )


def _exact_out_counterexample() -> dict[str, object]:
    """Find the minimal hard-coded exact-out reversal witness."""
    intent = _exact_out_intent()
    context = _context(_pool(reserve0=100, reserve1=1_000), intent, balance=5_000)
    candidate = _BoundaryState(
        r_in=100,
        r_out=1_000,
        balances=(5_000,),
        amount_a=10,
        surplus_b=0,
        order_ids=(_iid(1),),
    )
    dominated = _BoundaryState(
        r_in=200,
        r_out=900,
        balances=(5_000,),
        amount_a=10,
        surplus_b=0,
        order_ids=(_iid(2),),
    )

    candidate_final = _apply_exact_out_suffix(candidate, intent, context)
    dominated_final = _apply_exact_out_suffix(dominated, intent, context)
    candidate_key = _key(candidate_final)
    dominated_key = _key(dominated_final)
    return {
        "counterexample_found": bool(
            _state_dominates(candidate, dominated)
            and _is_better_ab_key(dominated_key, candidate_key)
        ),
        "reason": (
            "Exact-out improves user price by lowering required input, while "
            "the AB objective treats larger executed input as better."
        ),
        "suffix_intent": intent.intent_id,
        "candidate_initial": asdict(candidate),
        "dominated_initial": asdict(dominated),
        "candidate_final": asdict(candidate_final),
        "dominated_final": asdict(dominated_final),
        "candidate_key": candidate_key,
        "dominated_key": dominated_key,
        "naive_dominance_holds": _state_dominates(candidate, dominated),
        "dominated_final_better": _is_better_ab_key(dominated_key, candidate_key),
        "candidate_exact_out_input": int(candidate_final.amount_a - candidate.amount_a),
        "dominated_exact_out_input": int(dominated_final.amount_a - dominated.amount_a),
    }


def _mixed_direction_counterexample() -> dict[str, object]:
    """Show that the reserve order is direction-relative."""
    candidate = _BoundaryState(
        r_in=100,
        r_out=1_000,
        balances=(5_000,),
        amount_a=10,
        surplus_b=0,
        order_ids=(_iid(1),),
    )
    dominated = _BoundaryState(
        r_in=200,
        r_out=900,
        balances=(5_000,),
        amount_a=10,
        surplus_b=0,
        order_ids=(_iid(2),),
    )
    amount_in = 100
    min_amount_out = 0

    candidate_quote = quote_cpmm_swap_exact_in(
        reserve_in=candidate.r_out,
        reserve_out=candidate.r_in,
        amount_in=amount_in,
        fee_bps=30,
    )
    dominated_quote = quote_cpmm_swap_exact_in(
        reserve_in=dominated.r_out,
        reserve_out=dominated.r_in,
        amount_in=amount_in,
        fee_bps=30,
    )
    candidate_key = _ab_ordering_key_from_totals(
        A_B_order=(
            candidate.amount_a + amount_in,
            candidate_quote.amount_out - min_amount_out,
            candidate.order_ids,
        )
    )
    dominated_key = _ab_ordering_key_from_totals(
        A_B_order=(
            dominated.amount_a + amount_in,
            dominated_quote.amount_out - min_amount_out,
            dominated.order_ids,
        )
    )

    return {
        "counterexample_found": bool(
            _state_dominates(candidate, dominated)
            and _is_better_ab_key(dominated_key, candidate_key)
        ),
        "reason": (
            "The same reserve tuple that is favorable for asset0-to-asset1 is "
            "unfavorable after reversing the direction to asset1-to-asset0."
        ),
        "opposite_direction": {
            "asset_in": ASSET1,
            "asset_out": ASSET0,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
        "candidate_initial": asdict(candidate),
        "dominated_initial": asdict(dominated),
        "candidate_amount_out": int(candidate_quote.amount_out),
        "dominated_amount_out": int(dominated_quote.amount_out),
        "candidate_key": candidate_key,
        "dominated_key": dominated_key,
        "naive_dominance_holds": _state_dominates(candidate, dominated),
        "dominated_final_better": _is_better_ab_key(dominated_key, candidate_key),
    }


def _all_found(items: Iterable[dict[str, object]]) -> bool:
    return all(bool(item.get("counterexample_found")) for item in items)


def main() -> int:
    started = time.perf_counter()
    exact_out = _exact_out_counterexample()
    mixed_direction = _mixed_direction_counterexample()
    payload = {
        "schema": "zenodex/ab_subset_dp_dominance_boundary_refuter/v1",
        "ok": _all_found((exact_out, mixed_direction)),
        "exact_out": exact_out,
        "mixed_direction": mixed_direction,
        "boundary_decision": (
            "Keep the current dominance rule scoped to same-pool, "
            "same-direction, exact-in states. Exact-out and mixed-direction "
            "states need rejection by construction or a separate dominance proof."
        ),
        "non_claims": [
            "This refuter does not disprove exact-in same-direction dominance.",
            "This refuter does not propose a safe exact-out dominance relation.",
            "This refuter does not modify production ordering.",
            "No settlement authority is derived from this research artifact.",
        ],
        "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
