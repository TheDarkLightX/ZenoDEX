"""
Batch-auction aggregate witness backed by the exported batch-auction reference.

This wrapper is intentionally narrow and honest about scope. The underlying
`batch_auction_settler_v1` kernel models aggregate fairness and conservation for
uniform-price batch settlement. It does not model AMM reserve evolution, mixed
directions, reject semantics, or exact-out routing.

We only replay batches that fit the slice the kernel can meaningfully certify:
fully-filled `SWAP_EXACT_IN` intents, all against the same pool and direction,
with no CoW netting or other special-case fill reasons.
"""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Sequence

from ...core.domain_limits import is_strict_int
from ...core.settlement import FillAction, Settlement
from ...state.intents import Intent, IntentKind

REF_IR_HASH = "sha256:b4a7eca7617c99cb1be88d57517f4f46c19fd161e7cf2e512cb9fc969680bedc"
_MAX_BATCH_INTENTS = 32


@dataclass(frozen=True)
class BatchAuctionAggregateSnapshot:
    intent_count: int
    total_input_collected: int
    total_guaranteed_output: int
    total_actual_output: int
    total_filled_input: int
    fees_captured: int


def replay_supported_batch_auction_exact_in_witness(
    *, intents: Sequence[Intent], settlement: Settlement
) -> BatchAuctionAggregateSnapshot | None:
    """
    Return aggregate batch-auction observables for the supported exact-in slice.

    Returns `None` when the settlement is outside the kernel's honest replay
    domain. Raises on ref-load or replay failure for a batch that should be
    supportable by the ref-backed witness.
    """

    if not intents or len(intents) > _MAX_BATCH_INTENTS:
        return None

    fill_by_id = {fill.intent_id: fill for fill in settlement.fills}
    included_by_id = {intent_id: action for intent_id, action in settlement.included_intents}
    if len(included_by_id) != len(intents):
        return None

    first_shape: tuple[str, str, str] | None = None
    total_input = 0
    total_guaranteed = 0
    total_actual = 0
    total_filled_input = 0

    for intent in intents:
        if intent.kind != IntentKind.SWAP_EXACT_IN:
            return None

        pool_id = intent.get_field("pool_id")
        asset_in = intent.get_field("asset_in")
        asset_out = intent.get_field("asset_out")
        amount_in = intent.get_field("amount_in")
        min_amount_out = intent.get_field("min_amount_out", 0)
        if not isinstance(pool_id, str) or not pool_id:
            return None
        if not isinstance(asset_in, str) or not asset_in:
            return None
        if not isinstance(asset_out, str) or not asset_out or asset_out == asset_in:
            return None
        if not is_strict_int(amount_in) or int(amount_in) <= 0:
            return None
        if not is_strict_int(min_amount_out) or int(min_amount_out) < 0:
            return None

        shape = (pool_id, asset_in, asset_out)
        if first_shape is None:
            first_shape = shape
        elif shape != first_shape:
            return None

        if included_by_id.get(intent.intent_id) != FillAction.FILL:
            return None
        fill = fill_by_id.get(intent.intent_id)
        if fill is None or fill.action != FillAction.FILL:
            return None
        if fill.reason not in (None, ""):
            return None
        if not is_strict_int(fill.amount_in_filled) or int(fill.amount_in_filled) != int(amount_in):
            return None
        if not is_strict_int(fill.amount_out_filled) or int(fill.amount_out_filled) < 0:
            return None

        total_input += int(amount_in)
        total_guaranteed += int(min_amount_out)
        total_actual += int(fill.amount_out_filled)
        total_filled_input += int(fill.amount_in_filled)

    # The batch-auction kernel reasons in a single aggregate notional space.
    # When swap outputs or guarantees exceed collected inputs, the AMM execution
    # is still valid, but it is outside this kernel's honest replay domain.
    if int(total_actual) > int(total_input):
        return None
    if int(total_guaranteed) > int(total_input):
        return None

    ref = _load_generated_ref()
    state = ref.init_state()

    for intent in intents:
        state = _step_or_raise(
            ref,
            state,
            tag="add_intent",
            args={
                "amount_in": int(intent.get_field("amount_in")),
                "min_amount_out": int(intent.get_field("min_amount_out", 0)),
                "auth_ok": True,
            },
        )

    state = _step_or_raise(ref, state, tag="close_collection", args={"operator_auth": True})

    remainder_after_outputs = int(total_input) - int(total_actual)
    clearing_price_bps = max(1, min(100_000, (int(total_actual) * 10_000) // max(1, int(total_filled_input))))
    surplus_bps = min(9_999, max(0, (int(remainder_after_outputs) * 10_000) // max(1, int(total_input))))

    state = _step_or_raise(
        ref,
        state,
        tag="submit_solution",
        args={
            "solver_id": 1,
            "proposed_clearing_price_bps": int(clearing_price_bps),
            "surplus_extracted_bps": int(surplus_bps),
            "clearing_valid_witness": True,
        },
    )
    state = _step_or_raise(ref, state, tag="finalize_winner", args={"operator_auth": True})

    for intent in intents:
        fill = fill_by_id[intent.intent_id]
        state = _step_or_raise(
            ref,
            state,
            tag="execute_fill",
            args={
                "fill_input_amount": int(fill.amount_in_filled),
                "fill_output_amount": int(fill.amount_out_filled),
                "fill_min_guaranteed": int(intent.get_field("min_amount_out", 0)),
                "fill_valid_witness": True,
            },
        )

    state = _step_or_raise(
        ref,
        state,
        tag="complete_batch",
        args={
            "protocol_fee_amount": int(remainder_after_outputs),
            "solver_reward_amount": 0,
            "conservation_witness": True,
        },
    )
    if state.phase != "Complete":
        raise RuntimeError(f"batch_auction_settler_v1 ended in non-complete phase: {state.phase!r}")

    return BatchAuctionAggregateSnapshot(
        intent_count=int(state.intent_count),
        total_input_collected=int(state.total_input_collected),
        total_guaranteed_output=int(state.total_guaranteed_output),
        total_actual_output=int(state.total_actual_output),
        total_filled_input=int(state.total_filled_input),
        fees_captured=int(state.fees_captured),
    )


def _step_or_raise(ref: Any, state: Any, *, tag: str, args: dict[str, object]) -> Any:
    result = ref.step(state, ref.Command(tag=tag, args=args))
    if not result.ok or result.state is None:
        detail = result.error or "unknown error"
        raise RuntimeError(f"batch_auction_settler_v1 {tag} failed: {detail}")
    return result.state


@lru_cache(maxsize=1)
def _load_generated_ref() -> Any:
    ref_path = Path(__file__).resolve().parents[3] / "generated" / "batch_auction_settler_v1" / "python_ref" / "batch_auction_settler_v1_ref.py"
    if not ref_path.exists():
        raise FileNotFoundError(f"generated ref not found at {ref_path}")

    module_name = "generated.batch_auction_settler_v1.python_ref.batch_auction_settler_v1_ref"
    existing = sys.modules.get(module_name)
    if existing is not None:
        return existing

    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load module spec for {ref_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module
