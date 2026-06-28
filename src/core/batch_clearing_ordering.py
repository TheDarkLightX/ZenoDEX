"""Small AB-ordering helper surface for replayable research scripts.

This module intentionally exposes only deterministic helper functions used by
the CPSS/AB-CoW research replay scripts. Current settlement dispatch remains in
``src.core.batch_clearing``.
"""

from __future__ import annotations

from typing import List, Tuple

from ..state.intents import Intent, IntentKind
from .neutral_tiebreak import tiebreak_token


def _get_limit_price(intent: Intent) -> int:
    """Return a comparable integer limit-price key for a swap intent."""
    if intent.kind == IntentKind.SWAP_EXACT_IN:
        amount_in = intent.get_field("amount_in", 1)
        min_amount_out = intent.get_field("min_amount_out", 0)
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            return 0
        if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool):
            return 0
        return (int(min_amount_out) * 10**18) // int(amount_in)
    if intent.kind == IntentKind.SWAP_EXACT_OUT:
        amount_out = intent.get_field("amount_out", 1)
        max_amount_in = intent.get_field("max_amount_in", 10**18)
        if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or max_amount_in <= 0:
            return 0
        if not isinstance(amount_out, int) or isinstance(amount_out, bool):
            return 0
        return (int(amount_out) * 10**18) // int(max_amount_in)
    return 0


def _order_swaps_limit_price(intents: List[Intent], *, seed: bytes | None = None) -> List[Intent]:
    """Sort swaps by descending limit price with deterministic tie-breaking."""
    return sorted(
        intents,
        key=lambda intent: (
            -_get_limit_price(intent),
            tiebreak_token(intent.intent_id, seed),
        ),
    )


def _ab_ordering_key_from_totals(
    amount_a: int | None = None,
    surplus_b: int | None = None,
    intent_ids: Tuple[str, ...] | None = None,
    *,
    A_B_order: Tuple[int, int, Tuple[str, ...]] | None = None,
    seed: bytes | None = None,
) -> Tuple[int, int, Tuple[str, ...]]:
    """Build the canonical AB objective key used in research replay."""
    del seed
    if A_B_order is not None:
        amount_a, surplus_b, intent_ids = A_B_order
    if amount_a is None or surplus_b is None or intent_ids is None:
        raise ValueError("amount_a, surplus_b, and intent_ids are required")
    return (int(amount_a), int(surplus_b), tuple(str(intent_id) for intent_id in intent_ids))


def _is_better_ab_key(
    candidate: Tuple[int, int, Tuple[str, ...]],
    best: Tuple[int, int, Tuple[str, ...]] | None,
) -> bool:
    """Return true when ``candidate`` improves A, then B, then lexicographic ids."""
    if best is None:
        return True
    if int(candidate[0]) != int(best[0]):
        return int(candidate[0]) > int(best[0])
    if int(candidate[1]) != int(best[1]):
        return int(candidate[1]) > int(best[1])
    return tuple(candidate[2]) < tuple(best[2])
