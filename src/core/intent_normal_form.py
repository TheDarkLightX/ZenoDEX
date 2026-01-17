"""
Intent normal forms (canonical batch ordering) for quotient-space reasoning.

Goal: provide a deterministic "normal form" for a list of intents so that:
  - many syntactic batches collapse to one canonical representative, and
  - proof/certificate verification can require canonical ordering.

This module is intentionally conservative: it does not claim that reordering
preserves economic semantics; rather it defines the order the protocol
*chooses* as canonical when a proof/certificate is required.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Optional, Sequence, Tuple

from ..state.intents import Intent, IntentKind


class IntentNormalFormError(ValueError):
    pass


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise IntentNormalFormError(f"{name} must be an int")
    return int(value)


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise IntentNormalFormError(f"{name} must be a non-empty string")
    return value


def _pool_id_for_intent(intent: Intent) -> Optional[str]:
    if intent.kind == IntentKind.CREATE_POOL:
        return None
    pool_id = intent.get_field("pool_id")
    if pool_id is None:
        return None
    return _require_str(pool_id, name="intent.fields.pool_id")


def _swap_limit_price(intent: Intent) -> int:
    """
    Effective limit price used for deterministic ordering (best first).

    Matches the spirit of src/core/batch_clearing._get_limit_price but is kept
    local here to avoid coupling normal-form code to settlement internals.
    """
    if intent.kind == IntentKind.SWAP_EXACT_IN:
        amount_in = _require_int(intent.get_field("amount_in", 0), name="swap.amount_in")
        min_amount_out = _require_int(intent.get_field("min_amount_out", 0), name="swap.min_amount_out")
        if amount_in <= 0:
            raise IntentNormalFormError("swap.amount_in must be > 0")
        if min_amount_out < 0:
            raise IntentNormalFormError("swap.min_amount_out must be >= 0")
        return (min_amount_out * 10**18) // amount_in

    if intent.kind == IntentKind.SWAP_EXACT_OUT:
        amount_out = _require_int(intent.get_field("amount_out", 0), name="swap.amount_out")
        max_amount_in = _require_int(intent.get_field("max_amount_in", 0), name="swap.max_amount_in")
        if max_amount_in <= 0:
            # Treat as worst; but fail-closed in strict contexts.
            raise IntentNormalFormError("swap.max_amount_in must be > 0")
        if amount_out <= 0:
            raise IntentNormalFormError("swap.amount_out must be > 0")
        if max_amount_in < 0:
            raise IntentNormalFormError("swap.max_amount_in must be >= 0")
        return (amount_out * 10**18) // max_amount_in

    raise IntentNormalFormError(f"not a swap intent: {intent.kind}")


def _lp_submission_order(intent: Intent) -> Optional[int]:
    # Optional field; if absent, caller decides whether to reject or fallback.
    value = intent.get_field("submission_order")
    if value is None:
        return None
    return _require_int(value, name="lp.submission_order")


@dataclass(frozen=True)
class NormalizedBatch:
    intents: List[Intent]

    @property
    def intent_ids(self) -> List[str]:
        return [i.intent_id for i in self.intents]


def normalize_intents(
    intents: Sequence[Intent],
    *,
    strict_lp_order: bool = False,
) -> NormalizedBatch:
    """
    Return a deterministic normal form ordering for `intents`.

    Ordering rules (high level):
    1) CREATE_POOL first (by intent_id)
    2) Then per pool_id (lexicographic)
       - swaps first: best limit price first (descending), tie-break by intent_id
       - liquidity next: by submission_order (if present), else by intent_id
    3) Intents without pool_id at the end (by intent_id)

    If `strict_lp_order=True`, all ADD/REMOVE_LIQUIDITY intents must provide
    an integer `submission_order` field.
    """

    def key(intent: Intent) -> Tuple[int, str, int, int, str]:
        # phase: CREATE_POOL first
        if intent.kind == IntentKind.CREATE_POOL:
            return (0, "", 0, 0, intent.intent_id)

        pool_id = _pool_id_for_intent(intent)
        pool_bucket = pool_id if pool_id is not None else "\uffff"

        # kind bucket within a pool
        if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            price = _swap_limit_price(intent)
            # Use negative price for descending order.
            return (1, pool_bucket, 0, -price, intent.intent_id)

        if intent.kind in (IntentKind.ADD_LIQUIDITY, IntentKind.REMOVE_LIQUIDITY):
            sub = _lp_submission_order(intent)
            if sub is None and strict_lp_order:
                raise IntentNormalFormError(
                    f"liquidity intent missing submission_order: {intent.intent_id}"
                )
            # For non-strict mode, fall back to intent_id ordering.
            sub_key = sub if sub is not None else 0
            return (1, pool_bucket, 1, sub_key, intent.intent_id)

        # Unknown/other intent kinds: place after known pool actions.
        return (1, pool_bucket, 2, 0, intent.intent_id)

    return NormalizedBatch(intents=sorted(list(intents), key=key))


def is_in_normal_form(
    intents: Sequence[Intent],
    *,
    strict_lp_order: bool = False,
) -> bool:
    normalized = normalize_intents(intents, strict_lp_order=strict_lp_order)
    return [i.intent_id for i in intents] == normalized.intent_ids


def require_normal_form(
    intents: Sequence[Intent],
    *,
    strict_lp_order: bool = False,
) -> None:
    if not is_in_normal_form(intents, strict_lp_order=strict_lp_order):
        raise IntentNormalFormError("intents not in normal form")


def iter_pool_partitions(intents: Sequence[Intent]) -> Iterable[Tuple[Optional[str], List[Intent]]]:
    """
    Yield (pool_id, intents) partitions in normal-form pool order.

    Useful for “quotient” reasoning and certificate generation where per-pool
    reasoning is performed on a canonical representative.
    """
    normalized = normalize_intents(intents).intents
    out: List[Tuple[Optional[str], List[Intent]]] = []
    buckets: dict[Optional[str], List[Intent]] = {}
    order: List[Optional[str]] = []
    for intent in normalized:
        pool_id = _pool_id_for_intent(intent)
        if intent.kind == IntentKind.CREATE_POOL:
            pool_id = None
        if pool_id not in buckets:
            buckets[pool_id] = []
            order.append(pool_id)
        buckets[pool_id].append(intent)
    for pool_id in order:
        out.append((pool_id, buckets[pool_id]))
    return out

