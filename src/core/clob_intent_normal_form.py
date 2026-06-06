"""
Deterministic normal form + typed bridge for zk-CLOB v1 limit-order intents.

This is the CLOB counterpart to ``src/core/intent_normal_form.py`` (which orders
AMM swap/liquidity intents). It is kept on its OWN path so it never perturbs the
existing swap/liquidity buckets: it accepts only ``IntentKind.LIMIT_ORDER``
intents and orders incoming orders by the same replay key the batch matcher
uses: earliest ``sequence``, then ``order_id``. Resting-book priority remains a
separate price-time key in :func:`~src.state.clob_book.order_priority_key`.

It also provides :func:`clob_order_from_intent`, the bridge from a validated
:class:`~src.state.intents.Intent` (kind ``LIMIT_ORDER``, fields already shape-
checked by :class:`~src.state.intents.ClobOrderIntent`) to the frozen
:class:`~src.state.clob_book.ClobOrder` domain value the matcher consumes.

CBC discipline: pure, integer-only, deterministic; raises a stable error type on
malformed input rather than guessing.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence

from ..state.clob_book import ClobOrder, ClobSide
from ..state.intents import Intent, IntentKind


class ClobIntentNormalFormError(ValueError):
    pass


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ClobIntentNormalFormError(f"{name} must be an int")
    return int(value)


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ClobIntentNormalFormError(f"{name} must be a non-empty string")
    return value


def clob_order_from_intent(intent: Intent) -> ClobOrder:
    """
    Build the frozen :class:`ClobOrder` the matcher consumes from a LIMIT_ORDER intent.

    The :class:`ClobOrder` constructor re-validates and canonicalizes the fields
    (bool-is-not-int, hex canonicalization, domain bounds), so this bridge is the
    single, total point where an intent becomes a matchable order. ``owner``
    defaults to the intent's ``sender_pubkey`` when not explicitly set.
    """
    if intent.kind != IntentKind.LIMIT_ORDER:
        raise ClobIntentNormalFormError(f"not a LIMIT_ORDER intent: {intent.kind}")

    side_raw = _require_str(intent.get_field("side"), name="side")
    if side_raw not in ("BUY", "SELL"):
        raise ClobIntentNormalFormError("side must be 'BUY' or 'SELL'")
    side = ClobSide.BUY if side_raw == "BUY" else ClobSide.SELL

    price = _require_int(intent.get_field("price_q_per_base"), name="price_q_per_base")
    base_qty = _require_int(intent.get_field("base_qty"), name="base_qty")
    sequence = _require_int(intent.get_field("sequence"), name="sequence")
    order_id = _require_str(intent.get_field("order_id"), name="order_id")
    owner = intent.get_field("owner", intent.sender_pubkey)
    owner = _require_str(owner, name="owner")

    # ClobOrder.__post_init__ enforces all domain bounds / canonical hex and
    # raises ValueError with a stable reject code on any malformed field.
    try:
        return ClobOrder(
            side=side,
            price_q_per_base=price,
            base_qty=base_qty,
            sequence=sequence,
            order_id=order_id,
            owner=owner,
        )
    except ValueError as exc:
        raise ClobIntentNormalFormError(str(exc)) from exc


@dataclass(frozen=True)
class NormalizedClobBatch:
    orders: List[ClobOrder]

    @property
    def order_ids(self) -> List[str]:
        return [o.order_id for o in self.orders]


def incoming_order_key(order: ClobOrder) -> tuple[int, str]:
    """Strict replay key for a batch of incoming orders."""
    return (order.sequence, order.order_id)


def normalize_clob_orders(orders: Sequence[ClobOrder]) -> NormalizedClobBatch:
    """
    Return the deterministic normal-form ordering for a batch of CLOB orders.

    Incoming orders are replayed in strict ``(sequence, order_id)`` order, matching
    :func:`src.core.clob_matching.apply_orders`. Price and side do not affect
    incoming replay order; they affect only resting-book priority once an order is
    on the book.
    """
    return NormalizedClobBatch(orders=sorted(list(orders), key=incoming_order_key))


def normalize_clob_intents(intents: Sequence[Intent]) -> NormalizedClobBatch:
    """Bridge + normalize a batch of LIMIT_ORDER intents to ordered ClobOrders."""
    return normalize_clob_orders([clob_order_from_intent(i) for i in intents])


def is_in_normal_form(orders: Sequence[ClobOrder]) -> bool:
    normalized = normalize_clob_orders(orders)
    return [o.order_id for o in orders] == normalized.order_ids
