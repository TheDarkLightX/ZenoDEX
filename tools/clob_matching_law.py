"""Stage 2 bounded matching-law checker (proof-carrying orderbook).

The Stage 2 law (docs/product_discipline/proof_carrying_orderbook_build_spec.md):

    "No higher-priority eligible order was skipped for any accepted fill."

This module is an INDEPENDENT re-derivation of that law over the OUTPUT of the
live matcher ``src/core/clob_matching.apply_order``. It does NOT call the matcher;
it checks the matcher's result against the law using only the canonical priority
key (``src/state/clob_book.order_priority_key``) and the crossing predicate
(``src/core/clob_matching.crosses``). So a green check is an independent,
bounded corroboration that the live matcher honors price-time priority -- the
dual-checker discipline (production matcher vs. this re-derivation). The eventual
RISC0 guest must prove the SAME law against the same priority key.

Scope (Stage 2 initial): one market, limit orders, price-time priority, bounded
event batches, no hidden order types.
"""
from __future__ import annotations

from typing import Optional

from src.core.clob_matching import ClobMatchAccepted, crosses
from src.state.clob_book import ClobBook, ClobOrder, order_priority_key


def verify_no_priority_skip(
    book_before: ClobBook, taker: ClobOrder, accepted: ClobMatchAccepted
) -> Optional[str]:
    """Return ``None`` iff the matching law holds for this accepted match, else a
    human-readable violation string.

    Law: for every maker that received an accepted fill, EVERY resting maker in
    the PRE-match book that (a) is on the opposite side and crosses the taker and
    (b) has STRICTLY HIGHER priority (``order_priority_key`` strictly smaller)
    must be FULLY consumed (its entire pre-match ``base_qty`` filled). Otherwise a
    higher-priority eligible order was skipped to fill a lower-priority one.

    Pure and total: no I/O, no matcher call -- only the priority key + crossing
    predicate applied to the pre-match book and the accepted fills.
    """
    by_id = {o.order_id: o for o in book_before.orders}

    filled_base: dict[str, int] = {}
    for f in accepted.fills:
        if f.maker_order_id not in by_id:
            return f"fill references maker {f.maker_order_id} absent from the pre-match book"
        filled_base[f.maker_order_id] = filled_base.get(f.maker_order_id, 0) + f.base

    for oid, total in filled_base.items():
        if total > by_id[oid].base_qty:
            return f"maker {oid} over-filled: {total} > pre-match base_qty {by_id[oid].base_qty}"

    # Eligible makers = opposite side AND crossing the taker, from the PRE-match book.
    crossing = [o for o in book_before.orders if o.side is not taker.side and crosses(taker, o)]

    for oid in filled_base:
        k_filled = order_priority_key(by_id[oid])
        for mp in crossing:
            if order_priority_key(mp) < k_filled:  # strictly higher priority than a filled maker
                consumed = filled_base.get(mp.order_id, 0)
                if consumed < mp.base_qty:
                    return (
                        f"priority skip: higher-priority crossing maker {mp.order_id} "
                        f"key={order_priority_key(mp)} filled {consumed}/{mp.base_qty}, but "
                        f"lower-priority maker {oid} key={k_filled} received a fill"
                    )
    return None
