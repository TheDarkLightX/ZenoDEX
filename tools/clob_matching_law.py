"""Stage 2 bounded matching-law checker (proof-carrying orderbook).

The Stage 2 law (docs/product_discipline/proof_carrying_orderbook_build_spec.md):

    "No higher-priority eligible order was skipped for any accepted fill."

This module is an INDEPENDENT re-derivation of that law over the OUTPUT of the
live matcher ``src/core/clob_matching.apply_order``. It does NOT call the matcher;
it checks the matcher's result against the law using only the canonical priority
key (``src/state/clob_book.order_priority_key``) and the crossing predicate
(``src/core/clob_matching.crosses``). So a green check is an independent, bounded
corroboration that the live matcher honors price-time priority in BOTH fill
SELECTION (no higher-priority eligible maker skipped) and fill ORDER (fills
emitted best-priority-first) -- the dual-checker discipline (production matcher
vs. this re-derivation). The eventual RISC0 guest must prove the SAME law against
the same priority key.

Scope (Stage 2 initial): one market, limit orders, price-time priority, bounded
event batches, no hidden order types. This checker covers ONLY the priority law
(selection + order); it does NOT check post-book root, quote rounding/fees, or
per-asset conservation -- those are separate obligations (clob_matching's own
conservation path + the orderbook replay root).
"""
from __future__ import annotations

from typing import Optional

from src.core.clob_matching import ClobMatchAccepted, crosses
from src.state.canonical import domain_sep_bytes, sha256_hex
from src.state.clob_book import ClobBook, ClobOrder, order_priority_key

# Stable identity hash of the matching LAW (mirrors orderbook_api's
# MATCHING_RULE_HASH / FEE_RULE_HASH labelling). The RISC0 guest commits this
# into its journal after running the in-guest law checker
# (zk/state_proof_risc0/shared/src/clob.rs::clob_matching_law_rule_hash), so a
# client can pin WHICH law (identity/version) the proof attests. The Rust label
# MUST byte-match this constant -- the cross-language pin lives in
# clob_law_cases_v1.json (tools/gen_clob_law_fixture.py).
MATCHING_LAW_RULE_HASH = sha256_hex(
    domain_sep_bytes("clob_matching_law_rule", version=1)
    + b"no_higher_priority_eligible_order_skipped_for_any_accepted_fill"
)

# Stable cross-language violation classes. ``verify_no_priority_skip`` keeps its
# human-readable strings (the detail is diagnostic); the no_std guest checker
# returns these codes, and ``law_violation_code`` maps each Python violation to
# its class so the fixture can pin verdict parity.
LAW_ABSENT_MAKER = "law:absent_maker"
LAW_OVERFILL = "law:overfill"
LAW_FILL_ORDER = "law:fill_order"
LAW_PRIORITY_SKIP = "law:priority_skip"


def law_violation_code(violation: Optional[str]) -> Optional[str]:
    """Classify a ``verify_no_priority_skip`` result into its stable class code.

    ``None`` (law holds) maps to ``None``. Any unrecognized violation string is a
    programming error and raises (fail-closed) rather than mislabelling.
    """
    if violation is None:
        return None
    if "absent from the pre-match book" in violation:
        return LAW_ABSENT_MAKER
    if "over-filled" in violation:
        return LAW_OVERFILL
    if violation.startswith("fill-order priority violation"):
        return LAW_FILL_ORDER
    if violation.startswith("priority skip"):
        return LAW_PRIORITY_SKIP
    raise ValueError(f"unclassifiable law violation: {violation}")


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

    # Receipt-ORDER price-time priority: fills must be emitted best-priority-first.
    # A higher-priority maker filled AFTER a lower-priority one is a chronological
    # priority violation even when both end fully consumed -- an aggregate/set-only
    # check would miss it (Codex review 2026-06-06, finding #1).
    prev_key = None
    for f in accepted.fills:
        k = order_priority_key(by_id[f.maker_order_id])
        if prev_key is not None and k < prev_key:
            return (
                f"fill-order priority violation: maker {f.maker_order_id} key={k} was filled "
                f"after a strictly-lower-priority maker key={prev_key}"
            )
        prev_key = k

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
