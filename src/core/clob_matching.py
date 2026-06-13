"""
Pure deterministic continuous CLOB matching kernel (zk-CLOB v1).

The moat
--------
dYdX v4 runs an off-chain order book and trusts honest validators to order and
match correctly. ZenoDEX instead encodes price-time priority as a DETERMINISTIC,
integer, conservation-preserving matching RULE: a correct match (the resulting
``post_book_root`` plus the matched fill receipts) is a PRECONDITION OF CLIENT
ACCEPTANCE. A client replays this exact kernel; if the claimed matching does not
reproduce bit-for-bit, the client refuses the transition. Trust the math, not the
sequencer.

What this module is
-------------------
A single-order transition :func:`apply_order` over a :class:`ClobBook`:

    apply_order(book, taker) -> ClobMatchResult

It is a *total function*: every input returns a deterministic accept (with the
post-book and the list of fills) or a deterministic reject (book unchanged).
A batch driver (:func:`apply_orders`) folds incoming orders **in ascending
``sequence``** so the continuous outcome is independent of arrival permutation.

Matching rule (continuous, price-time priority)
-----------------------------------------------
* A BUY taker crosses a SELL maker iff ``taker.price >= maker.price`` (and the
  symmetric condition for a SELL taker vs a BUY maker). If the incoming order
  does not cross the best opposite order, it RESTS (not a reject).
* The taker walks the opposite book in strict :func:`order_priority_key` order
  (best price first, then earliest sequence, then order_id), consuming each
  resting maker until the taker is exhausted or the book stops crossing.
* **FILL PRICE = the RESTING (maker) order's limit price** ``P_m`` — not an
  oracle, not a midpoint. This is the crux convention. Both limits hold at once
  (CROSSING-LIMIT invariant, see ``docs/ZK_CLOB_V1.md``).
* ``quote = floor(matched_base * P_m / PRICE_SCALE)`` — integer-only, checked.
  Both sides book the SAME floored quote, so conservation is exact and rounding
  independent.
* Partial fills: a taker larger than a maker consumes it fully and continues;
  a leftover taker re-rests; a maker larger than the taker has its resting
  quantity reduced and remains.

Reject codes (order-validity; book unchanged on reject — reject-is-no-op)
------------------------------------------------------------------------
``BAD_PRICE``, ``BAD_QTY``, ``BAD_SIDE``, ``BAD_SEQUENCE``, ``BAD_ORDER_ID``,
``BAD_OWNER`` (malformed order), ``DUP_ORDER_ID`` (order_id already resting or
duplicated inside an incoming batch), ``SELF_TRADE`` (taker would match its own
resting maker), ``BOOK_FULL`` (a non-crossing order cannot rest because the book
is at capacity). ``NOT_CROSSING`` is NOT a reject: such an order rests.

Settlement / conservation
-------------------------
Each fill yields a buyer ``(-quote, +base)`` / seller ``(+quote, -base)`` pair of
:class:`~src.core.settlement.BalanceDelta` values (the shared floored quote), so
per-asset ``sum(net_delta) == 0`` exactly — the conservation homomorphism the
CLOB inherits from ``settlement.py``. :func:`settle_fills` routes those deltas
through the conservation-checked balance kernel (``transfer``), which is also
where ``INSUFFICIENT_BALANCE`` is enforced. Callers that need atomic book plus
balance commit use :func:`apply_order_with_settlement`, which commits the
candidate post-book only after all balance transfers accept.

v1 scope / honesty
------------------
Resting orders are NOT collateral-locked (no escrow) in v1: balance sufficiency
is checked at SETTLEMENT of matched fills, not when an order rests. Escrow is
deferred. The RISC0 guest STARK is DESIGN-ONLY (see ``docs/ZK_CLOB_V1.md``); no
proof is produced in v1.

CBC discipline: pure functions, immutable inputs, integer/checked arithmetic,
candidate-commit (validate fully before mutating), stable reject codes,
deterministic total-order tie-breaks.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Tuple, Union

from ..state.balances import AssetId
from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.clob_book import (
    MAX_BASE_QTY,
    MAX_BOOK_ORDERS,
    MAX_PRICE_Q_PER_BASE,
    OWNER_NBYTES,
    PRICE_SCALE,
    REJ_BAD_ORDER_ID,
    REJ_BAD_OWNER,
    REJ_BAD_PRICE,
    REJ_BAD_QTY,
    REJ_BAD_SEQUENCE,
    REJ_BAD_SIDE,
    REJ_BOOK_FULL,
    REJ_DUP_ORDER_ID,
    REJ_NOT_OWNER,
    REJ_SELF_TRADE,
    REJ_UNKNOWN_ORDER,
    ClobBook,
    ClobOrder,
    ClobSide,
    validate_order_fields,
)
from .balance_kernel import (
    BalanceAccepted,
    BalanceRejected,
    BalanceState,
    transfer,
)
from .settlement import BalanceDelta

__all__ = [
    "ClobFill",
    "ClobMatchAccepted",
    "ClobMatchRejected",
    "ClobMatchResult",
    "compute_quote",
    "crosses",
    "apply_order",
    "apply_orders",
    "apply_cancel",
    "ClobCancelAccepted",
    "ClobCancelRejected",
    "ClobCancelResult",
    "fill_balance_deltas",
    "settle_fills",
    "ClobAtomicAccepted",
    "ClobAtomicRejected",
    "ClobAtomicResult",
    "apply_order_with_settlement",
    "REJ_BAD_PRICE",
    "REJ_BAD_QTY",
    "REJ_BAD_SIDE",
    "REJ_BAD_SEQUENCE",
    "REJ_BAD_ORDER_ID",
    "REJ_BAD_OWNER",
    "REJ_DUP_ORDER_ID",
    "REJ_SELF_TRADE",
    "REJ_BOOK_FULL",
]

# Largest single-fill base*price product; reject (never wrap) above this.
_MAX_FILL_PRODUCT = MAX_BASE_QTY * MAX_PRICE_Q_PER_BASE


@dataclass(frozen=True)
class ClobFill:
    """
    One executed fill between a taker and a resting maker.

    ``maker_price`` is the execution price (the maker's resting limit).
    ``base`` is the matched base quantity; ``quote = floor(base*maker_price/SCALE)``.
    ``buyer``/``seller`` are the owners receiving base / quote respectively.
    ``taker_order_id``/``maker_order_id`` bind the fill to its two orders.
    """

    base: int
    quote: int
    maker_price: int
    buyer: str  # receives base, pays quote
    seller: str  # receives quote, gives base
    taker_order_id: str
    maker_order_id: str
    maker_side: ClobSide  # side of the RESTING maker order


@dataclass(frozen=True)
class ClobMatchAccepted:
    book: ClobBook
    fills: Tuple[ClobFill, ...]
    resting_taker_qty: int  # leftover taker base that re-rested (0 if fully filled)


@dataclass(frozen=True)
class ClobMatchRejected:
    reason: str
    book: ClobBook  # unchanged (reject-is-no-op)


ClobMatchResult = Union[ClobMatchAccepted, ClobMatchRejected]


def compute_quote(base: int, maker_price: int) -> int:
    """
    quote = floor(base * maker_price / PRICE_SCALE), integer-only and checked.

    The product is rejected (``OverflowError``) above the documented envelope
    rather than silently wrapping (matches perp_np_matching's i128 discipline).
    """
    if base < 0 or maker_price < 0:
        raise ValueError("base and maker_price must be non-negative")
    product = base * maker_price
    if product > _MAX_FILL_PRODUCT:
        raise OverflowError("clob fill product exceeds documented bound")
    return product // PRICE_SCALE


def crosses(taker: ClobOrder, maker: ClobOrder) -> bool:
    """
    True iff ``taker`` crosses resting ``maker`` (opposite sides, prices cross).

    BUY taker crosses SELL maker iff ``taker.price >= maker.price``.
    SELL taker crosses BUY maker iff ``taker.price <= maker.price``.
    """
    if taker.side is maker.side:
        return False
    if taker.side is ClobSide.BUY:
        return taker.price_q_per_base >= maker.price_q_per_base
    return taker.price_q_per_base <= maker.price_q_per_base


def _buyer_seller(taker: ClobOrder, maker: ClobOrder) -> Tuple[str, str]:
    """Return (buyer_owner, seller_owner) for a taker/maker pair."""
    if taker.side is ClobSide.BUY:
        return taker.owner, maker.owner  # taker buys base, maker sells base
    return maker.owner, taker.owner  # maker buys base, taker sells base


def apply_order(book: ClobBook, taker: object) -> ClobMatchResult:
    """
    Apply a single incoming ``taker`` order to ``book`` (continuous match).

    Candidate-commit: the full match outcome (fills + post-book) is computed
    locally; every reject check runs before any state is committed. On reject the
    returned book is the original (reject-is-no-op).

    NOTE: field validity (price/qty/side/sequence/order_id/owner) is enforced at
    the :class:`ClobOrder` type boundary (``__post_init__``), so a well-typed
    ``taker`` already satisfies ``validate_order_fields``. The ``bad_*`` re-check
    below is DEFENSIVE (and the stable code path used if a caller ever bypasses
    the constructor); the bound-violation reject codes are exercised at
    construction in ``tests/state/test_clob_book.py``.
    """
    if not isinstance(book, ClobBook):
        raise TypeError("book must be a ClobBook")

    # 1. Field validity (malformed taker -> reject, book unchanged).
    if not isinstance(taker, ClobOrder):
        # A non-ClobOrder cannot have been validated; surface a stable code.
        return ClobMatchRejected(REJ_BAD_SIDE, book)
    field_reason = validate_order_fields(
        side=taker.side,
        price_q_per_base=taker.price_q_per_base,
        base_qty=taker.base_qty,
        sequence=taker.sequence,
        order_id=taker.order_id,
        owner=taker.owner,
    )
    if field_reason is not None:
        return ClobMatchRejected(field_reason, book)

    # 2. order_id must be unique against resting orders (replay/dup guard).
    if book.has_order_id(taker.order_id):
        return ClobMatchRejected(REJ_DUP_ORDER_ID, book)

    # 3. Walk the opposite book best-first, building a CANDIDATE outcome.
    opposite = ClobSide.SELL if taker.side is ClobSide.BUY else ClobSide.BUY
    makers = book.resting_for_side(opposite)  # already best-first total order

    remaining = taker.base_qty
    fills: List[ClobFill] = []
    consumed_ids: set[str] = set()  # makers fully consumed
    reduced: dict[str, int] = {}  # maker_order_id -> new remaining qty (partial)

    for maker in makers:
        if remaining <= 0:
            break
        if not crosses(taker, maker):
            break  # best opposite no longer crosses -> stop (price priority)
        # Self-trade: taker would match its own resting order. Reject the whole
        # taker (candidate discarded, book unchanged).
        if maker.owner == taker.owner:
            return ClobMatchRejected(REJ_SELF_TRADE, book)

        match_base = remaining if remaining < maker.base_qty else maker.base_qty
        quote = compute_quote(match_base, maker.price_q_per_base)
        buyer, seller = _buyer_seller(taker, maker)
        fills.append(
            ClobFill(
                base=match_base,
                quote=quote,
                maker_price=maker.price_q_per_base,
                buyer=buyer,
                seller=seller,
                taker_order_id=taker.order_id,
                maker_order_id=maker.order_id,
                maker_side=maker.side,
            )
        )
        remaining -= match_base
        if match_base == maker.base_qty:
            consumed_ids.add(maker.order_id)
        else:
            reduced[maker.order_id] = maker.base_qty - match_base

    # 4. Build the candidate post-book.
    new_orders: List[ClobOrder] = []
    for o in book.orders:
        if o.order_id in consumed_ids:
            continue  # fully filled maker leaves the book
        if o.order_id in reduced:
            new_orders.append(o.with_base_qty(reduced[o.order_id]))
        else:
            new_orders.append(o)

    resting_taker_qty = 0
    if remaining > 0:
        # Leftover taker re-rests. A non-crossing/leftover order needs a slot.
        if len(new_orders) >= MAX_BOOK_ORDERS:
            # Book is full and the leftover cannot rest -> reject, no-op.
            return ClobMatchRejected(REJ_BOOK_FULL, book)
        new_orders.append(taker.with_base_qty(remaining))
        resting_taker_qty = remaining

    post_book = book.with_orders(tuple(new_orders))
    return ClobMatchAccepted(book=post_book, fills=tuple(fills), resting_taker_qty=resting_taker_qty)


def apply_orders(
    book: ClobBook, incoming: Sequence[ClobOrder]
) -> Tuple[ClobBook, Tuple[ClobFill, ...], Tuple[ClobMatchRejected, ...]]:
    """
    Fold a batch of incoming orders into ``book`` deterministically.

    Incoming orders are processed in ascending ``(sequence, order_id)`` order, not
    caller arrival order, so the outcome (post-book root + fill list) is identical
    for any permutation of ``incoming``. Duplicate incoming ``order_id`` values are
    rejected before replay because they would otherwise make ``(sequence,
    order_id)`` non-strict and leave equal-key ordering to caller permutation.
    Resting makers are still consumed by price-time priority inside
    :func:`apply_order`. Rejected orders are no-ops and collected separately.
    """
    ordered = sorted(incoming, key=lambda o: (o.sequence, o.order_id))
    fills: List[ClobFill] = []
    rejects: List[ClobMatchRejected] = []
    counts: dict[str, int] = {}
    for o in ordered:
        counts[o.order_id] = counts.get(o.order_id, 0) + 1
    unique_ordered: List[ClobOrder] = []
    for o in ordered:
        if counts[o.order_id] > 1:
            rejects.append(ClobMatchRejected(REJ_DUP_ORDER_ID, book))
        else:
            unique_ordered.append(o)
    cur = book
    for o in unique_ordered:
        res = apply_order(cur, o)
        if isinstance(res, ClobMatchAccepted):
            cur = res.book
            fills.extend(res.fills)
        else:
            rejects.append(res)
    return cur, tuple(fills), tuple(rejects)


# --- Cancel transition ---------------------------------------------------------
@dataclass(frozen=True)
class ClobCancelAccepted:
    book: ClobBook
    cancelled_order_id: str


@dataclass(frozen=True)
class ClobCancelRejected:
    reason: str
    book: ClobBook  # unchanged (reject-is-no-op)


ClobCancelResult = Union[ClobCancelAccepted, ClobCancelRejected]


def apply_cancel(book: ClobBook, *, order_id: str, requester: str) -> ClobCancelResult:
    """
    Cancel a resting order by ``order_id`` on behalf of ``requester`` (its owner).

    Authorization is ownership: only the resting order's ``owner`` may cancel it.
    Reject codes (book unchanged on reject — reject-is-no-op):

    * ``bad_order_id`` — ``order_id`` not a canonical 32-byte hex;
    * ``bad_owner`` — ``requester`` not a canonical 48-byte pubkey;
    * ``unknown_order`` — no resting order has that id;
    * ``not_owner`` — ``requester`` is not the resting order's owner.

    NOTE (v1 honesty): this enforces ownership at the *value* layer (the
    ``requester`` pubkey must equal the resting owner). Binding ``requester`` to a
    verified signature end-to-end is deferred (see docs/ZK_CLOB_V1.md).
    """
    if not isinstance(book, ClobBook):
        raise TypeError("book must be a ClobBook")

    try:
        oid = canonical_hex_fixed_allow_0x(order_id, nbytes=32, name="order_id")
    except (TypeError, ValueError):
        return ClobCancelRejected(REJ_BAD_ORDER_ID, book)
    try:
        req = canonical_hex_fixed_allow_0x(requester, nbytes=OWNER_NBYTES, name="owner")
    except (TypeError, ValueError):
        return ClobCancelRejected(REJ_BAD_OWNER, book)

    resting = book.find_order(oid)
    if resting is None:
        return ClobCancelRejected(REJ_UNKNOWN_ORDER, book)
    if resting.owner != req:
        return ClobCancelRejected(REJ_NOT_OWNER, book)

    return ClobCancelAccepted(book=book.remove_order_id(oid), cancelled_order_id=oid)


# --- Settlement / conservation -------------------------------------------------
def fill_balance_deltas(
    fill: ClobFill, base_asset: AssetId, quote_asset: AssetId
) -> List[BalanceDelta]:
    """
    Four balance deltas for one fill (buyer/seller x base/quote), shared quote.

    buyer:  -quote (quote_asset),  +base (base_asset)
    seller: +quote (quote_asset),  -base (base_asset)

    Per-asset net == 0 by construction (same integers on both sides), giving the
    conservation homomorphism regardless of how ``quote`` was rounded.
    """
    return [
        BalanceDelta(pubkey=fill.buyer, asset=quote_asset, delta_add=0, delta_sub=fill.quote),
        BalanceDelta(pubkey=fill.buyer, asset=base_asset, delta_add=fill.base, delta_sub=0),
        BalanceDelta(pubkey=fill.seller, asset=quote_asset, delta_add=fill.quote, delta_sub=0),
        BalanceDelta(pubkey=fill.seller, asset=base_asset, delta_add=0, delta_sub=fill.base),
    ]


@dataclass(frozen=True)
class ClobSettlementResult:
    state: BalanceState
    fills_settled: int


@dataclass(frozen=True)
class ClobSettlementRejected:
    reason: str
    state: BalanceState  # unchanged (reject-is-no-op)
    fill_index: int


ClobSettleOutcome = Union[ClobSettlementResult, ClobSettlementRejected]


@dataclass(frozen=True)
class ClobAtomicAccepted:
    """Accepted atomic transition over both book and balance state."""

    book: ClobBook
    state: BalanceState
    fills: Tuple[ClobFill, ...]
    resting_taker_qty: int


@dataclass(frozen=True)
class ClobAtomicRejected:
    """Rejected atomic transition; both ``book`` and ``state`` are unchanged."""

    reason: str
    book: ClobBook
    state: BalanceState


ClobAtomicResult = Union[ClobAtomicAccepted, ClobAtomicRejected]


def settle_fills(
    *,
    state: BalanceState,
    fills: Sequence[ClobFill],
    base_asset: AssetId,
    quote_asset: AssetId,
) -> ClobSettleOutcome:
    """
    Settle matched fills through the conservation-checked balance kernel.

    Each fill is settled as two ``transfer`` calls: buyer->seller of ``quote`` of
    ``quote_asset``, and seller->buyer of ``base`` of ``base_asset``. The balance
    kernel enforces non-negativity and returns ``insufficient_balance`` if a side
    lacks funds (resting orders are NOT escrowed in v1). On the FIRST rejecting
    transfer the original balance ``state`` is returned unchanged
    (reject-is-no-op for balances): we only commit the candidate if all transfers
    accept. This function does not know about the order book; callers that need
    atomic book+balance commit use :func:`apply_order_with_settlement`.

    NOTE (v1 honesty): this is the supply-conserving settlement path; it does not
    by itself prove the *taker* received exactly its entitlement — that is the
    no-overdelivery property tested on ``compute_quote``/``ClobFill``.
    """
    cur = state
    for idx, f in enumerate(fills):
        if f.quote > 0:
            # REVIEW [B+ -> A-]: keep the authority result as ``object`` at this
            # boundary so malformed shadow/authority responses still hit the
            # defensive fail-closed branch instead of becoming statically dead.
            r1: object = transfer(
                state=cur, sender=f.buyer, recipient=f.seller, asset=quote_asset, amount=f.quote
            )
            if isinstance(r1, BalanceRejected):
                return ClobSettlementRejected(r1.reason, state, idx)
            if not isinstance(r1, BalanceAccepted):
                return ClobSettlementRejected("unexpected_balance_result", state, idx)
            cur = r1.state
        if f.base > 0:
            r2: object = transfer(
                state=cur, sender=f.seller, recipient=f.buyer, asset=base_asset, amount=f.base
            )
            if isinstance(r2, BalanceRejected):
                # Roll back to the ORIGINAL pre-settlement state (no-op on reject).
                return ClobSettlementRejected(r2.reason, state, idx)
            if not isinstance(r2, BalanceAccepted):
                return ClobSettlementRejected("unexpected_balance_result", state, idx)
            cur = r2.state
    return ClobSettlementResult(state=cur, fills_settled=len(fills))


def apply_order_with_settlement(
    *,
    book: ClobBook,
    state: BalanceState,
    taker: ClobOrder,
) -> ClobAtomicResult:
    """Apply one order and settle its fills as one candidate-commit transition.

    ``apply_order`` is intentionally a pure book transition. This wrapper is the
    authority-shaped path for a live caller: it computes the candidate post-book,
    settles every fill through the balance kernel, and commits both objects only
    when every transfer accepts. Any match or settlement reject returns the
    original ``book`` and original ``state``.
    """
    match = apply_order(book, taker)
    if isinstance(match, ClobMatchRejected):
        return ClobAtomicRejected(reason=match.reason, book=book, state=state)
    settled = settle_fills(
        state=state,
        fills=match.fills,
        base_asset=book.base_asset,
        quote_asset=book.quote_asset,
    )
    if isinstance(settled, ClobSettlementRejected):
        return ClobAtomicRejected(reason=settled.reason, book=book, state=state)
    return ClobAtomicAccepted(
        book=match.book,
        state=settled.state,
        fills=match.fills,
        resting_taker_qty=match.resting_taker_qty,
    )
