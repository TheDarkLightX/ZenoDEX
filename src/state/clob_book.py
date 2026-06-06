"""
Canonical central-limit-order-book (CLOB) state with a deterministic state root.

This is the COMMITMENT layer of zk-CLOB v1. The book is a sparse, canonical set
of resting :class:`ClobOrder` values; its :meth:`ClobBook.state_root` mirrors the
hashing discipline of ``src/core/balance_kernel.py`` (``BalanceState``):

* domain-separated prefix (``domain_sep_bytes("clob_book", version=1)``);
* a length-prefixed, fixed-order list of entries;
* fixed-width hex fields via ``hex_to_bytes_fixed`` and ``encode_uvarint``.

Because the entries are serialized in a single explicit total order
(:func:`order_priority_key` — price/sequence/order_id, never Python dict order),
two books built from the same multiset of resting orders produce the *same*
``state_root`` regardless of insertion order. A ``post_book_root`` is therefore a
well-defined cryptographic commitment that a client can recompute and refuse if
it does not match a claimed CLOB transition (the moat: trust the math, not the
sequencer).

The book here is PURE STATE only: it stores resting orders and exposes canonical
ordering + the root. Continuous matching (the transition) lives in
``src/core/clob_matching.py`` and operates on this state.

CBC discipline:
  * frozen dataclasses, immutable inputs, explicit outputs;
  * integer-only fields (bool is *not* int — see :func:`_is_plain_int`);
  * stable reject codes; the book never mutates in place;
  * no floats, no I/O, no wall-clock, no randomness.

Relation to other ZenoDEX matchers (see ``docs/ZK_CLOB_V1.md``):
  * ``src/core/batch_clearing.py`` — pool-facing greedy (A,B) clearer (orders
    trade against an AMM pool; canonical order is best-limit-price-first);
  * ``src/core/uniform_batch_clearing.py`` — one uniform clearing price for the
    whole batch;
  * ``src/core/perp_np_matching.py`` — net-zero clearinghouse (quantity only, all
    fills at one published clearing price; NO price-time priority);
  * CLOB (this/the matcher) — continuous, peer-to-peer, fills at the RESTING
    maker's limit price, with strict price-then-time priority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Union

from .canonical import (
    canonical_hex_fixed_allow_0x,
    domain_sep_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)

__all__ = [
    "PRICE_SCALE",
    "MAX_PRICE_Q_PER_BASE",
    "MAX_BASE_QTY",
    "MAX_SEQUENCE",
    "MAX_BOOK_ORDERS",
    "ORDER_ID_NBYTES",
    "OWNER_NBYTES",
    "ASSET_NBYTES",
    "BOOK_DOMAIN_SEP_LABEL",
    "BOOK_VERSION",
    "ClobSide",
    "ClobOrder",
    "ClobBook",
    "order_priority_key",
    "REJ_BAD_PRICE",
    "REJ_BAD_QTY",
    "REJ_BAD_SIDE",
    "REJ_BAD_ORDER_ID",
    "REJ_BAD_SEQUENCE",
    "REJ_BAD_OWNER",
    "REJ_DUP_ORDER_ID",
    "REJ_BOOK_FULL",
    "REJ_SELF_TRADE",
    "REJ_INSUFFICIENT_BALANCE",
    "REJ_UNKNOWN_ORDER",
    "REJ_NOT_OWNER",
]

# --- Domain bounds (keep arithmetic inside a documented integer envelope) -------
# Quote-per-base prices are scaled integers: a price of `p` means `p / PRICE_SCALE`
# quote units per 1 base unit. quote = floor(base * price / PRICE_SCALE).
PRICE_SCALE = 10**8  # mirrors perp_np_matching.E8 (quote-per-base * 1e8)

# Bound price and quantity so the largest single-fill product
#   base * price  <=  MAX_BASE_QTY * MAX_PRICE_Q_PER_BASE
# stays well within an i128 / Rust-shadow envelope (< 2**127). With both at
# (1<<56)-1 the product is < 2**112, leaving headroom for accumulation.
MAX_PRICE_Q_PER_BASE = (1 << 56) - 1
MAX_BASE_QTY = (1 << 56) - 1
MAX_SEQUENCE = (1 << 64) - 1  # u64 sequence
MAX_BOOK_ORDERS = 1 << 20  # capacity guard (BOOK_FULL)

ORDER_ID_NBYTES = 32  # 0x-prefixed 32-byte hex id (matches intent_id discipline)
OWNER_NBYTES = 48  # BLS12-381 pubkey (matches balance_kernel.PUBKEY_NBYTES)
ASSET_NBYTES = 32  # asset id (matches balance_kernel.ASSET_NBYTES)

BOOK_DOMAIN_SEP_LABEL = "clob_book"
BOOK_VERSION = 1

# --- Stable reject codes (order-validity; consensus behaviour) ------------------
REJ_BAD_PRICE = "bad_price"
REJ_BAD_QTY = "bad_qty"
REJ_BAD_SIDE = "bad_side"
REJ_BAD_ORDER_ID = "bad_order_id"
REJ_BAD_SEQUENCE = "bad_sequence"
REJ_BAD_OWNER = "bad_owner"
REJ_DUP_ORDER_ID = "dup_order_id"
REJ_BOOK_FULL = "book_full"
REJ_SELF_TRADE = "self_trade"
REJ_INSUFFICIENT_BALANCE = "insufficient_balance"
# Cancel-path reject codes.
REJ_UNKNOWN_ORDER = "unknown_order"
REJ_NOT_OWNER = "not_owner"


def _is_plain_int(v: object) -> bool:
    """True for a genuine int (bool is NOT accepted as int)."""
    return isinstance(v, int) and not isinstance(v, bool)


def _canonical_order_id(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=ORDER_ID_NBYTES, name="order_id")
    except Exception:
        return None


def _canonical_owner(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=OWNER_NBYTES, name="owner")
    except Exception:
        return None


def _canonical_asset(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=ASSET_NBYTES, name="asset")
    except Exception:
        return None


class ClobSide(Enum):
    """Order side. Integer codes are used in the canonical root encoding."""

    BUY = "BUY"
    SELL = "SELL"

    @property
    def code(self) -> int:
        return 0 if self is ClobSide.BUY else 1


@dataclass(frozen=True)
class ClobOrder:
    """
    A single typed CLOB order (resting or incoming taker).

    Fields are strongly typed domain values, validated at construction so a
    malformed order can never enter the book:

    * ``side`` — :class:`ClobSide` (BUY/SELL).
    * ``price_q_per_base`` — scaled integer quote-per-base limit price,
      ``1 <= price <= MAX_PRICE_Q_PER_BASE``.
    * ``base_qty`` — remaining base quantity, ``1 <= base_qty <= MAX_BASE_QTY``.
    * ``sequence`` — u64 arrival sequence used as the time-priority key. NOTE: v1
      only **bounds-checks** this — it is submitter-supplied, NOT enforced monotone —
      so the time-priority guarantee is conditional on a canonical sequence source
      (assignment from ingress ``intent_id`` order is deferred; see docs/ZK_CLOB_V1.md).
    * ``order_id`` — 0x-prefixed 32-byte hex id (final tie-break, uniqueness).
    * ``owner`` — 0x-prefixed 48-byte pubkey (self-trade + settlement routing).

    ``__post_init__`` raises ``ValueError`` (with the matching stable reject code
    as the message) on any malformed field; callers that want a reject *result*
    rather than an exception use :func:`validate_order_fields`.
    """

    side: ClobSide
    price_q_per_base: int
    base_qty: int
    sequence: int
    order_id: str
    owner: str

    def __post_init__(self) -> None:
        reason = validate_order_fields(
            side=self.side,
            price_q_per_base=self.price_q_per_base,
            base_qty=self.base_qty,
            sequence=self.sequence,
            order_id=self.order_id,
            owner=self.owner,
        )
        if reason is not None:
            raise ValueError(reason)
        # Canonicalize hex fields in place (frozen -> object.__setattr__).
        object.__setattr__(self, "order_id", _canonical_order_id(self.order_id))
        object.__setattr__(self, "owner", _canonical_owner(self.owner))

    def with_base_qty(self, new_qty: int) -> "ClobOrder":
        """Return a copy with a reduced remaining quantity (partial fill)."""
        return ClobOrder(
            side=self.side,
            price_q_per_base=self.price_q_per_base,
            base_qty=new_qty,
            sequence=self.sequence,
            order_id=self.order_id,
            owner=self.owner,
        )


def validate_order_fields(
    *,
    side: object,
    price_q_per_base: object,
    base_qty: object,
    sequence: object,
    order_id: object,
    owner: object,
) -> Union[str, None]:
    """
    Validate raw order fields; return a stable reject code or ``None`` if valid.

    Validation order is fixed (side, price, qty, sequence, order_id, owner) and is
    part of the consensus contract: it determines which reject code a multiply
    malformed order receives.
    """
    if not isinstance(side, ClobSide):
        return REJ_BAD_SIDE
    if not _is_plain_int(price_q_per_base) or not (1 <= price_q_per_base <= MAX_PRICE_Q_PER_BASE):
        return REJ_BAD_PRICE
    if not _is_plain_int(base_qty) or not (1 <= base_qty <= MAX_BASE_QTY):
        return REJ_BAD_QTY
    if not _is_plain_int(sequence) or not (0 <= sequence <= MAX_SEQUENCE):
        return REJ_BAD_SEQUENCE
    if _canonical_order_id(order_id) is None:
        return REJ_BAD_ORDER_ID
    if _canonical_owner(owner) is None:
        return REJ_BAD_OWNER
    return None


def order_priority_key(order: ClobOrder) -> tuple[int, int, int, str]:
    """
    Strict total-order matching/canonical key for a resting order.

    The matcher consumes resting orders by ascending key (best first):

    * **price** — for a SELL book, *lowest* price is best (key uses ``+price``);
      for a BUY book, *highest* price is best (key uses ``-price``). The sign is
      chosen so ascending-key == best-first on *both* sides.
    * **sequence** — earlier (smaller) arrival sequence wins (time priority). This
      is a strict total order over the sequences *as given*; the time-priority
      guarantee is only as trustworthy as the sequence source, which v1 leaves
      submitter-supplied (canonical assignment deferred — see docs/ZK_CLOB_V1.md).
    * **order_id** — lexicographic, final deterministic tie-break. Because
      ``order_id`` is unique within a book (DUP_ORDER_ID is rejected) the key is a
      strict total order: no two resting orders ever compare equal.

    Returned tuple: ``(side_code, price_term, sequence, order_id)`` where
    ``side_code`` keeps the two books separable but is constant within a book.
    """
    if order.side is ClobSide.BUY:
        price_term = -order.price_q_per_base  # highest price first
    else:
        price_term = order.price_q_per_base  # lowest price first
    return (order.side.code, price_term, order.sequence, order.order_id)


@dataclass(frozen=True)
class ClobBook:
    """
    Canonical resting-order book (one trading pair).

    ``orders`` is a tuple of resting :class:`ClobOrder` values. Construction
    canonicalizes the tuple into strict ``order_priority_key`` order and rejects
    duplicate ``order_id`` / over-capacity books, so the *representation* is
    unique for a given resting set. ``base_asset`` / ``quote_asset`` fix the two
    settlement assets and are bound into the root.
    """

    base_asset: str
    quote_asset: str
    orders: tuple[ClobOrder, ...] = ()

    def __post_init__(self) -> None:
        base = _canonical_asset(self.base_asset)
        quote = _canonical_asset(self.quote_asset)
        if base is None:
            raise ValueError("bad_base_asset")
        if quote is None:
            raise ValueError("bad_quote_asset")
        if base == quote:
            raise ValueError("base_asset must differ from quote_asset")
        if not isinstance(self.orders, tuple):
            raise TypeError("orders must be a tuple")
        if len(self.orders) > MAX_BOOK_ORDERS:
            raise ValueError(REJ_BOOK_FULL)
        seen: set[str] = set()
        for o in self.orders:
            if not isinstance(o, ClobOrder):
                raise TypeError("book orders must be ClobOrder")
            if o.order_id in seen:
                raise ValueError(REJ_DUP_ORDER_ID)
            seen.add(o.order_id)
        object.__setattr__(self, "base_asset", base)
        object.__setattr__(self, "quote_asset", quote)
        object.__setattr__(
            self,
            "orders",
            tuple(sorted(self.orders, key=order_priority_key)),
        )

    # --- queries ---------------------------------------------------------------
    def has_order_id(self, order_id: str) -> bool:
        oid = _canonical_order_id(order_id)
        if oid is None:
            return False
        return any(o.order_id == oid for o in self.orders)

    def find_order(self, order_id: str) -> Union["ClobOrder", None]:
        oid = _canonical_order_id(order_id)
        if oid is None:
            return None
        for o in self.orders:
            if o.order_id == oid:
                return o
        return None

    def resting_for_side(self, side: ClobSide) -> tuple[ClobOrder, ...]:
        """Resting orders on ``side``, already in best-first total order."""
        return tuple(o for o in self.orders if o.side is side)

    def is_full(self) -> bool:
        return len(self.orders) >= MAX_BOOK_ORDERS

    # --- mutators (return a NEW book; never in-place) --------------------------
    def with_orders(self, orders: tuple[ClobOrder, ...]) -> "ClobBook":
        return ClobBook(base_asset=self.base_asset, quote_asset=self.quote_asset, orders=orders)

    def add_order(self, order: ClobOrder) -> "ClobBook":
        """Rest ``order`` (caller guarantees it has passed validity/dup checks)."""
        return self.with_orders(self.orders + (order,))

    def remove_order_id(self, order_id: str) -> "ClobBook":
        oid = _canonical_order_id(order_id)
        kept = tuple(o for o in self.orders if o.order_id != oid)
        return self.with_orders(kept)

    # --- commitment ------------------------------------------------------------
    def state_root(self) -> str:
        """
        Domain-separated SHA-256 commitment to the resting book.

        Mirrors ``BalanceState.state_root``: a domain-separated prefix, a
        length prefix, then each entry's fixed-width fields in canonical
        (best-first) order. Insertion-order independent by construction
        (entries are sorted in ``__post_init__``); the root changes iff the
        resting multiset changes.
        """
        payload = bytearray(domain_sep_bytes(BOOK_DOMAIN_SEP_LABEL, version=BOOK_VERSION))
        payload += hex_to_bytes_fixed(self.base_asset, nbytes=ASSET_NBYTES, name="base_asset")
        payload += hex_to_bytes_fixed(self.quote_asset, nbytes=ASSET_NBYTES, name="quote_asset")
        payload += encode_uvarint(len(self.orders))
        for o in self.orders:
            payload += encode_uvarint(o.side.code)
            payload += encode_uvarint(o.price_q_per_base)
            payload += encode_uvarint(o.base_qty)
            payload += encode_uvarint(o.sequence)
            payload += hex_to_bytes_fixed(o.order_id, nbytes=ORDER_ID_NBYTES, name="order_id")
            payload += hex_to_bytes_fixed(o.owner, nbytes=OWNER_NBYTES, name="owner")
        return sha256_hex(bytes(payload))
