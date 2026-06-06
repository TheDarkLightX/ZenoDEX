"""
Deterministic (non-ZK) replay engine + verifier for the proof-carrying orderbook.

Stage 1 of ``docs/product_discipline/proof_carrying_orderbook_build_spec.md``.

What this is
------------
A DETERMINISTIC replay of an ordered list of typed order events through the
COMMITTED matching kernel (``src/core/clob_matching.py``) from an empty book,
recording per event the ``pre_book_root``, ``post_book_root``, and the fills
produced (with a receipt hash per fill). The whole replay is bound into a
single domain-separated ``replay_root``.

This is the ``replay_verified`` evidence source named in the status model
(``OrderStatus.REPLAY_VERIFIED``): a client re-derives the transition locally
and refuses anything that does not reproduce bit-for-bit. It is the EXACT
computation the Stage-2 RISC0 guest will later prove.

Honest scope
------------
* This is deterministic replay ONLY. It is NOT a ZK proof and produces no STARK.
  It is the deterministic ``replay_verified`` evidence the Stage-2 guest proves.
* ``matching_rule_hash`` + ``fee_rule_hash`` are PINNED into the receipt and the
  ``replay_root`` (the rulebook/constitution link). v1 has NO per-fill fee field
  in ``ClobFill``, so the fee hash binds the rulebook identity, not a re-derived
  fee value. A claim whose stale ``replay_root`` no longer matches a re-hash over
  the changed fee rule is rejected; a claim that consistently re-hashes a
  different fee rule is the CLIENT's pinned-rulebook defense (Stage 2/3), not
  Stage-1 replay scope.
* "Duplicate" here means a resting ``order_id`` collision rejected by the
  matcher (``dup_order_id``), not a global replay-nonce ledger.

Determinism
-----------
The canonical replay order is the ``sequence`` field ONLY: NO wall clock, NO
arrival order. ``replay_events`` sorts events by ``sequence`` before replay, so
the SAME event multiset yields an identical ``replay_root`` regardless of how
the caller built the list. Sequences must be unique (strict total order); a
duplicate sequence is a fail-closed reject.

CBC discipline
--------------
Pure functions, immutable frozen records, integer/checked arithmetic, stable
reject codes, candidate-commit (verifier re-executes before accepting), and a
fixed, documented compare precedence (consensus behavior). The receipt and its
per-event records are DUMB typed containers: they validate SHAPE only, never
cross-field consistency. ALL consistency checking lives in :func:`verify_replay`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple, Union

from ..state.canonical import (
    domain_sep_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from ..state.clob_book import (
    ASSET_NBYTES,
    ORDER_ID_NBYTES,
    OWNER_NBYTES,
    ClobBook,
    ClobOrder,
    ClobSide,
)
from .clob_matching import (
    ClobCancelAccepted,
    ClobCancelRejected,
    ClobFill,
    ClobMatchAccepted,
    ClobMatchRejected,
    apply_cancel,
    apply_order,
)

__all__ = [
    "RULE_HASH_NBYTES",
    "EVENT_PLACE",
    "EVENT_CANCEL",
    "PlaceEvent",
    "CancelEvent",
    "OrderEvent",
    "FillRecord",
    "PerEventResult",
    "ReplayReceipt",
    "replay_events",
    "verify_replay",
    "fill_receipt_hash",
    # Stable verifier reject codes.
    "REJ_DUP_SEQUENCE",
    "REJ_EMPTY_EVENTS",
    "REJ_BAD_EVENT",
    "REJ_EVENT_COUNT_MISMATCH",
    "REJ_EVENT_MISMATCH",
    "REJ_ACCEPT_STATUS_MISMATCH",
    "REJ_REJECT_CODE_MISMATCH",
    "REJ_PRE_ROOT_MISMATCH",
    "REJ_POST_ROOT_MISMATCH",
    "REJ_FILL_COUNT_MISMATCH",
    "REJ_FILL_MISMATCH",
    "REJ_FILL_RECEIPT_MISMATCH",
    "REJ_FINAL_ROOT_MISMATCH",
    "REJ_REPLAY_ROOT_MISMATCH",
    "REJ_REEXEC_ERROR",
]

# A matching/fee rule hash is a 0x-prefixed 32-byte hex digest (the rulebook pin).
RULE_HASH_NBYTES = 32

EVENT_PLACE = "place"
EVENT_CANCEL = "cancel"

REPLAY_DOMAIN_SEP_LABEL = "orderbook_replay"
REPLAY_VERSION = 1
FILL_DOMAIN_SEP_LABEL = "orderbook_replay_fill"
FILL_VERSION = 1

# --- Stable verifier reject codes (consensus behavior; fixed compare order) -----
REJ_DUP_SEQUENCE = "dup_sequence"
REJ_EMPTY_EVENTS = "empty_events"
REJ_BAD_EVENT = "bad_event"
REJ_EVENT_COUNT_MISMATCH = "event_count_mismatch"
REJ_EVENT_MISMATCH = "event_mismatch"
REJ_ACCEPT_STATUS_MISMATCH = "accept_status_mismatch"
REJ_REJECT_CODE_MISMATCH = "reject_code_mismatch"
REJ_PRE_ROOT_MISMATCH = "pre_root_mismatch"
REJ_POST_ROOT_MISMATCH = "post_root_mismatch"
REJ_FILL_COUNT_MISMATCH = "fill_count_mismatch"
REJ_FILL_MISMATCH = "fill_mismatch"
REJ_FILL_RECEIPT_MISMATCH = "fill_receipt_mismatch"
REJ_FINAL_ROOT_MISMATCH = "final_root_mismatch"
REJ_REPLAY_ROOT_MISMATCH = "replay_root_mismatch"
REJ_REEXEC_ERROR = "reexec_error"


def _canonical_rule_hash(value: object, name: str) -> str:
    """Validate a 0x-prefixed 32-byte rule hash; raise on malformed input."""
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    # hex_to_bytes_fixed enforces 0x prefix + exact length + hex charset.
    hex_to_bytes_fixed(value, nbytes=RULE_HASH_NBYTES, name=name)
    return value.lower()


# --- Typed, frozen order events -------------------------------------------------
@dataclass(frozen=True)
class PlaceEvent:
    """
    A typed PLACE event: rest/match an order at a given canonical sequence.

    DUMB container: shape/type validation only. The embedded :class:`ClobOrder`
    already validated its own fields at construction; we require its ``sequence``
    to equal this event's ``sequence`` so there is a SINGLE source of truth for
    the canonical (time-priority and replay) order.
    """

    sequence: int
    order: ClobOrder

    def __post_init__(self) -> None:
        if not isinstance(self.sequence, int) or isinstance(self.sequence, bool):
            raise TypeError("sequence must be a plain int")
        if self.sequence < 0:
            raise ValueError("sequence must be non-negative")
        if not isinstance(self.order, ClobOrder):
            raise TypeError("order must be a ClobOrder")
        if self.order.sequence != self.sequence:
            # One source of truth: the order's time-priority key IS the event seq.
            raise ValueError("place order.sequence must equal event sequence")

    @property
    def kind(self) -> str:
        return EVENT_PLACE


@dataclass(frozen=True)
class CancelEvent:
    """
    A typed CANCEL event: remove a resting order on behalf of ``requester``.

    DUMB container: shape/type validation only. Authorization (requester == owner)
    is enforced by the COMMITTED ``apply_cancel`` at replay time, not here.
    """

    sequence: int
    order_id: str
    requester: str

    def __post_init__(self) -> None:
        if not isinstance(self.sequence, int) or isinstance(self.sequence, bool):
            raise TypeError("sequence must be a plain int")
        if self.sequence < 0:
            raise ValueError("sequence must be non-negative")
        if not isinstance(self.order_id, str):
            raise TypeError("order_id must be a str")
        if not isinstance(self.requester, str):
            raise TypeError("requester must be a str")

    @property
    def kind(self) -> str:
        return EVENT_CANCEL


OrderEvent = Union[PlaceEvent, CancelEvent]


# --- Per-fill receipt record ----------------------------------------------------
@dataclass(frozen=True)
class FillRecord:
    """
    A recorded fill = the matcher's :class:`ClobFill` fields plus a receipt hash.

    DUMB container: it stores what the matcher produced AS-IS plus a precomputed
    ``receipt_hash``. The verifier recomputes the canonical fill (and its hash)
    and compares; this record never recomputes amounts itself.
    """

    base: int
    quote: int
    maker_price: int
    buyer: str
    seller: str
    taker_order_id: str
    maker_order_id: str
    maker_side: str  # ClobSide value ("BUY"/"SELL")
    receipt_hash: str

    @staticmethod
    def from_fill(fill: ClobFill) -> "FillRecord":
        return FillRecord(
            base=fill.base,
            quote=fill.quote,
            maker_price=fill.maker_price,
            buyer=fill.buyer,
            seller=fill.seller,
            taker_order_id=fill.taker_order_id,
            maker_order_id=fill.maker_order_id,
            maker_side=fill.maker_side.value,
            receipt_hash=fill_receipt_hash(fill),
        )


@dataclass(frozen=True)
class PerEventResult:
    """
    The per-event replay record: pre/post book roots, accept-status, fills.

    DUMB container: shape only. For an accepted event ``accepted=True`` and
    ``reject_code is None``; for a rejected event (e.g. a duplicate order_id)
    ``accepted=False``, ``reject_code`` is the matcher's stable code, ``fills``
    is empty, and ``post_book_root == pre_book_root`` (reject-is-no-op). The
    verifier RE-CHECKS all of that; the container does not.
    """

    pre_book_root: str
    post_book_root: str
    accepted: bool
    reject_code: Optional[str]
    fills: Tuple[FillRecord, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.accepted, bool):
            raise TypeError("accepted must be a bool")
        if not isinstance(self.fills, tuple):
            raise TypeError("fills must be a tuple")
        for f in self.fills:
            if not isinstance(f, FillRecord):
                raise TypeError("fills must be FillRecord")


@dataclass(frozen=True)
class ReplayReceipt:
    """
    The full replay receipt = events, per-event results, final root, rule pins.

    DUMB container: shape only, NO cross-field consistency check. The
    ``replay_root`` is stored as claimed; :func:`verify_replay` recomputes it and
    every other field by re-executing the event log from scratch.
    """

    base_asset: str
    quote_asset: str
    matching_rule_hash: str
    fee_rule_hash: str
    events: Tuple[OrderEvent, ...]
    per_event: Tuple[PerEventResult, ...]
    final_book_root: str
    replay_root: str

    def __post_init__(self) -> None:
        if not isinstance(self.events, tuple):
            raise TypeError("events must be a tuple")
        if not isinstance(self.per_event, tuple):
            raise TypeError("per_event must be a tuple")
        for e in self.events:
            if not isinstance(e, (PlaceEvent, CancelEvent)):
                raise TypeError("events must be PlaceEvent/CancelEvent")
        for r in self.per_event:
            if not isinstance(r, PerEventResult):
                raise TypeError("per_event must be PerEventResult")


# --- Canonical hashing ----------------------------------------------------------
def fill_receipt_hash(fill: ClobFill) -> str:
    """
    Domain-separated SHA-256 receipt hash for a single fill.

    Reuses the same encoding primitives as ``ClobBook.state_root`` (uvarint +
    fixed-width hex). Injective over the fill's fields so two distinct fills can
    never collide.
    """
    payload = bytearray(domain_sep_bytes(FILL_DOMAIN_SEP_LABEL, version=FILL_VERSION))
    payload += encode_uvarint(fill.base)
    payload += encode_uvarint(fill.quote)
    payload += encode_uvarint(fill.maker_price)
    payload += hex_to_bytes_fixed(fill.buyer, nbytes=OWNER_NBYTES, name="buyer")
    payload += hex_to_bytes_fixed(fill.seller, nbytes=OWNER_NBYTES, name="seller")
    payload += hex_to_bytes_fixed(fill.taker_order_id, nbytes=ORDER_ID_NBYTES, name="taker_order_id")
    payload += hex_to_bytes_fixed(fill.maker_order_id, nbytes=ORDER_ID_NBYTES, name="maker_order_id")
    payload += encode_uvarint(fill.maker_side.code)
    return sha256_hex(bytes(payload))


def _encode_hash_field(payload: bytearray, hex_str: str, name: str) -> None:
    """Append a 0x-prefixed 32-byte hash (root or rule hash) to ``payload``."""
    payload += hex_to_bytes_fixed(hex_str, nbytes=RULE_HASH_NBYTES, name=name)


def _encode_optional_code(payload: bytearray, code: Optional[str]) -> None:
    """Append an optional reject code with a presence byte + length prefix.

    Presence byte 0 == absent, 1 == present; injective so a None code can never
    collide with a present code.
    """
    if code is None:
        payload += b"\x00"
        return
    raw = code.encode("ascii")
    payload += b"\x01"
    payload += encode_uvarint(len(raw))
    payload += raw


def _encode_event(payload: bytearray, event: OrderEvent) -> None:
    """Append a canonical encoding of one event (place or cancel)."""
    if isinstance(event, PlaceEvent):
        payload += encode_uvarint(0)  # place tag
        payload += encode_uvarint(event.sequence)
        o = event.order
        payload += encode_uvarint(o.side.code)
        payload += encode_uvarint(o.price_q_per_base)
        payload += encode_uvarint(o.base_qty)
        payload += encode_uvarint(o.sequence)
        payload += hex_to_bytes_fixed(o.order_id, nbytes=ORDER_ID_NBYTES, name="order_id")
        payload += hex_to_bytes_fixed(o.owner, nbytes=OWNER_NBYTES, name="owner")
    elif isinstance(event, CancelEvent):
        payload += encode_uvarint(1)  # cancel tag
        payload += encode_uvarint(event.sequence)
        # order_id/requester are validated by apply_cancel; encode canonically.
        payload += hex_to_bytes_fixed(event.order_id, nbytes=ORDER_ID_NBYTES, name="order_id")
        payload += hex_to_bytes_fixed(event.requester, nbytes=OWNER_NBYTES, name="requester")
    else:  # pragma: no cover - guarded by container types
        raise TypeError("unknown event kind")


def _encode_per_event(payload: bytearray, r: PerEventResult) -> None:
    """Append a canonical encoding of one per-event result."""
    _encode_hash_field(payload, r.pre_book_root, "pre_book_root")
    _encode_hash_field(payload, r.post_book_root, "post_book_root")
    payload += b"\x01" if r.accepted else b"\x00"
    _encode_optional_code(payload, r.reject_code)
    payload += encode_uvarint(len(r.fills))
    for f in r.fills:
        payload += encode_uvarint(f.base)
        payload += encode_uvarint(f.quote)
        payload += encode_uvarint(f.maker_price)
        payload += hex_to_bytes_fixed(f.buyer, nbytes=OWNER_NBYTES, name="buyer")
        payload += hex_to_bytes_fixed(f.seller, nbytes=OWNER_NBYTES, name="seller")
        payload += hex_to_bytes_fixed(f.taker_order_id, nbytes=ORDER_ID_NBYTES, name="taker_order_id")
        payload += hex_to_bytes_fixed(f.maker_order_id, nbytes=ORDER_ID_NBYTES, name="maker_order_id")
        _encode_hash_field(payload, f.receipt_hash, "receipt_hash")


def _compute_replay_root(
    *,
    base_asset: str,
    quote_asset: str,
    matching_rule_hash: str,
    fee_rule_hash: str,
    events: Sequence[OrderEvent],
    per_event: Sequence[PerEventResult],
    final_book_root: str,
) -> str:
    """
    Domain-separated SHA-256 over (assets || rule hashes || events || per_event ||
    final_book_root).

    Binding the rule hashes here is what gives ``fee_rule_hash`` teeth: a claim
    whose ``replay_root`` was computed over a DIFFERENT fee hash no longer matches
    the recomputed root.
    """
    payload = bytearray(domain_sep_bytes(REPLAY_DOMAIN_SEP_LABEL, version=REPLAY_VERSION))
    payload += hex_to_bytes_fixed(base_asset, nbytes=ASSET_NBYTES, name="base_asset")
    payload += hex_to_bytes_fixed(quote_asset, nbytes=ASSET_NBYTES, name="quote_asset")
    _encode_hash_field(payload, matching_rule_hash, "matching_rule_hash")
    _encode_hash_field(payload, fee_rule_hash, "fee_rule_hash")
    payload += encode_uvarint(len(events))
    for e in events:
        _encode_event(payload, e)
    payload += encode_uvarint(len(per_event))
    for r in per_event:
        _encode_per_event(payload, r)
    _encode_hash_field(payload, final_book_root, "final_book_root")
    return sha256_hex(bytes(payload))


# --- Replay engine --------------------------------------------------------------
def _apply_event(book: ClobBook, event: OrderEvent) -> Tuple[ClobBook, PerEventResult]:
    """
    Apply one event through the COMMITTED matcher; build its per-event record.

    Returns the post-book and the per-event result. Reject-is-no-op: a rejected
    event leaves the book unchanged and records ``post == pre``.
    """
    pre_root = book.state_root()
    if isinstance(event, PlaceEvent):
        res = apply_order(book, event.order)
        if isinstance(res, ClobMatchAccepted):
            fills = tuple(FillRecord.from_fill(f) for f in res.fills)
            post = res.book
            record = PerEventResult(
                pre_book_root=pre_root,
                post_book_root=post.state_root(),
                accepted=True,
                reject_code=None,
                fills=fills,
            )
            return post, record
        if isinstance(res, ClobMatchRejected):
            # reject-is-no-op: book unchanged, post_root == pre_root.
            record = PerEventResult(
                pre_book_root=pre_root,
                post_book_root=pre_root,
                accepted=False,
                reject_code=res.reason,
                fills=(),
            )
            return book, record
        raise TypeError("unexpected match result")  # pragma: no cover
    if isinstance(event, CancelEvent):
        res = apply_cancel(book, order_id=event.order_id, requester=event.requester)
        if isinstance(res, ClobCancelAccepted):
            post = res.book
            record = PerEventResult(
                pre_book_root=pre_root,
                post_book_root=post.state_root(),
                accepted=True,
                reject_code=None,
                fills=(),
            )
            return post, record
        if isinstance(res, ClobCancelRejected):
            record = PerEventResult(
                pre_book_root=pre_root,
                post_book_root=pre_root,
                accepted=False,
                reject_code=res.reason,
                fills=(),
            )
            return book, record
        raise TypeError("unexpected cancel result")  # pragma: no cover
    raise TypeError("unknown event kind")  # pragma: no cover


def _canonical_event_order(events: Sequence[OrderEvent]) -> Tuple[OrderEvent, ...]:
    """
    Sort events into canonical replay order by ``sequence`` ONLY.

    Sequences MUST be unique (strict total order). A duplicate sequence is a
    fail-closed error (``ValueError(REJ_DUP_SEQUENCE)``): replay order would
    otherwise depend on caller arrival permutation, breaking determinism.
    """
    seen: set[int] = set()
    for e in events:
        if e.sequence in seen:
            raise ValueError(REJ_DUP_SEQUENCE)
        seen.add(e.sequence)
    return tuple(sorted(events, key=lambda e: e.sequence))


def replay_events(
    events: Sequence[OrderEvent],
    *,
    base_asset: str,
    quote_asset: str,
    matching_rule_hash: str,
    fee_rule_hash: str,
) -> ReplayReceipt:
    """
    Replay an ordered event list through the committed matcher from an EMPTY book.

    Fully deterministic: the only ordering is the ``sequence`` field (NO wall
    clock, NO arrival order). The SAME event multiset yields an identical
    ``replay_root`` regardless of how the caller built the list.

    Records per event the ``pre_book_root``, ``post_book_root``, and fills (each
    with a receipt hash), then binds everything (assets + both rule hashes +
    events + per_event + final_book_root) into ``replay_root``.

    Raises ``ValueError(REJ_DUP_SEQUENCE)`` on a duplicate sequence and
    ``ValueError(REJ_EMPTY_EVENTS)`` on an empty event list.
    """
    if not isinstance(events, (list, tuple)):
        raise TypeError("events must be a sequence")
    for e in events:
        if not isinstance(e, (PlaceEvent, CancelEvent)):
            raise TypeError("each event must be a PlaceEvent or CancelEvent")
    if len(events) == 0:
        raise ValueError(REJ_EMPTY_EVENTS)

    matching_rule_hash = _canonical_rule_hash(matching_rule_hash, "matching_rule_hash")
    fee_rule_hash = _canonical_rule_hash(fee_rule_hash, "fee_rule_hash")

    ordered = _canonical_event_order(events)

    book = ClobBook(base_asset=base_asset, quote_asset=quote_asset, orders=())
    base_asset = book.base_asset  # canonicalized form
    quote_asset = book.quote_asset
    per_event: List[PerEventResult] = []
    for e in ordered:
        book, record = _apply_event(book, e)
        per_event.append(record)

    final_book_root = book.state_root()
    per_event_t = tuple(per_event)
    replay_root = _compute_replay_root(
        base_asset=base_asset,
        quote_asset=quote_asset,
        matching_rule_hash=matching_rule_hash,
        fee_rule_hash=fee_rule_hash,
        events=ordered,
        per_event=per_event_t,
        final_book_root=final_book_root,
    )
    return ReplayReceipt(
        base_asset=base_asset,
        quote_asset=quote_asset,
        matching_rule_hash=matching_rule_hash,
        fee_rule_hash=fee_rule_hash,
        events=ordered,
        per_event=per_event_t,
        final_book_root=final_book_root,
        replay_root=replay_root,
    )


# --- Verifier -------------------------------------------------------------------
def _verify_per_event(
    claimed: PerEventResult, recomputed: PerEventResult
) -> Optional[str]:
    """
    Compare one claimed per-event record against the re-executed one.

    Fixed precedence: accept-status -> reject_code -> pre_root -> post_root ->
    fill count -> each fill's value fields -> each fill's receipt hash. Returns
    the FIRST mismatch's stable code, or ``None`` if identical.
    """
    if claimed.accepted != recomputed.accepted:
        return REJ_ACCEPT_STATUS_MISMATCH
    if claimed.reject_code != recomputed.reject_code:
        return REJ_REJECT_CODE_MISMATCH
    if claimed.pre_book_root != recomputed.pre_book_root:
        return REJ_PRE_ROOT_MISMATCH
    if claimed.post_book_root != recomputed.post_book_root:
        return REJ_POST_ROOT_MISMATCH
    if len(claimed.fills) != len(recomputed.fills):
        return REJ_FILL_COUNT_MISMATCH
    for cf, rf in zip(claimed.fills, recomputed.fills):
        # rf is itself a recomputed FillRecord (with its own canonical hash).
        if (
            cf.base != rf.base
            or cf.quote != rf.quote
            or cf.maker_price != rf.maker_price
            or cf.buyer != rf.buyer
            or cf.seller != rf.seller
            or cf.taker_order_id != rf.taker_order_id
            or cf.maker_order_id != rf.maker_order_id
            or cf.maker_side != rf.maker_side
        ):
            return REJ_FILL_MISMATCH
        if cf.receipt_hash != rf.receipt_hash:
            return REJ_FILL_RECEIPT_MISMATCH
    return None


def verify_replay(claimed_receipt: ReplayReceipt) -> Tuple[bool, Optional[str]]:
    """
    Re-execute a claimed replay from scratch and compare BIT-FOR-BIT.

    ACCEPT (``(True, None)``) iff every recomputed field is identical to the
    claim. On the FIRST mismatch REJECT with a stable code. Single matching path:
    we re-run :func:`replay_events` on the claim's OWN events + rule hashes +
    assets, then compare field-by-field in a FIXED precedence:

        event count
        -> per event (canonical order): accept-status, reject_code,
           pre_root, post_root, fill count, each fill's fields, each fill's
           receipt hash
        -> final_book_root
        -> replay_root

    NEVER raises: any structural exception during re-execution maps to
    ``(False, REJ_REEXEC_ERROR)`` (fail-closed). The verifier compares against the
    claim's events in their CANONICAL (sequence) order, which is exactly what
    ``replay_events`` produces, so a claim that scrambled per-event order against
    its event sequence is caught by the per-event roots/fills.
    """
    if not isinstance(claimed_receipt, ReplayReceipt):
        return (False, REJ_BAD_EVENT)
    try:
        recomputed = replay_events(
            claimed_receipt.events,
            base_asset=claimed_receipt.base_asset,
            quote_asset=claimed_receipt.quote_asset,
            matching_rule_hash=claimed_receipt.matching_rule_hash,
            fee_rule_hash=claimed_receipt.fee_rule_hash,
        )
    except Exception:
        # Fail-closed: any malformed claim (dup sequence, bad rule hash, bad
        # asset, etc.) that prevents clean re-execution is a REJECT, not a raise.
        return (False, REJ_REEXEC_ERROR)

    # Event count first (the claim could carry a divergent per_event length).
    if len(claimed_receipt.per_event) != len(recomputed.per_event):
        return (False, REJ_EVENT_COUNT_MISMATCH)
    if len(claimed_receipt.events) != len(recomputed.events):
        return (False, REJ_EVENT_COUNT_MISMATCH)

    # The claim's events are re-sorted into canonical order by replay_events; to
    # compare per_event positionally, the claim's per_event must line up with the
    # claim's events in THAT canonical order. We pair the claim's per_event with
    # the claim's events as stored, then sort both by event sequence so a claim
    # that mismatched per_event-to-event ordering surfaces as a root/fill diff.
    claimed_pairs = list(zip(claimed_receipt.events, claimed_receipt.per_event))
    claimed_pairs.sort(key=lambda pe: pe[0].sequence)

    for (claimed_evt, claimed_pe), recomputed_pe, recomputed_evt in zip(
        claimed_pairs, recomputed.per_event, recomputed.events
    ):
        # Defensive: the canonical event itself must match (same sequence/shape).
        if claimed_evt.sequence != recomputed_evt.sequence:
            return (False, REJ_EVENT_MISMATCH)
        code = _verify_per_event(claimed_pe, recomputed_pe)
        if code is not None:
            return (False, code)

    if claimed_receipt.final_book_root != recomputed.final_book_root:
        return (False, REJ_FINAL_ROOT_MISMATCH)
    if claimed_receipt.replay_root != recomputed.replay_root:
        return (False, REJ_REPLAY_ROOT_MISMATCH)

    return (True, None)
