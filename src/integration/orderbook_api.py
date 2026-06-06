"""
Stage 0 proof-carrying orderbook HTTP handler (self-contained, non-persistent).

This is STAGE 0 of ``docs/product_discipline/proof_carrying_orderbook_build_spec.md``:
the bot-compatible REST *shape* over the EXISTING matching kernel, with honest
finality labels. It wires on top of — and does NOT reimplement — the committed
matcher:

* matching transition: :func:`src.core.clob_matching.apply_order` /
  :func:`~src.core.clob_matching.apply_cancel`;
* canonical book + ``state_root``: :class:`src.state.clob_book.ClobBook`;
* intent shape validation: :class:`src.state.intents.ClobOrderIntent` via
  :func:`src.core.clob_intent_normal_form.clob_order_from_intent`.

Stage 0 honesty (LABELLED, not hidden):

* **Non-persistent.** The store is an in-memory object created per process /
  injected per call. Nothing is durable. ``data_status = live_unproven``.
* **No proof.** Every proof field is ``proof_pending`` / ``not_available`` and
  ``latest_proven_height`` is ``null``. No response implies trustless finality;
  ``is_final`` is reserved for ``proof_verified``, which Stage 0 never emits.
* **Signature is NOT cryptographically verified.** ``signature`` must be a
  well-formed hex field, but v1 only checks shape. Authority binding is deferred.
* **LIMIT-ONLY.** ``order_type`` other than ``"limit"`` is rejected
  (``unsupported_order_type``). Market / IOC orders are out of Stage 0 scope.
* **Cancellation is sequenced as an order event** (it consumes a store sequence
  number), matching the owner decision and the spec's event-log model.
* **HTTP transport wiring into ``api_server.py`` is DEFERRED** — this module is
  tested by DIRECT function calls (:func:`handle_orderbook_request`).

The request → ``ClobOrder`` enrichment (the real work) is one deterministic
helper, :func:`_build_clob_order`. The canonical request fields are NOT the
``ClobOrder`` fields; see that helper for every derivation
(``client_order_id`` → derived 32-byte ``order_id``, ``market_id`` →
base/quote assets, base-unit *strings* → ints, store-assigned ``sequence``).

CBC discipline: pure-ish over an injectable store; integer/checked arithmetic;
typed domain values; stable reject codes; reject-is-no-op (a rejected submit /
cancel / idempotency-conflict mutates neither the store nor any book);
deterministic (no wall clock — ``now`` is injected).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, replace
from typing import Any, Dict, List, Optional, Tuple

from ..core.clob_intent_normal_form import (
    ClobIntentNormalFormError,
    clob_order_from_intent,
)
from ..core.clob_matching import (
    ClobCancelAccepted,
    ClobFill,
    ClobMatchAccepted,
    apply_cancel,
    apply_order,
)
from ..core.orderbook_status import DataStatus, OrderStatus, ProofStatus
from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.clob_book import (
    MAX_BASE_QTY,
    MAX_PRICE_Q_PER_BASE,
    ClobBook,
    ClobOrder,
)
from ..state.intents import ClobOrderIntent, Intent, IntentKind

__all__ = [
    "OrderbookStore",
    "MarketMeta",
    "OrderRecord",
    "FillRecord",
    "handle_orderbook_request",
    "new_demo_store",
    # Stable reject codes (exported for tests / callers).
    "REJ_INVALID_JSON",
    "REJ_EMPTY_BODY",
    "REJ_BODY_TOO_LARGE",
    "REJ_BAD_SHAPE",
    "REJ_UNSUPPORTED_ORDER_TYPE",
    "REJ_EXPIRED",
    "REJ_IDEMPOTENCY_CONFLICT",
    "REJ_UNKNOWN_MARKET",
    "REJ_NOT_FOUND",
    "REJ_METHOD_NOT_ALLOWED",
    "REJ_MATCH_PREFIX",
    "REJ_CANCEL_PREFIX",
]

# --- limits & stable reject codes ---------------------------------------------
MAX_POST_BODY = 1 << 16  # 64 KiB Stage-0 request cap

REJ_INVALID_JSON = "invalid_json"
REJ_EMPTY_BODY = "empty_body"
REJ_BODY_TOO_LARGE = "body_too_large"
REJ_BAD_SHAPE = "bad_shape"
REJ_UNSUPPORTED_ORDER_TYPE = "unsupported_order_type"
REJ_EXPIRED = "expired"
REJ_IDEMPOTENCY_CONFLICT = "idempotency_conflict"
REJ_UNKNOWN_MARKET = "unknown_market"
REJ_NOT_FOUND = "not_found"
REJ_METHOD_NOT_ALLOWED = "method_not_allowed"
REJ_BAD_AGENT_KEY = "bad_agent_key_id"
REJ_BAD_SIGNATURE = "bad_signature"
# Underlying-kernel reject codes are re-surfaced with a prefix so the API caller
# can tell a matching/cancel reject from a shape reject without losing the code.
REJ_MATCH_PREFIX = "match:"
REJ_CANCEL_PREFIX = "cancel:"

# Stage-0 honest non-claim labels. Reused verbatim in every response and in the
# proof-policy endpoint so the surface never implies finality.
NON_CLAIMS: Tuple[str, ...] = (
    "no_zk_proof_produced_in_stage_0",
    "signature_well_formed_only_not_cryptographically_verified",
    "sequence_is_store_assigned_not_canonical_intent_order",
    "store_is_in_memory_non_persistent",
    "executed_means_locally_applied_not_client_verified",
    "no_response_implies_trustless_finality",
)

ResponseT = Tuple[int, Dict[str, Any]]

# Deterministic Stage-0 rule hashes. These are stable constants (the matching
# rule is the committed clob_matching kernel; fees are 0 in v1 — ClobFill has no
# fee field — so fee_rule_hash is a stub label). The SAME matching_rule_hash is
# the proof-policy accepted_rulebook_hash.
MATCHING_RULE_HASH = sha256_hex(
    domain_sep_bytes("clob_matching_rule", version=1) + b"price_time_priority_resting_maker_limit_floor_quote"
)
FEE_RULE_HASH = sha256_hex(
    domain_sep_bytes("clob_fee_rule", version=1) + b"stage0_zero_fee_stub"
)

_AGENT_KEY_NBYTES = 48  # agent_key_id IS the owner BLS pubkey (48-byte) in Stage 0


# --- store domain types --------------------------------------------------------
@dataclass(frozen=True)
class MarketMeta:
    """Static market metadata exposed to clients (precision + rule hashes)."""

    market_id: str
    base_asset: str  # 32-byte hex
    quote_asset: str  # 32-byte hex
    base_decimals: int
    quote_decimals: int
    price_tick_size: int
    quantity_step_size: int
    min_order_size: int


@dataclass(frozen=True)
class OrderRecord:
    """One submitted order's stored receipt (Stage 0 in-memory)."""

    order_id: str  # derived 32-byte hex; the GET/DELETE resource id
    client_order_id: str
    agent_key_id: str  # owner pubkey
    market_id: str
    side: str
    price: int
    quantity: int
    filled_base: int
    resting_base: int
    sequence: int
    request_receipt_hash: str
    status: str  # OrderStatus value
    proof_status: str  # ProofStatus value
    height: int


@dataclass(frozen=True)
class FillRecord:
    """One executed fill receipt (Stage 0 in-memory)."""

    fill_id: str  # derived 32-byte hex
    market_id: str
    taker_order_id: str
    maker_order_id: str
    price: int
    base: int
    quote: int
    buyer: str
    seller: str
    pre_book_root: str
    post_book_root: str
    height: int
    status: str
    proof_status: str


@dataclass
class OrderbookStore:
    """
    Injectable in-memory Stage-0 store (NON-PERSISTENT — labelled).

    Holds market metadata, per-market :class:`ClobBook` state, order/fill
    receipts, the idempotency index, and the monotonic sequence/height counters.
    It is a plain mutable shell; the authority math stays in the matching kernel.
    Mutation happens ONLY on an accepted submit/cancel; every reject path leaves
    this object byte-identical (reject-is-no-op).
    """

    markets: Dict[str, MarketMeta] = field(default_factory=dict)
    books: Dict[str, ClobBook] = field(default_factory=dict)
    orders: Dict[str, OrderRecord] = field(default_factory=dict)  # order_id -> record
    fills: Dict[str, FillRecord] = field(default_factory=dict)  # fill_id -> record
    # idempotency: (agent_key_id, market_id, client_order_id) -> (request_hash, order_id)
    idempotency: Dict[Tuple[str, str, str], Tuple[str, str]] = field(default_factory=dict)
    seq_counter: int = 0
    height: int = 0
    # injected logical clock for deterministic expiry checks (unix seconds).
    now: int = 0

    def add_market(self, meta: MarketMeta) -> None:
        self.markets[meta.market_id] = meta
        self.books[meta.market_id] = ClobBook(
            base_asset=meta.base_asset, quote_asset=meta.quote_asset, orders=()
        )

    def next_sequence(self) -> int:
        self.seq_counter += 1
        return self.seq_counter


# --- request shape parsing -----------------------------------------------------
def _parse_json_body(body: Optional[bytes]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    if body is None or len(body) == 0:
        return None, REJ_EMPTY_BODY
    if len(body) > MAX_POST_BODY:
        return None, REJ_BODY_TOO_LARGE
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, REJ_INVALID_JSON
    if not isinstance(obj, dict):
        return None, REJ_INVALID_JSON
    return obj, None


def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _parse_base_unit(value: object) -> Optional[int]:
    """
    Parse a base-unit amount. Spec says amounts/prices are base-unit *strings*;
    we also accept a genuine int (bool excluded). Any non-integer / float / sign
    / malformed string returns None (caller -> bad_shape, no-op). No float path.
    """
    if _is_plain_int(value):
        return value
    if isinstance(value, str):
        s = value.strip()
        if not s or not s.isdigit():  # digits only -> non-negative integer
            return None
        try:
            return int(s)
        except ValueError:
            return None
    return None


def _derive_id(*, domain: str, parts: List[str]) -> str:
    """
    Deterministic 0x-prefixed 32-byte hex id from labelled parts.

    ``sha256_hex`` already returns a ``0x``-prefixed 64-hex-char digest, so the
    result is canonical 32-byte hex without an extra prefix.
    """
    payload = bytearray(domain_sep_bytes(domain, version=1))
    for p in parts:
        pb = p.encode("utf-8")
        payload += len(pb).to_bytes(8, "big")
        payload += pb
    return sha256_hex(bytes(payload))


def _canonical_request_hash(raw: Dict[str, Any]) -> str:
    """
    Canonical-request-hash over the (near-raw) client request.

    Uses ``canonical_json_bytes`` (sorted keys, no whitespace) so dict order does
    not matter. Computed before enrichment so two distinct client payloads can
    never collide to the same derived order and mask a real idempotency conflict.
    The caller passes the raw request with ONLY ``agent_key_id`` canonicalized so
    a hex-case / ``0x`` variant of the same pubkey replays idempotently; every
    other field is hashed exactly as sent (a real semantic change fails closed).
    """
    return sha256_hex(domain_sep_bytes("clob_request", version=1) + canonical_json_bytes(raw))


# --- the enrichment layer: API request -> ClobOrder ----------------------------
@dataclass(frozen=True)
class _BuiltOrder:
    order: ClobOrder
    order_id: str
    sequence: int
    side: str
    price: int
    quantity: int


def _build_clob_order(
    store: OrderbookStore, raw: Dict[str, Any], *, sequence: int
) -> Tuple[Optional[_BuiltOrder], Optional[str]]:
    """
    Deterministically map a canonical API request to a frozen :class:`ClobOrder`.

    Derivations (the crux — see module docstring):

    * ``order_type`` must be ``"limit"`` (LIMIT-ONLY) else
      ``unsupported_order_type``.
    * ``market_id`` -> ``base_asset`` / ``quote_asset`` from the store registry
      (``unknown_market`` if absent).
    * ``client_order_id`` (arbitrary idempotency token) -> a deterministic
      32-byte ``order_id`` = hash(agent_key_id, market_id, client_order_id). The
      book's ``order_id`` is NEVER the client token.
    * ``price`` / ``quantity`` are base-unit strings -> strict non-negative int
      parse (no float path); domain bounds enforced by ``ClobOrder``.
    * ``agent_key_id`` IS the ``owner`` 48-byte pubkey (Stage-0 decision; sig is
      shape-only). Bad 48-byte hex -> ``bad_agent_key_id``.
    * ``sequence`` is STORE-ASSIGNED (monotonic), not the request ``nonce`` — the
      nonce is carried for replay/signature scope but not trusted as ordering.

    Returns ``(_BuiltOrder, None)`` on success or ``(None, reject_code)``. Pure:
    reads the store registry but mutates nothing.
    """
    if not isinstance(raw, dict):
        return None, REJ_BAD_SHAPE

    order_type = raw.get("order_type")
    if order_type != "limit":
        return None, REJ_UNSUPPORTED_ORDER_TYPE

    market_id = raw.get("market_id")
    if not isinstance(market_id, str) or not market_id:
        return None, REJ_BAD_SHAPE
    meta = store.markets.get(market_id)
    if meta is None:
        return None, REJ_UNKNOWN_MARKET

    client_order_id = raw.get("client_order_id")
    if not isinstance(client_order_id, str) or not client_order_id:
        return None, REJ_BAD_SHAPE

    agent_key_id = raw.get("agent_key_id")
    if not isinstance(agent_key_id, str) or not agent_key_id:
        return None, REJ_BAD_SHAPE
    try:
        owner = canonical_hex_fixed_allow_0x(agent_key_id, nbytes=_AGENT_KEY_NBYTES, name="agent_key_id")
    except (TypeError, ValueError):
        return None, REJ_BAD_AGENT_KEY

    # signature must be present and well-formed hex (NOT cryptographically verified
    # — labelled). "Well-formed" = 0x-prefixed, even-length, all hex digits; this is
    # shape only, authority binding is deferred (so e.g. "0xZZ" is rejected as the
    # claim says, but a valid-hex signature is NOT checked against any key).
    signature = raw.get("signature")
    if not isinstance(signature, str) or not signature.startswith("0x") or len(signature) < 4:
        return None, REJ_BAD_SIGNATURE
    _sig_hex = signature[2:]
    if len(_sig_hex) % 2 != 0:
        return None, REJ_BAD_SIGNATURE
    try:
        bytes.fromhex(_sig_hex)
    except ValueError:
        return None, REJ_BAD_SIGNATURE

    side = raw.get("side")
    if side not in ("BUY", "SELL"):
        return None, REJ_BAD_SHAPE

    price = _parse_base_unit(raw.get("price"))
    quantity = _parse_base_unit(raw.get("quantity"))
    if price is None or quantity is None:
        return None, REJ_BAD_SHAPE
    if not (1 <= price <= MAX_PRICE_Q_PER_BASE) or not (1 <= quantity <= MAX_BASE_QTY):
        return None, REJ_BAD_SHAPE

    # nonce / deadline / time_in_force / expires_at are shape-checked elsewhere;
    # nonce just needs to be a plain int here (carried, not trusted as sequence).
    nonce = raw.get("nonce")
    if not _is_plain_int(nonce) or nonce < 0:
        return None, REJ_BAD_SHAPE

    order_id = _derive_id(domain="clob_order_id", parts=[owner, market_id, client_order_id])
    intent_id = _derive_id(domain="clob_intent_id", parts=[owner, market_id, client_order_id, str(sequence)])

    deadline = raw.get("deadline")
    if not _is_plain_int(deadline):
        return None, REJ_BAD_SHAPE

    # Build the full LIMIT_ORDER intent, then bridge through the committed
    # clob_order_from_intent path (which re-validates + canonicalizes).
    try:
        intent = ClobOrderIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.LIMIT_ORDER,
            intent_id=intent_id,
            sender_pubkey=owner,
            deadline=deadline,
            fields={
                "side": side,
                "price_q_per_base": price,
                "base_qty": quantity,
                "sequence": sequence,
                "order_id": order_id,
                "base_asset": meta.base_asset,
                "quote_asset": meta.quote_asset,
                "owner": owner,
            },
        )
    except (ValueError, TypeError):
        return None, REJ_BAD_SHAPE

    try:
        order = clob_order_from_intent(intent)
    except ClobIntentNormalFormError:
        return None, REJ_BAD_SHAPE

    return (
        _BuiltOrder(
            order=order,
            order_id=order.order_id,
            sequence=sequence,
            side=side,
            price=price,
            quantity=quantity,
        ),
        None,
    )


def _is_expired(store: OrderbookStore, raw: Dict[str, Any]) -> bool:
    """expires_at / deadline strictly in the past (vs injected now) => expired."""
    for key in ("expires_at", "deadline"):
        v = raw.get(key)
        if _is_plain_int(v) and v < store.now:
            return True
    return False


# --- response shaping ----------------------------------------------------------
def _order_response(rec: OrderRecord) -> Dict[str, Any]:
    return {
        "order_id": rec.order_id,
        "client_order_id": rec.client_order_id,
        "agent_key_id": rec.agent_key_id,
        "market_id": rec.market_id,
        "side": rec.side,
        "price": str(rec.price),
        "quantity": str(rec.quantity),
        "filled_base": str(rec.filled_base),
        "resting_base": str(rec.resting_base),
        "sequence": rec.sequence,
        "request_receipt_hash": rec.request_receipt_hash,
        "status": rec.status,
        "proof_status": rec.proof_status,
        "height": rec.height,
        "latest_proven_height": None,
        "non_claims": list(NON_CLAIMS),
    }


def _fill_response(rec: FillRecord) -> Dict[str, Any]:
    return {
        "fill_id": rec.fill_id,
        "market_id": rec.market_id,
        "taker_order_id": rec.taker_order_id,
        "maker_order_id": rec.maker_order_id,
        "price": str(rec.price),
        "base": str(rec.base),
        "quote": str(rec.quote),
        "buyer": rec.buyer,
        "seller": rec.seller,
        "maker_fee": "0",
        "taker_fee": "0",
        "pre_book_root": rec.pre_book_root,
        "post_book_root": rec.post_book_root,
        "matching_rule_hash": MATCHING_RULE_HASH,
        "fee_rule_hash": FEE_RULE_HASH,
        "height": rec.height,
        "status": rec.status,
        "proof_status": rec.proof_status,
        "latest_proven_height": None,
    }


def _market_response(store: OrderbookStore, meta: MarketMeta) -> Dict[str, Any]:
    book = store.books.get(meta.market_id)
    book_root = book.state_root() if book is not None else None
    return {
        "market_id": meta.market_id,
        "base_asset": meta.base_asset,
        "quote_asset": meta.quote_asset,
        "base_decimals": meta.base_decimals,
        "quote_decimals": meta.quote_decimals,
        "price_tick_size": str(meta.price_tick_size),
        "quantity_step_size": str(meta.quantity_step_size),
        "min_order_size": str(meta.min_order_size),
        "matching_rule_hash": MATCHING_RULE_HASH,
        "fee_rule_hash": FEE_RULE_HASH,
        "book_root": book_root,
        "latest_height": store.height,
        "latest_proven_height": None,
        "data_status": DataStatus.LIVE_UNPROVEN.value,
    }


# --- POST /orders --------------------------------------------------------------
def _handle_place_order(store: OrderbookStore, raw_body: Optional[bytes]) -> ResponseT:
    raw, perr = _parse_json_body(raw_body)
    if perr is not None:
        return 400, {"ok": False, "error": perr, "status": OrderStatus.REJECTED.value}

    assert raw is not None  # _parse_json_body contract

    # 1. Identity for idempotency requires agent_key_id/market_id/client_order_id.
    agent_key_id = raw.get("agent_key_id")
    market_id = raw.get("market_id")
    client_order_id = raw.get("client_order_id")
    if not (isinstance(agent_key_id, str) and agent_key_id
            and isinstance(market_id, str) and market_id
            and isinstance(client_order_id, str) and client_order_id):
        return 400, {"ok": False, "error": REJ_BAD_SHAPE, "status": OrderStatus.REJECTED.value}

    # 2. Canonical-request-hash over the RAW request (pre-enrichment). The
    #    idempotency KEY canonicalizes agent_key_id so that hex-case / 0x-prefix
    #    variants of the SAME pubkey map to the SAME key (the derived order_id is
    #    likewise computed from the canonical owner) — otherwise a case variant
    #    would miss the index yet collide on order_id (match:dup_order_id) instead
    #    of replaying idempotently. The request-HASH still covers the raw payload
    #    so a genuinely different request under the same key fails closed.
    try:
        idem_agent = canonical_hex_fixed_allow_0x(agent_key_id, nbytes=_AGENT_KEY_NBYTES, name="agent_key_id")
    except (TypeError, ValueError):
        return 400, {"ok": False, "error": REJ_BAD_AGENT_KEY, "status": OrderStatus.REJECTED.value}
    idem_key = (idem_agent, market_id, client_order_id)
    # Hash over the raw request, but with agent_key_id canonicalized so a hex-case
    # / 0x variant of the SAME pubkey produces the SAME hash (and replays) while a
    # genuinely different field value still changes the hash (fails closed).
    hash_input = dict(raw)
    hash_input["agent_key_id"] = idem_agent
    req_hash = _canonical_request_hash(hash_input)

    # 3. Idempotency short-circuit / fail-closed conflict (BEFORE any execution).
    existing = store.idempotency.get(idem_key)
    if existing is not None:
        stored_hash, stored_order_id = existing
        if stored_hash == req_hash:
            # Same id + same request => return the SAME stored receipt (no re-exec).
            rec = store.orders.get(stored_order_id)
            if rec is not None:
                return 200, {"ok": True, "idempotent_replay": True, "order": _order_response(rec)}
            # Defensive: index without record should not happen; treat as conflict.
        # Same id + different request => fail-closed; no store/book mutation.
        return 409, {
            "ok": False,
            "error": REJ_IDEMPOTENCY_CONFLICT,
            "status": OrderStatus.REJECTED.value,
        }

    # 4. Expiry (deadline/expires_at in the past) => expired, no-op.
    if _is_expired(store, raw):
        return 422, {"ok": False, "error": REJ_EXPIRED, "status": OrderStatus.EXPIRED.value}

    # 5. Build the order WITHOUT consuming a sequence yet (so a shape reject is a
    #    pure no-op). Use a probe sequence; the order_id does not depend on it.
    built, berr = _build_clob_order(store, raw, sequence=store.seq_counter + 1)
    if berr is not None:
        http = 404 if berr == REJ_UNKNOWN_MARKET else 400
        return http, {"ok": False, "error": berr, "status": OrderStatus.REJECTED.value}
    assert built is not None

    book = store.books.get(market_id)
    if book is None:
        return 404, {"ok": False, "error": REJ_UNKNOWN_MARKET, "status": OrderStatus.REJECTED.value}

    pre_root = book.state_root()
    result = apply_order(book, built.order)
    if not isinstance(result, ClobMatchAccepted):
        # Matching reject (e.g. dup_order_id, book_full). Reject-is-no-op: the
        # kernel returned the unchanged book; we commit nothing to the store.
        return 400, {
            "ok": False,
            "error": REJ_MATCH_PREFIX + result.reason,
            "status": OrderStatus.REJECTED.value,
        }

    # 6. Accepted: NOW consume the sequence + height and commit the receipt.
    sequence = store.next_sequence()
    store.height += 1
    height = store.height
    new_book = result.book
    post_root = new_book.state_root()
    store.books[market_id] = new_book

    filled_base = built.quantity - result.resting_taker_qty
    rec = OrderRecord(
        order_id=built.order_id,
        client_order_id=client_order_id,
        agent_key_id=built.order.owner,
        market_id=market_id,
        side=built.side,
        price=built.price,
        quantity=built.quantity,
        filled_base=filled_base,
        resting_base=result.resting_taker_qty,
        sequence=sequence,
        request_receipt_hash=req_hash,
        # EXECUTED = locally applied (NOT final). proof is pending.
        status=OrderStatus.EXECUTED.value,
        proof_status=ProofStatus.PROOF_PENDING.value,
        height=height,
    )
    store.orders[built.order_id] = rec
    store.idempotency[idem_key] = (req_hash, built.order_id)
    _record_fills(store, market_id, result.fills, pre_root, post_root, height)

    return 201, {"ok": True, "idempotent_replay": False, "order": _order_response(rec)}


def _record_fills(
    store: OrderbookStore,
    market_id: str,
    fills: Tuple[ClobFill, ...],
    pre_root: str,
    post_root: str,
    height: int,
) -> None:
    for idx, f in enumerate(fills):
        fill_id = _derive_id(
            domain="clob_fill_id",
            parts=[market_id, f.taker_order_id, f.maker_order_id, str(height), str(idx)],
        )
        store.fills[fill_id] = FillRecord(
            fill_id=fill_id,
            market_id=market_id,
            taker_order_id=f.taker_order_id,
            maker_order_id=f.maker_order_id,
            price=f.maker_price,
            base=f.base,
            quote=f.quote,
            buyer=f.buyer,
            seller=f.seller,
            pre_book_root=pre_root,
            post_book_root=post_root,
            height=height,
            status=OrderStatus.EXECUTED.value,
            proof_status=ProofStatus.PROOF_PENDING.value,
        )


# --- DELETE /orders/{id} -------------------------------------------------------
def _handle_cancel_order(
    store: OrderbookStore, order_id: str, raw_body: Optional[bytes], query: Dict[str, str]
) -> ResponseT:
    rec = store.orders.get(order_id)
    if rec is None:
        return 404, {"ok": False, "error": REJ_NOT_FOUND, "status": OrderStatus.REJECTED.value}

    # requester (owner) for the ownership check: the caller MUST present an
    # agent_key_id (body or ?agent_key_id=). We do NOT fall back to the stored
    # owner -- doing so would let anyone cancel an order by id alone (the
    # ownership check would trivially pass). apply_cancel then enforces the
    # value-layer ownership match requester == resting owner (cryptographic sig
    # binding is still deferred -- labelled; this is value-layer ownership only).
    requester: Optional[str] = None
    if raw_body:
        parsed, _ = _parse_json_body(raw_body)
        if parsed is not None and isinstance(parsed.get("agent_key_id"), str):
            requester = parsed["agent_key_id"]
    if requester is None and isinstance(query.get("agent_key_id"), str):
        requester = query["agent_key_id"]
    if requester is None:
        return 400, {
            "ok": False,
            "error": REJ_CANCEL_PREFIX + "missing_requester",
            "status": OrderStatus.REJECTED.value,
        }

    book = store.books.get(rec.market_id)
    if book is None:
        return 404, {"ok": False, "error": REJ_UNKNOWN_MARKET, "status": OrderStatus.REJECTED.value}

    result = apply_cancel(book, order_id=order_id, requester=requester)
    if not isinstance(result, ClobCancelAccepted):
        # Reject-is-no-op: book unchanged, record untouched.
        return 400, {
            "ok": False,
            "error": REJ_CANCEL_PREFIX + result.reason,
            "status": OrderStatus.REJECTED.value,
        }

    # Cancellation is sequenced as an order event (consumes a sequence + height).
    sequence = store.next_sequence()
    store.height += 1
    store.books[rec.market_id] = result.book
    new_rec = replace(
        rec,
        status=OrderStatus.CANCELLED.value,
        resting_base=0,
        sequence=sequence,
        height=store.height,
    )
    store.orders[order_id] = new_rec
    return 200, {"ok": True, "order": _order_response(new_rec)}


# --- GET handlers --------------------------------------------------------------
def _handle_list_orders(store: OrderbookStore, query: Dict[str, str]) -> ResponseT:
    market = query.get("market")
    recs = [
        _order_response(r)
        for _, r in sorted(store.orders.items())
        if market is None or r.market_id == market
    ]
    return 200, {"ok": True, "orders": recs}


def _handle_get_order(store: OrderbookStore, order_id: str) -> ResponseT:
    rec = store.orders.get(order_id)
    if rec is None:
        return 404, {"ok": False, "error": REJ_NOT_FOUND}
    return 200, {"ok": True, "order": _order_response(rec)}


def _handle_list_fills(store: OrderbookStore, query: Dict[str, str]) -> ResponseT:
    market = query.get("market")
    recs = [
        _fill_response(r)
        for _, r in sorted(store.fills.items())
        if market is None or r.market_id == market
    ]
    return 200, {"ok": True, "fills": recs}


def _handle_get_fill(store: OrderbookStore, fill_id: str) -> ResponseT:
    rec = store.fills.get(fill_id)
    if rec is None:
        return 404, {"ok": False, "error": REJ_NOT_FOUND}
    return 200, {"ok": True, "fill": _fill_response(rec)}


def _handle_list_markets(store: OrderbookStore) -> ResponseT:
    out = [_market_response(store, m) for _, m in sorted(store.markets.items())]
    return 200, {"ok": True, "markets": out}


def _handle_get_market(store: OrderbookStore, market_id: str) -> ResponseT:
    meta = store.markets.get(market_id)
    if meta is None:
        return 404, {"ok": False, "error": REJ_UNKNOWN_MARKET}
    return 200, {"ok": True, "market": _market_response(store, meta)}


def _handle_proof_policy(store: OrderbookStore) -> ResponseT:
    return 200, {
        "ok": True,
        "proof_mode": "pending",
        "accepted_verifier_ids": [],
        "accepted_rulebook_hash": MATCHING_RULE_HASH,
        "latest_proven_height": None,
        "non_claims": list(NON_CLAIMS),
    }


# --- routing -------------------------------------------------------------------
def _split_path(path: str) -> Tuple[str, Dict[str, str]]:
    """Split ``/p?a=b&c=d`` -> ("/p", {"a": "b", "c": "d"}). No urllib needed."""
    if "?" not in path:
        return path, {}
    base, _, qs = path.partition("?")
    query: Dict[str, str] = {}
    for pair in qs.split("&"):
        if not pair:
            continue
        k, _, v = pair.partition("=")
        if k:
            query[k] = v
    return base, query


_ORDERS_PREFIX = "/api/orderbook/orders"
_FILLS_PREFIX = "/api/orderbook/fills"
_MARKETS_PREFIX = "/api/orderbook/markets"
_PROOF_POLICY = "/api/orderbook/proof-policy"


def handle_orderbook_request(
    method: str,
    path: str,
    raw_body: Optional[bytes],
    *,
    store: OrderbookStore,
) -> ResponseT:
    """
    Stage-0 orderbook request dispatcher (DIRECT-call tested; no HTTP transport).

    Returns ``(int_http_status, dict_response)``. The ``store`` is injected so the
    handler is deterministic and non-persistent across processes. Every reject is
    a no-op on ``store`` (and on every per-market book).

    Routes (LIMIT-ONLY):
      * ``POST   /api/orderbook/orders``
      * ``GET    /api/orderbook/orders[?market=]``
      * ``GET    /api/orderbook/orders/{id}``
      * ``DELETE /api/orderbook/orders/{id}``
      * ``GET    /api/orderbook/markets`` / ``/markets/{id}``
      * ``GET    /api/orderbook/fills`` / ``/fills/{id}``
      * ``GET    /api/orderbook/proof-policy``
    """
    if not isinstance(store, OrderbookStore):
        raise TypeError("store must be an OrderbookStore")
    base, query = _split_path(path)
    m = method.upper()

    if base == _PROOF_POLICY:
        if m == "GET":
            return _handle_proof_policy(store)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}

    # --- orders ---
    if base == _ORDERS_PREFIX:
        if m == "POST":
            return _handle_place_order(store, raw_body)
        if m == "GET":
            return _handle_list_orders(store, query)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}
    if base.startswith(_ORDERS_PREFIX + "/"):
        order_id = base[len(_ORDERS_PREFIX) + 1 :]
        if not order_id or "/" in order_id:
            return 404, {"ok": False, "error": REJ_NOT_FOUND}
        if m == "GET":
            return _handle_get_order(store, order_id)
        if m == "DELETE":
            return _handle_cancel_order(store, order_id, raw_body, query)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}

    # --- markets ---
    if base == _MARKETS_PREFIX:
        if m == "GET":
            return _handle_list_markets(store)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}
    if base.startswith(_MARKETS_PREFIX + "/"):
        market_id = base[len(_MARKETS_PREFIX) + 1 :]
        if not market_id or "/" in market_id:
            return 404, {"ok": False, "error": REJ_NOT_FOUND}
        if m == "GET":
            return _handle_get_market(store, market_id)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}

    # --- fills ---
    if base == _FILLS_PREFIX:
        if m == "GET":
            return _handle_list_fills(store, query)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}
    if base.startswith(_FILLS_PREFIX + "/"):
        fill_id = base[len(_FILLS_PREFIX) + 1 :]
        if not fill_id or "/" in fill_id:
            return 404, {"ok": False, "error": REJ_NOT_FOUND}
        if m == "GET":
            return _handle_get_fill(store, fill_id)
        return 405, {"ok": False, "error": REJ_METHOD_NOT_ALLOWED}

    return 404, {"ok": False, "error": REJ_NOT_FOUND}


# --- demo store helper (NON-PERSISTENT) ----------------------------------------
def new_demo_store(*, now: int = 0) -> OrderbookStore:
    """
    Build a Stage-0 in-memory store seeded with one demo market.

    NON-PERSISTENT and for tests / local bots only. ``now`` is the injected
    logical clock (unix seconds) used for the deterministic expiry check.
    """
    store = OrderbookStore(now=now)
    base_asset = "0x" + "11" * 32
    quote_asset = "0x" + "22" * 32
    store.add_market(
        MarketMeta(
            market_id="ZENO-USD",
            base_asset=base_asset,
            quote_asset=quote_asset,
            base_decimals=8,
            quote_decimals=8,
            price_tick_size=1,
            quantity_step_size=1,
            min_order_size=1,
        )
    )
    return store
