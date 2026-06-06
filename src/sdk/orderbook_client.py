"""
Python-bot SDK for the Stage-0 proof-carrying orderbook (in-process client).

This is the FIRST SDK per the owner decision (Python bot before browser/TS). It
gives a bot:

* typed dataclasses for the order / fill / market / proof-policy responses, so a
  bot reads ``resp.status`` / ``resp.proof_status`` instead of dict-spelunking;
* a single, FAIL-CLOSED finality helper :func:`is_final` that returns True ONLY
  on ``proof_verified`` and NEVER falls through to final on an unknown status;
* a thin in-process :class:`OrderbookClient` that wraps
  :func:`src.integration.orderbook_api.handle_orderbook_request` for Stage 0
  (no network transport — that wiring is deferred with the HTTP layer).

The finality contract is the whole point of the SDK: a bot MUST treat a result
as final ONLY when a client has verified proof material. Stage 0 never produces
proof material, so :func:`is_final` is always False here — by design, not by bug.

CBC discipline: pure typed values; the finality predicate is a positive equality
test (fail-closed), never a negation of a known set.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple, Union

from ..core.orderbook_status import OrderStatus, ProofStatus
from ..core.orderbook_status import is_final as _status_is_final
from ..integration.orderbook_api import (
    OrderbookStore,
    handle_orderbook_request,
    new_demo_store,
)

__all__ = [
    "OrderResponse",
    "FillResponse",
    "MarketResponse",
    "ProofPolicyResponse",
    "ApiError",
    "OrderbookClient",
    "is_final",
    "FINAL_STATUS",
]

# The single status string a bot may treat as final.
FINAL_STATUS: str = OrderStatus.PROOF_VERIFIED.value


@dataclass(frozen=True)
class OrderResponse:
    """Typed view of one order receipt from the orderbook API."""

    order_id: str
    client_order_id: str
    market_id: str
    side: str
    status: str
    proof_status: str
    request_receipt_hash: str
    sequence: int
    height: int
    latest_proven_height: Optional[int]
    price: str
    quantity: str
    filled_base: str
    resting_base: str
    non_claims: Tuple[str, ...]
    raw: Dict[str, Any]

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "OrderResponse":
        return OrderResponse(
            order_id=str(d.get("order_id", "")),
            client_order_id=str(d.get("client_order_id", "")),
            market_id=str(d.get("market_id", "")),
            side=str(d.get("side", "")),
            status=str(d.get("status", "")),
            proof_status=str(d.get("proof_status", "")),
            request_receipt_hash=str(d.get("request_receipt_hash", "")),
            sequence=int(d.get("sequence", 0)),
            height=int(d.get("height", 0)),
            latest_proven_height=d.get("latest_proven_height"),
            price=str(d.get("price", "")),
            quantity=str(d.get("quantity", "")),
            filled_base=str(d.get("filled_base", "")),
            resting_base=str(d.get("resting_base", "")),
            non_claims=tuple(d.get("non_claims", ()) or ()),
            raw=dict(d),
        )


@dataclass(frozen=True)
class FillResponse:
    """Typed view of one fill receipt."""

    fill_id: str
    market_id: str
    taker_order_id: str
    maker_order_id: str
    price: str
    base: str
    quote: str
    status: str
    proof_status: str
    pre_book_root: str
    post_book_root: str
    raw: Dict[str, Any]

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "FillResponse":
        return FillResponse(
            fill_id=str(d.get("fill_id", "")),
            market_id=str(d.get("market_id", "")),
            taker_order_id=str(d.get("taker_order_id", "")),
            maker_order_id=str(d.get("maker_order_id", "")),
            price=str(d.get("price", "")),
            base=str(d.get("base", "")),
            quote=str(d.get("quote", "")),
            status=str(d.get("status", "")),
            proof_status=str(d.get("proof_status", "")),
            pre_book_root=str(d.get("pre_book_root", "")),
            post_book_root=str(d.get("post_book_root", "")),
            raw=dict(d),
        )


@dataclass(frozen=True)
class MarketResponse:
    """Typed view of market metadata."""

    market_id: str
    base_asset: str
    quote_asset: str
    base_decimals: int
    quote_decimals: int
    price_tick_size: str
    quantity_step_size: str
    min_order_size: str
    matching_rule_hash: str
    fee_rule_hash: str
    book_root: Optional[str]
    latest_height: int
    latest_proven_height: Optional[int]
    data_status: str
    raw: Dict[str, Any]

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "MarketResponse":
        return MarketResponse(
            market_id=str(d.get("market_id", "")),
            base_asset=str(d.get("base_asset", "")),
            quote_asset=str(d.get("quote_asset", "")),
            base_decimals=int(d.get("base_decimals", 0)),
            quote_decimals=int(d.get("quote_decimals", 0)),
            price_tick_size=str(d.get("price_tick_size", "")),
            quantity_step_size=str(d.get("quantity_step_size", "")),
            min_order_size=str(d.get("min_order_size", "")),
            matching_rule_hash=str(d.get("matching_rule_hash", "")),
            fee_rule_hash=str(d.get("fee_rule_hash", "")),
            book_root=d.get("book_root"),
            latest_height=int(d.get("latest_height", 0)),
            latest_proven_height=d.get("latest_proven_height"),
            data_status=str(d.get("data_status", "")),
            raw=dict(d),
        )


@dataclass(frozen=True)
class ProofPolicyResponse:
    """Typed view of the proof policy."""

    proof_mode: str
    accepted_verifier_ids: Tuple[str, ...]
    accepted_rulebook_hash: str
    latest_proven_height: Optional[int]
    non_claims: Tuple[str, ...]
    raw: Dict[str, Any]

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> "ProofPolicyResponse":
        return ProofPolicyResponse(
            proof_mode=str(d.get("proof_mode", "")),
            accepted_verifier_ids=tuple(d.get("accepted_verifier_ids", ()) or ()),
            accepted_rulebook_hash=str(d.get("accepted_rulebook_hash", "")),
            latest_proven_height=d.get("latest_proven_height"),
            non_claims=tuple(d.get("non_claims", ()) or ()),
            raw=dict(d),
        )


@dataclass(frozen=True)
class ApiError:
    """A non-2xx orderbook response (a rejected/expired/not-found result)."""

    http_status: int
    error: str
    status: Optional[str]
    raw: Dict[str, Any]


def is_final(value: Union[OrderResponse, str, ProofStatus, OrderStatus, None]) -> bool:
    """
    Return True iff ``value`` represents the single final status (``proof_verified``).

    FAIL-CLOSED: this is a positive equality test. An :class:`OrderResponse` is
    final only if its ``status`` equals ``proof_verified``; a bare status string
    is final only if it equals ``proof_verified``. Any unknown / unrecognized
    status string, ``None``, an :class:`ApiError`, or any other type returns
    False — the helper NEVER falls through to final on an unrecognized status.

    Stage 0 never emits ``proof_verified``, so this is always False in Stage 0.
    """
    if isinstance(value, OrderResponse):
        return value.status == FINAL_STATUS
    if isinstance(value, ProofStatus):
        return value is ProofStatus.PROOF_VERIFIED
    # Delegate string / OrderStatus handling to the core predicate (fail-closed).
    return _status_is_final(value)


class OrderbookClient:
    """
    Thin in-process Stage-0 client wrapping :func:`handle_orderbook_request`.

    The HTTP transport is deferred (Stage 0), so this client calls the handler
    directly against an injected :class:`OrderbookStore`. A real bot swaps this
    for an HTTP-backed client with the SAME typed surface once the transport
    follow-on lands; the finality contract (:func:`is_final`) does not change.
    """

    def __init__(self, store: Optional[OrderbookStore] = None) -> None:
        self._store = store if store is not None else new_demo_store()

    @property
    def store(self) -> OrderbookStore:
        return self._store

    # --- low-level ---
    def _request(
        self, method: str, path: str, body: Optional[bytes]
    ) -> Tuple[int, Dict[str, Any]]:
        return handle_orderbook_request(method, path, body, store=self._store)

    # --- orders ---
    def place_order(self, request: Dict[str, Any]) -> Union[OrderResponse, ApiError]:
        import json

        status, resp = self._request(
            "POST", "/api/orderbook/orders", json.dumps(request).encode("utf-8")
        )
        if resp.get("ok") and isinstance(resp.get("order"), dict):
            return OrderResponse.from_dict(resp["order"])
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def get_order(self, order_id: str) -> Union[OrderResponse, ApiError]:
        status, resp = self._request("GET", f"/api/orderbook/orders/{order_id}", None)
        if resp.get("ok") and isinstance(resp.get("order"), dict):
            return OrderResponse.from_dict(resp["order"])
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def list_orders(self, market: Optional[str] = None) -> Union[List[OrderResponse], ApiError]:
        path = "/api/orderbook/orders"
        if market is not None:
            path += f"?market={market}"
        status, resp = self._request("GET", path, None)
        if resp.get("ok") and isinstance(resp.get("orders"), list):
            return [OrderResponse.from_dict(o) for o in resp["orders"]]
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def cancel_order(
        self, order_id: str, agent_key_id: Optional[str] = None
    ) -> Union[OrderResponse, ApiError]:
        import json

        body = None
        if agent_key_id is not None:
            body = json.dumps({"agent_key_id": agent_key_id}).encode("utf-8")
        status, resp = self._request("DELETE", f"/api/orderbook/orders/{order_id}", body)
        if resp.get("ok") and isinstance(resp.get("order"), dict):
            return OrderResponse.from_dict(resp["order"])
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    # --- markets / fills / proof-policy ---
    def get_market(self, market_id: str) -> Union[MarketResponse, ApiError]:
        status, resp = self._request("GET", f"/api/orderbook/markets/{market_id}", None)
        if resp.get("ok") and isinstance(resp.get("market"), dict):
            return MarketResponse.from_dict(resp["market"])
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def list_markets(self) -> Union[List[MarketResponse], ApiError]:
        status, resp = self._request("GET", "/api/orderbook/markets", None)
        if resp.get("ok") and isinstance(resp.get("markets"), list):
            return [MarketResponse.from_dict(m) for m in resp["markets"]]
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def list_fills(self, market: Optional[str] = None) -> Union[List[FillResponse], ApiError]:
        path = "/api/orderbook/fills"
        if market is not None:
            path += f"?market={market}"
        status, resp = self._request("GET", path, None)
        if resp.get("ok") and isinstance(resp.get("fills"), list):
            return [FillResponse.from_dict(f) for f in resp["fills"]]
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)

    def proof_policy(self) -> Union[ProofPolicyResponse, ApiError]:
        status, resp = self._request("GET", "/api/orderbook/proof-policy", None)
        if resp.get("ok"):
            return ProofPolicyResponse.from_dict(resp)
        return ApiError(status, str(resp.get("error", "")), resp.get("status"), resp)
