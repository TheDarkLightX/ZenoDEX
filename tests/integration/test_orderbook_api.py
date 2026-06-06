"""
Stage-0 proof-carrying orderbook API tests (DIRECT function calls).

Covers the build-spec Stage-0 acceptance + the task's enumerated cases:

* place / list / detail / cancel a limit order;
* idempotency: dup client_order_id + identical payload => SAME receipt;
* idempotency: dup client_order_id + CHANGED payload => fail-closed conflict;
* expired deadline => reject; non-limit order_type => reject; bad shape => reject;
* reject-is-no-op on EVERY reject (store + book root unchanged);
* honesty sweep: EVERY proof field is proof_pending / not_available / null —
  no response implies finality.

These hit :func:`handle_orderbook_request` directly; HTTP transport is deferred.
"""

import json
from typing import Any, Dict, Optional, Tuple

import pytest

from src.core.orderbook_status import OrderStatus, ProofStatus, is_final
from src.integration.orderbook_api import (
    REJ_BAD_SHAPE,
    REJ_EXPIRED,
    REJ_IDEMPOTENCY_CONFLICT,
    REJ_UNSUPPORTED_ORDER_TYPE,
    OrderbookStore,
    handle_orderbook_request,
    new_demo_store,
)

OWNER_A = "0x" + "ab" * 48
OWNER_B = "0x" + "cd" * 48
MARKET = "ZENO-USD"


def _call(
    store: OrderbookStore, method: str, path: str, body: Optional[Dict[str, Any]] = None
) -> Tuple[int, Dict[str, Any]]:
    raw = json.dumps(body).encode("utf-8") if body is not None else None
    return handle_orderbook_request(method, path, raw, store=store)


def _order_request(**overrides: Any) -> Dict[str, Any]:
    req = {
        "market_id": MARKET,
        "client_order_id": "bot-1",
        "side": "BUY",
        "order_type": "limit",
        "price": "1000",
        "quantity": "5",
        "time_in_force": "GTC",
        "expires_at": 0,
        "nonce": 1,
        "deadline": 0,
        "agent_key_id": OWNER_A,
        "signature": "0x" + "ff" * 8,
    }
    req.update(overrides)
    return req


def _book_root(store: OrderbookStore) -> str:
    return store.books[MARKET].state_root()


def _store_snapshot(store: OrderbookStore) -> Tuple[Any, ...]:
    return (
        _book_root(store),
        tuple(sorted(store.orders.keys())),
        tuple(sorted(store.fills.keys())),
        tuple(sorted(store.idempotency.keys())),
        store.seq_counter,
        store.height,
    )


# --- happy path ---------------------------------------------------------------
def test_place_limit_order_executes_and_is_not_final():
    store = new_demo_store()
    status, resp = _call(store, "POST", "/api/orderbook/orders", _order_request())
    assert status == 201, resp
    assert resp["ok"] is True
    order = resp["order"]
    assert order["status"] == OrderStatus.EXECUTED.value
    assert order["proof_status"] == ProofStatus.PROOF_PENDING.value
    assert order["latest_proven_height"] is None
    # EXECUTED is NOT final.
    assert is_final(order["status"]) is False
    assert order["order_id"].startswith("0x")
    assert len(order["order_id"]) == 2 + 64


def test_get_order_and_list_orders():
    store = new_demo_store()
    _, resp = _call(store, "POST", "/api/orderbook/orders", _order_request())
    oid = resp["order"]["order_id"]

    s2, got = _call(store, "GET", f"/api/orderbook/orders/{oid}", None)
    assert s2 == 200
    assert got["order"]["order_id"] == oid

    s3, listed = _call(store, "GET", "/api/orderbook/orders", None)
    assert s3 == 200
    assert [o["order_id"] for o in listed["orders"]] == [oid]

    s4, filtered = _call(store, "GET", f"/api/orderbook/orders?market={MARKET}", None)
    assert s4 == 200
    assert len(filtered["orders"]) == 1
    s5, none = _call(store, "GET", "/api/orderbook/orders?market=NOPE", None)
    assert s5 == 200
    assert none["orders"] == []


def test_cancel_limit_order_sequenced():
    store = new_demo_store()
    _, resp = _call(store, "POST", "/api/orderbook/orders", _order_request())
    oid = resp["order"]["order_id"]
    seq_before = resp["order"]["sequence"]

    s2, cancelled = _call(store, "DELETE", f"/api/orderbook/orders/{oid}", {"agent_key_id": OWNER_A})
    assert s2 == 200, cancelled
    assert cancelled["order"]["status"] == OrderStatus.CANCELLED.value
    # Cancellation is sequenced as an order event (a new sequence was consumed).
    assert cancelled["order"]["sequence"] > seq_before
    # Order left the book.
    assert store.books[MARKET].find_order(oid) is None


def test_two_orders_match_and_produce_fill():
    store = new_demo_store()
    # Resting SELL @ 1000 qty 5.
    _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="maker", side="SELL", price="1000", quantity="5", agent_key_id=OWNER_B))
    # Crossing BUY @ 1000 qty 3 (different owner avoids self-trade).
    s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="taker", side="BUY", price="1000", quantity="3", agent_key_id=OWNER_A))
    assert s == 201, resp
    assert resp["order"]["filled_base"] == "3"

    sf, fills = _call(store, "GET", "/api/orderbook/fills", None)
    assert sf == 200
    assert len(fills["fills"]) == 1
    f = fills["fills"][0]
    assert f["base"] == "3"
    assert f["proof_status"] == ProofStatus.PROOF_PENDING.value
    assert is_final(f.get("status")) is False
    fid = f["fill_id"]
    s1, one = _call(store, "GET", f"/api/orderbook/fills/{fid}", None)
    assert s1 == 200
    assert one["fill"]["fill_id"] == fid


# --- idempotency --------------------------------------------------------------
def test_idempotent_same_payload_returns_same_receipt():
    store = new_demo_store()
    s1, r1 = _call(store, "POST", "/api/orderbook/orders", _order_request())
    assert s1 == 201
    assert r1.get("idempotent_replay") is False
    snap = _store_snapshot(store)

    # Same client_order_id + identical payload (reordered keys must not matter).
    req = _order_request()
    reordered = dict(reversed(list(req.items())))
    s2, r2 = _call(store, "POST", "/api/orderbook/orders", reordered)
    assert s2 == 200
    assert r2.get("idempotent_replay") is True
    assert r2["order"]["order_id"] == r1["order"]["order_id"]
    assert r2["order"]["request_receipt_hash"] == r1["order"]["request_receipt_hash"]
    # Replay did NOT re-apply to the book or grow the store.
    assert _store_snapshot(store) == snap


def test_idempotent_agent_key_case_variant_replays_not_dup():
    # Same pubkey expressed with different hex case / 0x must hit the SAME
    # idempotency key (canonicalized), not collide on order_id as dup.
    store = new_demo_store()
    s1, r1 = _call(store, "POST", "/api/orderbook/orders", _order_request(agent_key_id="0x" + "AB" * 48))
    assert s1 == 201, r1
    snap = _store_snapshot(store)
    s2, r2 = _call(store, "POST", "/api/orderbook/orders", _order_request(agent_key_id="0x" + "ab" * 48))
    assert s2 == 200, r2
    assert r2.get("idempotent_replay") is True
    assert r2["order"]["order_id"] == r1["order"]["order_id"]
    assert _store_snapshot(store) == snap


def test_idempotency_conflict_changed_payload_fails_closed():
    store = new_demo_store()
    _call(store, "POST", "/api/orderbook/orders", _order_request())
    snap = _store_snapshot(store)

    # Same client_order_id, DIFFERENT semantics (price changed) => fail closed.
    s2, r2 = _call(store, "POST", "/api/orderbook/orders", _order_request(price="2000"))
    assert s2 == 409
    assert r2["ok"] is False
    assert r2["error"] == REJ_IDEMPOTENCY_CONFLICT
    # Conflict is a no-op: nothing mutated.
    assert _store_snapshot(store) == snap


# --- rejects (all no-op) ------------------------------------------------------
def test_expired_deadline_rejects_no_op():
    store = new_demo_store(now=1000)
    snap = _store_snapshot(store)
    s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(deadline=999, expires_at=999))
    assert s == 422
    assert resp["error"] == REJ_EXPIRED
    assert resp["status"] == OrderStatus.EXPIRED.value
    assert _store_snapshot(store) == snap


def test_non_limit_order_type_rejects_no_op():
    store = new_demo_store()
    snap = _store_snapshot(store)
    s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(order_type="market"))
    assert s == 400
    assert resp["error"] == REJ_UNSUPPORTED_ORDER_TYPE
    assert _store_snapshot(store) == snap


def test_non_hex_signature_rejects_no_op():
    # "Well-formed hex" is enforced as SHAPE: 0x-prefixed, even-length, all hex
    # digits (it is NOT cryptographically verified in v1). Each malformed form is a
    # fail-closed reject that leaves the store/book untouched.
    store = new_demo_store()
    snap = _store_snapshot(store)
    for bad_sig in ("0xZZZZ", "0xfff", "ffffffffffff", "0x"):
        s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(signature=bad_sig))
        assert s >= 400, bad_sig
        assert resp["error"] == "bad_signature", bad_sig
        assert _store_snapshot(store) == snap, bad_sig


@pytest.mark.parametrize(
    "overrides",
    [
        {"side": "WRONG"},
        {"price": "1.5"},  # non-integer base-unit string
        {"price": "-3"},  # signed not allowed
        {"quantity": "0"},  # below min domain (1)
        {"price": "abc"},  # not hex/digits
        {"agent_key_id": "0xdead"},  # bad 48-byte pubkey
        {"nonce": -1},  # bad nonce
    ],
)
def test_bad_shape_rejects_no_op(overrides):
    store = new_demo_store()
    snap = _store_snapshot(store)
    s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(**overrides))
    assert s in (400, 422), resp
    assert resp["ok"] is False
    assert resp["status"] == OrderStatus.REJECTED.value or resp["status"] == OrderStatus.EXPIRED.value
    assert _store_snapshot(store) == snap


def test_empty_and_malformed_body_reject_no_op():
    store = new_demo_store()
    snap = _store_snapshot(store)
    s1, r1 = handle_orderbook_request("POST", "/api/orderbook/orders", None, store=store)
    assert s1 == 400 and r1["ok"] is False
    s2, r2 = handle_orderbook_request("POST", "/api/orderbook/orders", b"{not json", store=store)
    assert s2 == 400 and r2["ok"] is False
    assert _store_snapshot(store) == snap


def test_self_trade_match_reject_no_op():
    store = new_demo_store()
    # Rest a SELL by OWNER_A.
    _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="rest", side="SELL", price="1000", quantity="5", agent_key_id=OWNER_A))
    snap = _store_snapshot(store)
    # Crossing BUY by the SAME owner => self_trade, surfaced as match:self_trade, no-op.
    s, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="cross", side="BUY", price="1000", quantity="3", agent_key_id=OWNER_A))
    assert s == 400
    assert resp["error"].startswith("match:")
    assert _store_snapshot(store) == snap


def test_cancel_unknown_order_404_no_op():
    store = new_demo_store()
    snap = _store_snapshot(store)
    s, resp = _call(store, "DELETE", "/api/orderbook/orders/0x" + "00" * 32, {"agent_key_id": OWNER_A})
    assert s == 404
    assert _store_snapshot(store) == snap


def test_cancel_wrong_owner_reject_no_op():
    store = new_demo_store()
    _, resp = _call(store, "POST", "/api/orderbook/orders", _order_request(agent_key_id=OWNER_A))
    oid = resp["order"]["order_id"]
    snap = _store_snapshot(store)
    s, cresp = _call(store, "DELETE", f"/api/orderbook/orders/{oid}", {"agent_key_id": OWNER_B})
    assert s == 400
    assert cresp["error"].startswith("cancel:")
    assert _store_snapshot(store) == snap


# --- markets / proof-policy ---------------------------------------------------
def test_markets_expose_precision_and_rule_hashes():
    store = new_demo_store()
    s, resp = _call(store, "GET", "/api/orderbook/markets", None)
    assert s == 200
    m = resp["markets"][0]
    for key in (
        "base_asset", "quote_asset", "base_decimals", "quote_decimals",
        "price_tick_size", "quantity_step_size", "min_order_size",
        "matching_rule_hash", "fee_rule_hash", "book_root",
        "latest_height", "latest_proven_height", "data_status",
    ):
        assert key in m, key
    assert m["latest_proven_height"] is None
    assert m["data_status"] == "live_unproven"

    s2, one = _call(store, "GET", f"/api/orderbook/markets/{MARKET}", None)
    assert s2 == 200
    assert one["market"]["market_id"] == MARKET
    s3, miss = _call(store, "GET", "/api/orderbook/markets/NOPE", None)
    assert s3 == 404


def test_proof_policy_is_pending_and_honest():
    store = new_demo_store()
    s, resp = _call(store, "GET", "/api/orderbook/proof-policy", None)
    assert s == 200
    assert resp["proof_mode"] == "pending"
    assert resp["accepted_verifier_ids"] == []
    assert resp["latest_proven_height"] is None
    # accepted_rulebook_hash == market matching_rule_hash.
    _, mresp = _call(store, "GET", f"/api/orderbook/markets/{MARKET}", None)
    assert resp["accepted_rulebook_hash"] == mresp["market"]["matching_rule_hash"]
    assert len(resp["non_claims"]) > 0


# --- the honesty sweep: NO response implies finality --------------------------
def _assert_no_finality(obj: Any) -> None:
    """Recursively assert no proof_status implies finality and no proven height."""
    if isinstance(obj, dict):
        ps = obj.get("proof_status")
        if ps is not None:
            assert ps in (ProofStatus.PROOF_PENDING.value, ProofStatus.NOT_AVAILABLE.value), ps
        st = obj.get("status")
        if st is not None and isinstance(st, str):
            assert is_final(st) is False, st
        if "latest_proven_height" in obj:
            assert obj["latest_proven_height"] is None
        for v in obj.values():
            _assert_no_finality(v)
    elif isinstance(obj, list):
        for v in obj:
            _assert_no_finality(v)


def test_every_response_is_non_final():
    store = new_demo_store()
    # Build a populated state: a fill, a resting order.
    _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="maker", side="SELL", price="1000", quantity="5", agent_key_id=OWNER_B))
    _call(store, "POST", "/api/orderbook/orders", _order_request(
        client_order_id="taker", side="BUY", price="1000", quantity="3", agent_key_id=OWNER_A))

    endpoints = [
        ("GET", "/api/orderbook/orders"),
        ("GET", "/api/orderbook/fills"),
        ("GET", "/api/orderbook/markets"),
        ("GET", f"/api/orderbook/markets/{MARKET}"),
        ("GET", "/api/orderbook/proof-policy"),
    ]
    for method, path in endpoints:
        _, resp = _call(store, method, path, None)
        _assert_no_finality(resp)

    # Also the POST receipt itself.
    _, post = _call(store, "POST", "/api/orderbook/orders", _order_request(client_order_id="z"))
    _assert_no_finality(post)
