"""
Stage-0 orderbook Python-bot SDK tests.

The load-bearing contract: :func:`src.sdk.orderbook_client.is_final` returns True
for EXACTLY ``proof_verified`` and FAILS CLOSED on every other status (including
an unknown status string) — it never falls through to final. Also exercises the
thin in-process client over the injected store.
"""

from typing import Any

from src.core.orderbook_status import OrderStatus
from src.sdk.orderbook_client import (
    ApiError,
    OrderResponse,
    OrderbookClient,
    is_final,
)

ALL_DEFINED_STATUSES = [s.value for s in OrderStatus]
OWNER_A = "0x" + "ab" * 48


def _order_request(**overrides: Any) -> dict:
    req = {
        "market_id": "ZENO-USD",
        "client_order_id": "sdk-1",
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


# --- is_final fail-closed contract --------------------------------------------
def test_is_final_true_only_for_proof_verified_status_string():
    for s in ALL_DEFINED_STATUSES:
        expected = s == OrderStatus.PROOF_VERIFIED.value
        assert is_final(s) is expected, s


def test_is_final_false_on_unknown_status_fails_closed():
    for unknown in [
        "final", "verified", "FINAL", "proof_Verified", "done", "ok",
        "", "settled", "complete", "true", "1", "proof-verified",
    ]:
        assert is_final(unknown) is False, unknown


def test_is_final_false_on_non_string():
    for bad in [None, 0, 1, True, False, object(), [], {}, 3.14]:
        assert is_final(bad) is False, repr(bad)


def test_is_final_on_order_response_only_proof_verified():
    for s in ALL_DEFINED_STATUSES:
        resp = OrderResponse.from_dict({"status": s})
        assert is_final(resp) is (s == OrderStatus.PROOF_VERIFIED.value), s
    # Unknown status on a typed response is still non-final (fail-closed).
    assert is_final(OrderResponse.from_dict({"status": "mystery"})) is False


def test_stage0_executed_order_is_never_final():
    client = OrderbookClient()
    res = client.place_order(_order_request())
    assert isinstance(res, OrderResponse)
    assert res.status == OrderStatus.EXECUTED.value
    assert is_final(res) is False
    assert res.proof_status == "proof_pending"
    assert res.latest_proven_height is None


# --- thin in-process client over the injected store ---------------------------
def test_client_place_get_list_cancel_roundtrip():
    client = OrderbookClient()
    placed = client.place_order(_order_request())
    assert isinstance(placed, OrderResponse)
    oid = placed.order_id

    got = client.get_order(oid)
    assert isinstance(got, OrderResponse)
    assert got.order_id == oid

    orders = client.list_orders()
    assert isinstance(orders, list)
    assert [o.order_id for o in orders] == [oid]

    cancelled = client.cancel_order(oid, agent_key_id=OWNER_A)
    assert isinstance(cancelled, OrderResponse)
    assert cancelled.status == OrderStatus.CANCELLED.value


def test_client_idempotent_replay_and_conflict():
    client = OrderbookClient()
    r1 = client.place_order(_order_request())
    assert isinstance(r1, OrderResponse)
    # Identical payload -> same receipt.
    r2 = client.place_order(_order_request())
    assert isinstance(r2, OrderResponse)
    assert r2.request_receipt_hash == r1.request_receipt_hash
    # Changed payload, same client_order_id -> fail-closed conflict (ApiError).
    r3 = client.place_order(_order_request(price="2000"))
    assert isinstance(r3, ApiError)
    assert r3.http_status == 409
    assert r3.error == "idempotency_conflict"


def test_client_markets_and_proof_policy():
    client = OrderbookClient()
    markets = client.list_markets()
    assert isinstance(markets, list)
    assert markets[0].data_status == "live_unproven"
    assert markets[0].latest_proven_height is None

    policy = client.proof_policy()
    assert not isinstance(policy, ApiError)
    assert policy.proof_mode == "pending"
    assert policy.latest_proven_height is None
    assert policy.accepted_rulebook_hash == markets[0].matching_rule_hash
