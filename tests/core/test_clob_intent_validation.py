"""
Tests for the zk-CLOB v1 limit-order intent type, its bridge, and normal form.

Covers:
  * ClobOrderIntent rejects bool-as-int, non-positive qty/price, missing fields,
    bad side, same base/quote asset (mirrors intents.py _require_int_field).
  * CancelOrderIntent shape validation.
  * clob_order_from_intent bridges a validated intent -> frozen ClobOrder.
  * normalize_clob_orders / normalize_clob_intents uses the matcher replay order.
  * the AMM settlement ingress (operations.py) REJECTS CLOB kinds by design.

All assertions are hard.
"""

import random

import pytest

from src.state.intents import (
    ClobOrderIntent,
    CancelOrderIntent,
    IntentKind,
)
from src.state.clob_book import ClobOrder, ClobSide
from src.core.clob_intent_normal_form import (
    clob_order_from_intent,
    normalize_clob_orders,
    normalize_clob_intents,
    is_in_normal_form,
    ClobIntentNormalFormError,
)

OWNER = "0x" + "aa" * 48
BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32


def _intent_id(n: int) -> str:
    return "0x" + f"{n:064x}"


def _order_id(n: int) -> str:
    return "0x" + f"{n:064x}"


def _base_fields(**overrides):
    f = {
        "side": "BUY",
        "price_q_per_base": 100,
        "base_qty": 10,
        "sequence": 1,
        "order_id": _order_id(1),
        "base_asset": BASE,
        "quote_asset": QUOTE,
        "owner": OWNER,
    }
    f.update(overrides)
    return f


def _make_intent(kind=IntentKind.LIMIT_ORDER, fields=None, intent_n=1):
    return ClobOrderIntent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_intent_id(intent_n),
        sender_pubkey=OWNER,
        deadline=0,
        fields=fields if fields is not None else _base_fields(),
    )


# ---------------------------------------------------------------------------
# Accept
# ---------------------------------------------------------------------------
def test_valid_limit_order_intent_accepts():
    intent = _make_intent()
    assert intent.kind == IntentKind.LIMIT_ORDER
    # base/quote canonicalized in fields
    assert intent.get_field("base_asset") == BASE
    assert intent.get_field("quote_asset") == QUOTE


def test_valid_cancel_order_intent_accepts():
    intent = CancelOrderIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CANCEL_ORDER,
        intent_id=_intent_id(2),
        sender_pubkey=OWNER,
        deadline=0,
        fields={"order_id": _order_id(5)},
    )
    assert intent.kind == IntentKind.CANCEL_ORDER


# ---------------------------------------------------------------------------
# Reject: bool-is-not-int and bounds
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    "overrides",
    [
        {"price_q_per_base": True},   # bool-as-int
        {"price_q_per_base": 0},      # non-positive
        {"price_q_per_base": -5},
        {"base_qty": False},          # bool-as-int
        {"base_qty": 0},              # non-positive
        {"base_qty": -1},
        {"sequence": True},           # bool-as-int
        {"sequence": -1},             # negative
        {"side": "LONG"},             # bad side
        {"side": 1},                  # non-string side
        {"order_id": "0xdead"},       # wrong length
        {"order_id": 123},            # non-string
        {"base_asset": "0xnothex" + "0" * 56},  # invalid hex
    ],
)
def test_limit_order_intent_rejects_malformed_field(overrides):
    with pytest.raises(ValueError):
        _make_intent(fields=_base_fields(**overrides))


def test_limit_order_intent_rejects_same_base_and_quote_asset():
    with pytest.raises(ValueError):
        _make_intent(fields=_base_fields(quote_asset=BASE))


@pytest.mark.parametrize("missing", ["side", "price_q_per_base", "base_qty", "sequence", "order_id", "base_asset", "quote_asset"])
def test_limit_order_intent_rejects_missing_field(missing):
    fields = _base_fields()
    del fields[missing]
    with pytest.raises(ValueError):
        _make_intent(fields=fields)


def test_limit_order_intent_rejects_wrong_kind():
    with pytest.raises(ValueError):
        ClobOrderIntent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,  # wrong kind for ClobOrderIntent
            intent_id=_intent_id(9),
            sender_pubkey=OWNER,
            deadline=0,
            fields=_base_fields(),
        )


# ---------------------------------------------------------------------------
# Bridge intent -> ClobOrder
# ---------------------------------------------------------------------------
def test_clob_order_from_intent_bridges_to_frozen_order():
    intent = _make_intent(fields=_base_fields(side="SELL", price_q_per_base=250, base_qty=7, sequence=3, order_id=_order_id(42)))
    order = clob_order_from_intent(intent)
    assert isinstance(order, ClobOrder)
    assert order.side is ClobSide.SELL
    assert order.price_q_per_base == 250
    assert order.base_qty == 7
    assert order.sequence == 3
    assert order.order_id == _order_id(42)
    assert order.owner == OWNER


def test_clob_order_from_intent_defaults_owner_to_sender():
    fields = _base_fields()
    del fields["owner"]  # owner falls back to sender_pubkey
    intent = _make_intent(fields=fields)
    order = clob_order_from_intent(intent)
    assert order.owner == OWNER


def test_clob_order_from_intent_rejects_non_limit_kind():
    cancel = CancelOrderIntent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CANCEL_ORDER,
        intent_id=_intent_id(3),
        sender_pubkey=OWNER,
        deadline=0,
        fields={"order_id": _order_id(5)},
    )
    with pytest.raises(ClobIntentNormalFormError):
        clob_order_from_intent(cancel)


# ---------------------------------------------------------------------------
# Normal form: deterministic incoming replay order
# ---------------------------------------------------------------------------
def _order(side, price, seq, oid_n, owner_tag="aa"):
    return ClobOrder(
        side=side,
        price_q_per_base=price,
        base_qty=10,
        sequence=seq,
        order_id=_order_id(oid_n),
        owner="0x" + (owner_tag * 48)[:96],
    )


def test_normal_form_is_deterministic_under_permutation():
    orders = [
        _order(ClobSide.BUY, 102, 5, 1),
        _order(ClobSide.BUY, 102, 1, 2),   # earlier seq -> before oid 1
        _order(ClobSide.SELL, 100, 0, 3),
        _order(ClobSide.SELL, 100, 0, 4),  # same seq, tie-break by order_id
        _order(ClobSide.BUY, 99, 9, 5),
    ]
    canonical = normalize_clob_orders(orders).order_ids
    rng = random.Random(2024)
    for _ in range(50):
        shuffled = orders[:]
        rng.shuffle(shuffled)
        assert normalize_clob_orders(shuffled).order_ids == canonical
    assert is_in_normal_form(normalize_clob_orders(orders).orders)


def test_normal_form_same_price_earlier_sequence_first():
    o_late = _order(ClobSide.BUY, 100, 9, 1)
    o_early = _order(ClobSide.BUY, 100, 2, 2)
    nf = normalize_clob_orders([o_late, o_early]).orders
    assert nf[0].order_id == _order_id(2)  # earlier sequence first
    assert nf[1].order_id == _order_id(1)


def test_normal_form_replay_order_ignores_side_and_price():
    # This is load-bearing: apply_orders replays by (sequence, order_id). Sorting
    # incoming batches by resting-book price priority would let a later high-price
    # order execute before an earlier order and change fills.
    later_better_buy = _order(ClobSide.BUY, 500, 9, 1)
    earlier_sell = _order(ClobSide.SELL, 1, 2, 2)
    nf = normalize_clob_orders([later_better_buy, earlier_sell]).orders
    assert [o.order_id for o in nf] == [_order_id(2), _order_id(1)]


def test_normalize_clob_intents_from_intents():
    intents = [
        _make_intent(fields=_base_fields(side="BUY", price_q_per_base=103, sequence=2, order_id=_order_id(1)), intent_n=1),
        _make_intent(fields=_base_fields(side="BUY", price_q_per_base=101, sequence=1, order_id=_order_id(2)), intent_n=2),
    ]
    nf = normalize_clob_intents(intents).order_ids
    # Incoming replay order is sequence first, independent of price.
    assert nf == [_order_id(2), _order_id(1)]


# ---------------------------------------------------------------------------
# Firewall: AMM settlement ingress rejects CLOB kinds by design
# ---------------------------------------------------------------------------
def test_amm_ingress_rejects_limit_order_kind():
    from src.integration.operations import parse_signed_intents

    op = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "LIMIT_ORDER",
                "intent_id": _intent_id(1),
                "sender_pubkey": OWNER,
                "deadline": 0,
                "side": "BUY",
                "price_q_per_base": 100,
                "base_qty": 10,
                "sequence": 1,
                "order_id": _order_id(1),
                "base_asset": BASE,
                "quote_asset": QUOTE,
                "owner": OWNER,
            }
        ]
    }
    with pytest.raises(ValueError):
        parse_signed_intents(op)


def test_amm_ingress_rejects_cancel_order_kind():
    from src.integration.operations import parse_signed_intents

    op = {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "CANCEL_ORDER",
                "intent_id": _intent_id(1),
                "sender_pubkey": OWNER,
                "deadline": 0,
                "order_id": _order_id(1),
            }
        ]
    }
    with pytest.raises(ValueError):
        parse_signed_intents(op)
