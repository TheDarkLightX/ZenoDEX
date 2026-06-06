"""
Tests for the CLOB book commitment layer (src/state/clob_book.py).

Gates (commitment-layer-first, before any matching exists):
  * state_root is insertion-order independent (canonicalization);
  * the root changes iff the resting multiset changes;
  * sorted-level / strict-total-order invariant (price-time);
  * sparse: an empty book has a distinct, stable root;
  * order field validity (bad price/qty/side/sequence/order_id/owner);
  * duplicate order_id and over-capacity rejection.

All assertions are hard.
"""

import random

import pytest

from src.state.clob_book import (
    PRICE_SCALE,
    MAX_PRICE_Q_PER_BASE,
    MAX_BASE_QTY,
    MAX_SEQUENCE,
    ClobBook,
    ClobOrder,
    ClobSide,
    order_priority_key,
    validate_order_fields,
    REJ_BAD_PRICE,
    REJ_BAD_QTY,
    REJ_BAD_SIDE,
    REJ_BAD_SEQUENCE,
    REJ_BAD_ORDER_ID,
    REJ_BAD_OWNER,
    REJ_DUP_ORDER_ID,
)

BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32


def _owner(tag: str) -> str:
    return "0x" + (tag * 48)[:96]


def _oid(n: int) -> str:
    return "0x" + f"{n:064x}"


def mk(side, price, qty, seq, oid_n, owner_tag="aa"):
    return ClobOrder(
        side=side,
        price_q_per_base=price,
        base_qty=qty,
        sequence=seq,
        order_id=_oid(oid_n),
        owner=_owner(owner_tag),
    )


def test_state_root_insertion_order_independent():
    o1 = mk(ClobSide.SELL, 100, 50, 1, 1)
    o2 = mk(ClobSide.SELL, 101, 50, 2, 2)
    o3 = mk(ClobSide.BUY, 99, 30, 3, 3)
    b1 = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o1, o2, o3))
    b2 = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o3, o1, o2))
    b3 = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o2, o3, o1))
    assert b1.state_root() == b2.state_root() == b3.state_root()


def test_state_root_shuffle_invariance_many_permutations():
    orders = [
        mk(ClobSide.SELL, 100 + i, 10 + i, i, i, owner_tag=chr(ord("a") + (i % 5)) * 2)
        for i in range(8)
    ]
    canonical_root = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=tuple(orders)).state_root()
    rng = random.Random(1234)
    for _ in range(40):
        shuffled = orders[:]
        rng.shuffle(shuffled)
        assert ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=tuple(shuffled)).state_root() == canonical_root


def test_root_changes_iff_book_changes():
    o1 = mk(ClobSide.SELL, 100, 50, 1, 1)
    o2 = mk(ClobSide.SELL, 100, 50, 2, 2)
    b = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o1, o2))
    # Same content -> same root.
    assert ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o2, o1)).state_root() == b.state_root()
    # Change one qty -> root changes.
    o2b = mk(ClobSide.SELL, 100, 49, 2, 2)
    assert ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o1, o2b)).state_root() != b.state_root()
    # Change price -> root changes.
    o1b = mk(ClobSide.SELL, 101, 50, 1, 1)
    assert ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o1b, o2)).state_root() != b.state_root()
    # Different assets -> root changes (assets bound into the root).
    other_quote = "0x" + "33" * 32
    assert ClobBook(base_asset=BASE, quote_asset=other_quote, orders=(o1, o2)).state_root() != b.state_root()


def test_empty_book_root_stable_and_distinct():
    e1 = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=())
    e2 = ClobBook(base_asset=BASE, quote_asset=QUOTE)
    assert e1.state_root() == e2.state_root()
    nonempty = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(mk(ClobSide.BUY, 1, 1, 0, 1),))
    assert e1.state_root() != nonempty.state_root()


def test_sorted_level_invariant_strict_total_order():
    # BUY book: highest price first; SELL book: lowest price first; ties by seq.
    buys = (
        mk(ClobSide.BUY, 100, 5, 5, 1),
        mk(ClobSide.BUY, 102, 5, 1, 2),
        mk(ClobSide.BUY, 102, 5, 0, 3),  # same price, earlier seq -> first among 102s
    )
    b = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=buys)
    keys = [order_priority_key(o) for o in b.orders]
    assert keys == sorted(keys)
    # BUY best-first: 102/seq0, 102/seq1, 100/seq5
    resting = b.resting_for_side(ClobSide.BUY)
    assert [o.price_q_per_base for o in resting] == [102, 102, 100]
    assert [o.sequence for o in resting] == [0, 1, 5]

    sells = (
        mk(ClobSide.SELL, 105, 5, 9, 4),
        mk(ClobSide.SELL, 103, 5, 2, 5),
        mk(ClobSide.SELL, 103, 5, 1, 6),
    )
    s = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=sells)
    resting_s = s.resting_for_side(ClobSide.SELL)
    assert [o.price_q_per_base for o in resting_s] == [103, 103, 105]
    assert [o.sequence for o in resting_s] == [1, 2, 9]


def test_dup_order_id_rejected_at_construction():
    o1 = mk(ClobSide.SELL, 100, 50, 1, 7)
    o2 = mk(ClobSide.BUY, 99, 50, 2, 7)  # same order_id 7
    with pytest.raises(ValueError) as exc:
        ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(o1, o2))
    assert REJ_DUP_ORDER_ID in str(exc.value)


@pytest.mark.parametrize(
    "kwargs, code",
    [
        (dict(side="BUY"), REJ_BAD_SIDE),  # not a ClobSide
        (dict(price_q_per_base=0), REJ_BAD_PRICE),
        (dict(price_q_per_base=-1), REJ_BAD_PRICE),
        (dict(price_q_per_base=True), REJ_BAD_PRICE),  # bool is not int
        (dict(price_q_per_base=MAX_PRICE_Q_PER_BASE + 1), REJ_BAD_PRICE),
        (dict(base_qty=0), REJ_BAD_QTY),
        (dict(base_qty=False), REJ_BAD_QTY),  # bool is not int
        (dict(base_qty=MAX_BASE_QTY + 1), REJ_BAD_QTY),
        (dict(sequence=-1), REJ_BAD_SEQUENCE),
        (dict(sequence=MAX_SEQUENCE + 1), REJ_BAD_SEQUENCE),
        (dict(sequence=True), REJ_BAD_SEQUENCE),
        (dict(order_id="0xdeadbeef"), REJ_BAD_ORDER_ID),  # wrong length
        (dict(order_id=123), REJ_BAD_ORDER_ID),
        (dict(owner="0x" + "aa" * 32), REJ_BAD_OWNER),  # 32 bytes, need 48
    ],
)
def test_validate_order_fields_reject_codes(kwargs, code):
    base = dict(
        side=ClobSide.BUY,
        price_q_per_base=100,
        base_qty=10,
        sequence=1,
        order_id=_oid(1),
        owner=_owner("aa"),
    )
    base.update(kwargs)
    assert validate_order_fields(**base) == code


def test_valid_order_fields_pass():
    assert (
        validate_order_fields(
            side=ClobSide.SELL,
            price_q_per_base=100 * PRICE_SCALE,
            base_qty=10,
            sequence=0,
            order_id=_oid(1),
            owner=_owner("ff"),
        )
        is None
    )


def test_clob_order_canonicalizes_hex():
    # Upper-case + no-0x order_id/owner should canonicalize on construction.
    o = ClobOrder(
        side=ClobSide.BUY,
        price_q_per_base=5,
        base_qty=3,
        sequence=2,
        order_id="AB" * 32,  # no 0x, upper
        owner="CD" * 48,
    )
    assert o.order_id == "0x" + "ab" * 32
    assert o.owner == "0x" + "cd" * 48


def test_clob_order_with_base_qty_partial():
    o = mk(ClobSide.SELL, 100, 50, 1, 1)
    p = o.with_base_qty(20)
    assert p.base_qty == 20
    assert p.order_id == o.order_id and p.sequence == o.sequence and p.price_q_per_base == o.price_q_per_base
    # original frozen / unchanged
    assert o.base_qty == 50


def test_book_rejects_same_base_quote_asset():
    with pytest.raises(ValueError):
        ClobBook(base_asset=BASE, quote_asset=BASE, orders=())
