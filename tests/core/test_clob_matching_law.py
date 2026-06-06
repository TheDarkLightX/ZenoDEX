"""Stage 2 matching-law gate: the live matcher honors price-time priority.

Drives the LIVE ``src/core/clob_matching.apply_order`` over a hostile corpus + a
seeded-random sweep and asserts the INDEPENDENT no-skip law checker
(``tools.clob_matching_law.verify_no_priority_skip``) finds no violation -- the
dual-checker discipline (production matcher vs. an independent re-derivation of
the Stage 2 law). The teeth prove the checker is non-vacuous: a deliberately
priority-skipping (or over-filling) accepted match is CAUGHT.

Stage 2 law (docs/product_discipline/proof_carrying_orderbook_build_spec.md):
"No higher-priority eligible order was skipped for any accepted fill."
"""
from __future__ import annotations

import dataclasses
import random

from src.core.clob_matching import ClobMatchAccepted, apply_order
from src.state.clob_book import ClobBook, ClobOrder, ClobSide
from tools.clob_matching_law import verify_no_priority_skip


BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32


def _owner(tag: str) -> str:
    return "0x" + (tag * 48)[:96]


def _oid(n: int) -> str:
    return "0x" + f"{n:064x}"


def mk(side, price, qty, seq, oid_n, owner_tag="aa") -> ClobOrder:
    return ClobOrder(
        side=side, price_q_per_base=price, base_qty=qty,
        sequence=seq, order_id=_oid(oid_n), owner=_owner(owner_tag),
    )


def _accepted(book: ClobBook, taker: ClobOrder) -> ClobMatchAccepted:
    res = apply_order(book, taker)
    assert isinstance(res, ClobMatchAccepted), res
    return res


# --- Deterministic hostile corpus ---------------------------------------------
def test_law_holds_time_priority_same_price():
    # Two SELL makers at the same price; the earlier sequence is higher priority.
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        mk(ClobSide.SELL, 100, 5, seq=2, oid_n=1, owner_tag="aa"),
        mk(ClobSide.SELL, 100, 5, seq=1, oid_n=2, owner_tag="bb"),  # earlier seq -> higher priority
    ))
    taker = mk(ClobSide.BUY, 100, 3, seq=10, oid_n=99, owner_tag="cc")
    res = _accepted(book, taker)
    assert verify_no_priority_skip(book, taker, res) is None
    assert res.fills[0].maker_order_id == _oid(2)  # earlier-sequence maker fills first


def test_law_holds_price_priority():
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        mk(ClobSide.SELL, 102, 5, seq=1, oid_n=1, owner_tag="aa"),
        mk(ClobSide.SELL, 100, 5, seq=2, oid_n=2, owner_tag="bb"),  # best price -> highest priority
        mk(ClobSide.SELL, 101, 5, seq=3, oid_n=3, owner_tag="cc"),
    ))
    taker = mk(ClobSide.BUY, 102, 12, seq=10, oid_n=99, owner_tag="dd")
    res = _accepted(book, taker)
    assert verify_no_priority_skip(book, taker, res) is None
    assert res.fills[0].maker_order_id == _oid(2)  # best price fills first


def test_law_holds_partial_fill_leaves_lower_priority():
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        mk(ClobSide.SELL, 100, 5, seq=1, oid_n=1, owner_tag="aa"),
        mk(ClobSide.SELL, 101, 5, seq=2, oid_n=2, owner_tag="bb"),
    ))
    taker = mk(ClobSide.BUY, 101, 5, seq=10, oid_n=99, owner_tag="cc")  # fills only the best
    res = _accepted(book, taker)
    assert verify_no_priority_skip(book, taker, res) is None


def test_law_holds_taker_crosses_only_some():
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        mk(ClobSide.SELL, 100, 5, seq=1, oid_n=1, owner_tag="aa"),
        mk(ClobSide.SELL, 105, 5, seq=2, oid_n=2, owner_tag="bb"),  # above taker limit -> not eligible
    ))
    taker = mk(ClobSide.BUY, 100, 10, seq=10, oid_n=99, owner_tag="cc")
    res = _accepted(book, taker)
    assert verify_no_priority_skip(book, taker, res) is None


# --- Seeded-random sweep (deterministic) --------------------------------------
def test_law_holds_over_seeded_random_books():
    rng = random.Random(20260606)
    checked = 0
    for _ in range(600):
        side = rng.choice([ClobSide.BUY, ClobSide.SELL])
        maker_side = ClobSide.SELL if side is ClobSide.BUY else ClobSide.BUY
        makers, used = [], set()
        for _ in range(rng.randint(1, 6)):
            oid = rng.randint(1, 50)
            if oid in used:
                continue
            used.add(oid)
            makers.append(mk(maker_side, rng.randint(90, 110), rng.randint(1, 8),
                             seq=rng.randint(1, 100), oid_n=oid, owner_tag="aa"))
        if not makers:
            continue
        book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=tuple(makers))
        taker = mk(side, rng.randint(90, 110), rng.randint(1, 20), seq=200, oid_n=999, owner_tag="ee")
        res = apply_order(book, taker)
        if isinstance(res, ClobMatchAccepted):
            violation = verify_no_priority_skip(book, taker, res)
            assert violation is None, violation
            checked += 1
    assert checked > 50  # the sweep genuinely exercised accepted matches


# --- Non-vacuity teeth: a wrong accepted match MUST be caught ------------------
def test_teeth_priority_skip_is_caught():
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        mk(ClobSide.SELL, 100, 5, seq=1, oid_n=1, owner_tag="aa"),   # best price -> higher priority
        mk(ClobSide.SELL, 101, 5, seq=2, oid_n=2, owner_tag="bb"),
    ))
    taker = mk(ClobSide.BUY, 101, 5, seq=10, oid_n=99, owner_tag="cc")
    real = _accepted(book, taker)
    assert verify_no_priority_skip(book, taker, real) is None  # control: real match is lawful

    # Forge a match that fills the LOWER-priority maker (oid 2) while the
    # HIGHER-priority crossing maker (oid 1) is left unfilled -> a priority skip.
    forged_fill = dataclasses.replace(real.fills[0], maker_order_id=_oid(2), maker_price=101)
    forged = ClobMatchAccepted(book=real.book, fills=(forged_fill,), resting_taker_qty=real.resting_taker_qty)
    violation = verify_no_priority_skip(book, taker, forged)
    assert violation is not None and "priority skip" in violation, violation


def test_teeth_overfill_is_caught():
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(mk(ClobSide.SELL, 100, 5, seq=1, oid_n=1, owner_tag="aa"),))
    taker = mk(ClobSide.BUY, 100, 5, seq=10, oid_n=99, owner_tag="cc")
    real = _accepted(book, taker)
    forged_fill = dataclasses.replace(real.fills[0], base=real.fills[0].base + 1)
    forged = ClobMatchAccepted(book=real.book, fills=(forged_fill,), resting_taker_qty=0)
    violation = verify_no_priority_skip(book, taker, forged)
    assert violation is not None and "over-filled" in violation, violation
