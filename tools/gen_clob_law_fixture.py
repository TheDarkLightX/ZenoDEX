#!/usr/bin/env python3
"""Generate the cross-language CLOB matching-LAW parity fixture (Stage 2 I6).

Emits (book, taker, claimed-fills) cases with the verdict of the INDEPENDENT
Python law checker ``tools.clob_matching_law.verify_no_priority_skip`` (classified
into stable codes by ``law_violation_code``). Lawful cases carry the LIVE
matcher's real fills; violating cases carry FORGED fill lists (priority skip,
partial-fill skip, wrong fill order, over-fill, absent maker) that the Rust
``clob::check_no_skip_law`` must REJECT with the same class -- the non-vacuity
teeth for the in-guest law. Also pins MATCHING_LAW_RULE_HASH so the guest's
journal-committed law identity cannot drift from the Python ledger (the same
drift-bug class the rule hashes had).

Run:  python3 tools/gen_clob_law_fixture.py
"""
from __future__ import annotations

import dataclasses
import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.clob_matching import ClobMatchAccepted, apply_order  # noqa: E402
from src.state.clob_book import ClobBook, ClobOrder, ClobSide  # noqa: E402
from tools.clob_matching_law import (  # noqa: E402
    MATCHING_LAW_RULE_HASH,
    LAW_ABSENT_MAKER,
    LAW_FILL_ORDER,
    LAW_OVERFILL,
    LAW_PRIORITY_SKIP,
    law_violation_code,
    verify_no_priority_skip,
)

FIXTURE_PATH = _REPO / "zk" / "state_proof_risc0" / "shared" / "src" / "clob_law_cases_v1.json"

BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32
E8 = 100_000_000


def _oid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _owner(tag: str) -> str:
    return "0x" + (tag * 48)[:96]


def _o(side, price, qty, seq, oid_n, owner="aa") -> ClobOrder:
    return ClobOrder(side=side, price_q_per_base=price, base_qty=qty,
                     sequence=seq, order_id=_oid(oid_n), owner=_owner(owner))


def _order_json(o: ClobOrder) -> dict:
    return {
        "side_code": o.side.code, "price_q_per_base": o.price_q_per_base,
        "base_qty": o.base_qty, "sequence": o.sequence,
        "order_id": o.order_id, "owner": o.owner,
    }


def _fill_json(f) -> dict:
    return {
        "base": f.base, "quote": f.quote, "maker_price": f.maker_price,
        "buyer": f.buyer, "seller": f.seller,
        "taker_order_id": f.taker_order_id, "maker_order_id": f.maker_order_id,
        "maker_side_code": f.maker_side.code,
    }


def _accepted(book: ClobBook, taker: ClobOrder) -> ClobMatchAccepted:
    res = apply_order(book, taker)
    assert isinstance(res, ClobMatchAccepted), res
    return res


def _case(name: str, book: ClobBook, taker: ClobOrder, fills, expect_code) -> dict:
    """One fixture case from the CLAIMED ``fills`` with the Python verdict.

    ``expect_code`` is a gen-time sanity pin: the constructed case MUST classify
    to the intended class (None for lawful), or the corpus itself is wrong.
    """
    claimed = ClobMatchAccepted(book=book, fills=tuple(fills), resting_taker_qty=0)
    code = law_violation_code(verify_no_priority_skip(book, taker, claimed))
    assert code == expect_code, f"{name}: expected {expect_code}, got {code}"
    return {
        "name": name,
        "base_asset": book.base_asset,
        "quote_asset": book.quote_asset,
        "orders": [_order_json(o) for o in book.orders],
        "taker": _order_json(taker),
        "fills": [_fill_json(f) for f in fills],
        "violation": code,
    }


def build_corpus() -> list[dict]:
    cases: list[dict] = []

    # --- lawful: the LIVE matcher's own fills satisfy the law ------------------
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, E8, 5, 1, 1, "bb"),
    ))
    taker = _o(ClobSide.BUY, E8, 5, 10, 99, "aa")
    cases.append(_case("lawful_full_fill", book, taker,
                       _accepted(book, taker).fills, None))

    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, 102 * E8 // 100, 5, 1, 1, "bb"),
        _o(ClobSide.SELL, E8, 5, 2, 2, "cc"),
        _o(ClobSide.SELL, 101 * E8 // 100, 5, 3, 3, "dd"),
    ))
    taker = _o(ClobSide.BUY, 102 * E8 // 100, 12, 10, 99, "aa")
    cases.append(_case("lawful_price_priority_multi_fill", book, taker,
                       _accepted(book, taker).fills, None))

    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, E8, 5, 2, 1, "bb"),
        _o(ClobSide.SELL, E8, 5, 1, 2, "cc"),  # earlier seq -> higher priority
    ))
    taker = _o(ClobSide.BUY, E8, 3, 10, 99, "aa")
    cases.append(_case("lawful_time_priority_same_price", book, taker,
                       _accepted(book, taker).fills, None))

    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, E8, 5, 1, 1, "bb"),
        _o(ClobSide.SELL, 101 * E8 // 100, 5, 2, 2, "cc"),
    ))
    taker = _o(ClobSide.BUY, 101 * E8 // 100, 5, 10, 99, "aa")  # fills only the best
    cases.append(_case("lawful_partial_leaves_lower_priority", book, taker,
                       _accepted(book, taker).fills, None))

    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.BUY, 102 * E8 // 100, 5, 1, 1, "bb"),  # highest BUY = best
        _o(ClobSide.BUY, E8, 5, 2, 2, "cc"),
    ))
    taker = _o(ClobSide.SELL, E8, 8, 10, 99, "aa")  # SELL walks the BUY book
    cases.append(_case("lawful_sell_taker_buy_makers", book, taker,
                       _accepted(book, taker).fills, None))

    # --- violating: FORGED fills the checker must reject -----------------------
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, E8, 5, 1, 1, "bb"),  # best price -> higher priority
        _o(ClobSide.SELL, 101 * E8 // 100, 5, 2, 2, "cc"),
    ))
    taker = _o(ClobSide.BUY, 101 * E8 // 100, 5, 10, 99, "aa")
    real = _accepted(book, taker)
    skip = dataclasses.replace(real.fills[0], maker_order_id=_oid(2),
                               maker_price=101 * E8 // 100)
    cases.append(_case("violation_priority_skip", book, taker, (skip,),
                       LAW_PRIORITY_SKIP))

    # Partial-fill skip: the higher-priority maker is left PARTIALLY consumed
    # (4/5) while the lower-priority maker still receives a fill.
    taker = _o(ClobSide.BUY, 101 * E8 // 100, 8, 10, 99, "aa")
    real = _accepted(book, taker)
    assert [f.base for f in real.fills] == [5, 3]
    partial = (
        dataclasses.replace(real.fills[0], base=4),
        dataclasses.replace(real.fills[1], base=4),
    )
    cases.append(_case("violation_priority_skip_partial_fill", book, taker, partial,
                       LAW_PRIORITY_SKIP))

    taker = _o(ClobSide.BUY, 101 * E8 // 100, 10, 10, 99, "aa")
    real = _accepted(book, taker)
    assert len(real.fills) == 2  # both makers fully filled, in priority order
    cases.append(_case("violation_fill_order_reversed", book, taker,
                       tuple(reversed(real.fills)), LAW_FILL_ORDER))

    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=(
        _o(ClobSide.SELL, E8, 5, 1, 1, "bb"),
    ))
    taker = _o(ClobSide.BUY, E8, 5, 10, 99, "aa")
    real = _accepted(book, taker)
    over = dataclasses.replace(real.fills[0], base=real.fills[0].base + 1)
    cases.append(_case("violation_overfill", book, taker, (over,), LAW_OVERFILL))

    absent = dataclasses.replace(real.fills[0], maker_order_id=_oid(77))
    cases.append(_case("violation_absent_maker", book, taker, (absent,),
                       LAW_ABSENT_MAKER))

    return cases


def _strip0x(h: str) -> str:
    return h[2:] if h.startswith("0x") else h


def render() -> str:
    payload = {
        "version": 1,
        # The law identity the guest journal commits; the Rust
        # clob_matching_law_rule_hash() must reproduce this byte-for-byte.
        "matching_law_rule_hash": _strip0x(MATCHING_LAW_RULE_HASH),
        "cases": build_corpus(),
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main(argv: list[str] | None = None) -> int:
    argv = argv if argv is not None else sys.argv[1:]
    text = render()
    if "--check" in argv:
        current = FIXTURE_PATH.read_text(encoding="utf-8") if FIXTURE_PATH.exists() else ""
        if current != text:
            print("clob law fixture is STALE; run tools/gen_clob_law_fixture.py", file=sys.stderr)
            return 1
        print("clob law fixture is current")
        return 0
    FIXTURE_PATH.write_text(text, encoding="utf-8")
    print(f"wrote {FIXTURE_PATH.relative_to(_REPO)} ({len(build_corpus())} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
