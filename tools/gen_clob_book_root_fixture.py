#!/usr/bin/env python3
"""Generate the cross-language CLOB book-root parity fixture (Stage 2).

Emits a hostile corpus of ClobBooks plus their canonical ``clob_book.state_root``
hex. The RISC0 guest's Rust ``ClobBookV1::state_root`` must reproduce each hex
BYTE-FOR-BYTE (the guest proves the actual LEDGER book root by construction, with
no encoder-equivalence obligation). The Rust parity test reads this file; a
sibling Python test (test_clob_book_root_fixture.py) asserts it is current so it
can never go stale.

Orders are emitted in INPUT order (pre-canonicalization) so the Rust side must
reproduce the order_priority_key sort too -- including the signed-price-term trap
(BUY uses -price in the sort key but the UNSIGNED price in the encoding).

Run:  python3 tools/gen_clob_book_root_fixture.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.state.clob_book import (  # noqa: E402
    MAX_BASE_QTY,
    MAX_PRICE_Q_PER_BASE,
    MAX_SEQUENCE,
    ClobBook,
    ClobOrder,
    ClobSide,
)

FIXTURE_PATH = _REPO / "zk" / "state_proof_risc0" / "shared" / "src" / "clob_book_roots_v1.json"

BASE = "0x" + "11" * 32
QUOTE = "0x" + "22" * 32


def _oid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _owner(tag: str) -> str:
    return "0x" + (tag * 48)[:96]


def _order(side: ClobSide, price: int, qty: int, seq: int, oid_n: int, owner_tag: str = "aa") -> ClobOrder:
    return ClobOrder(
        side=side, price_q_per_base=price, base_qty=qty,
        sequence=seq, order_id=_oid(oid_n), owner=_owner(owner_tag),
    )


def _order_json(o: ClobOrder) -> dict:
    return {
        "side_code": o.side.code,
        "price_q_per_base": o.price_q_per_base,
        "base_qty": o.base_qty,
        "sequence": o.sequence,
        "order_id": o.order_id,
        "owner": o.owner,
    }


def _case(name: str, orders: list[ClobOrder]) -> dict:
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=tuple(orders))
    root = book.state_root()
    return {
        "name": name,
        "base_asset": BASE,
        "quote_asset": QUOTE,
        # INPUT order (pre-sort) -- the Rust must canonicalize it itself.
        "orders": [_order_json(o) for o in orders],
        "state_root": root[2:] if root.startswith("0x") else root,
    }


def build_corpus() -> list[dict]:
    return [
        _case("empty_book", []),
        _case("single_buy", [_order(ClobSide.BUY, 100, 5, 1, 1, "aa")]),
        _case("single_sell", [_order(ClobSide.SELL, 100, 5, 1, 2, "bb")]),
        # BUY-heavy, descending priority by -price -> exercises the signed-term trap.
        _case("buy_heavy_price_priority", [
            _order(ClobSide.BUY, 98, 3, 5, 1, "aa"),
            _order(ClobSide.BUY, 102, 4, 6, 2, "bb"),
            _order(ClobSide.BUY, 100, 7, 7, 3, "cc"),
        ]),
        # Mixed book (buys + sells), input order shuffled vs canonical.
        _case("mixed_book_shuffled", [
            _order(ClobSide.SELL, 101, 5, 3, 4, "dd"),
            _order(ClobSide.BUY, 99, 2, 1, 5, "aa"),
            _order(ClobSide.SELL, 100, 6, 2, 6, "bb"),
            _order(ClobSide.BUY, 100, 1, 4, 7, "cc"),
        ]),
        # Ties on (side, price, sequence) broken only by order_id (lexicographic).
        _case("ties_broken_by_order_id", [
            _order(ClobSide.SELL, 100, 5, 9, 30, "aa"),
            _order(ClobSide.SELL, 100, 5, 9, 10, "bb"),
            _order(ClobSide.SELL, 100, 5, 9, 20, "cc"),
        ]),
        # Max-width values (uvarint multi-byte boundaries).
        _case("max_width_values", [
            _order(ClobSide.BUY, MAX_PRICE_Q_PER_BASE, MAX_BASE_QTY, MAX_SEQUENCE, 40, "aa"),
            _order(ClobSide.SELL, MAX_PRICE_Q_PER_BASE, MAX_BASE_QTY, MAX_SEQUENCE, 41, "bb"),
        ]),
    ]


def render() -> str:
    return json.dumps({"version": 1, "cases": build_corpus()}, indent=2, sort_keys=True) + "\n"


def main(argv: list[str] | None = None) -> int:
    argv = argv if argv is not None else sys.argv[1:]
    text = render()
    if "--check" in argv:
        current = FIXTURE_PATH.read_text(encoding="utf-8") if FIXTURE_PATH.exists() else ""
        if current != text:
            print("clob book-root fixture is STALE; run tools/gen_clob_book_root_fixture.py", file=sys.stderr)
            return 1
        print("clob book-root fixture is current")
        return 0
    FIXTURE_PATH.write_text(text, encoding="utf-8")
    print(f"wrote {FIXTURE_PATH.relative_to(_REPO)} ({len(build_corpus())} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
