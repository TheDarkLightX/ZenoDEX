#!/usr/bin/env python3
"""Generate the cross-language CLOB matcher parity fixture (Stage 2 I2).

Emits a hostile corpus of (book, taker) cases with the LIVE Python
``clob_matching.apply_order`` result: for an accept, the fills + post-book
state_root + resting_taker_qty; for a reject, the stable reason code. The Rust
``clob::apply_clob_order`` must reproduce each case (same accept/reject, same
fills, same post-book root). This de-risks ALGORITHM parity the way the book-root
fixture de-risks ENCODING parity.

Prices are kept near PRICE_SCALE so quotes stay small (fit i64 for JSON); the
book-root fixture already covers max-width encoding.

Run:  python3 tools/gen_clob_match_fixture.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.clob_matching import (  # noqa: E402
    ClobMatchAccepted,
    ClobMatchRejected,
    apply_order,
)
# The LEDGER's rule-hash constants (the client's accepted_rulebook_hash). The Rust
# guest's clob_matching_rule_hash()/clob_fee_rule_hash() must reproduce these, or
# the client rejects every proof (adversarial review 2026-06-07, finding #5).
from src.integration.orderbook_api import FEE_RULE_HASH, MATCHING_RULE_HASH  # noqa: E402
from src.state.clob_book import ClobBook, ClobOrder, ClobSide  # noqa: E402

FIXTURE_PATH = _REPO / "zk" / "state_proof_risc0" / "shared" / "src" / "clob_match_cases_v1.json"

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


def _case(name: str, makers: list[ClobOrder], taker: ClobOrder) -> dict:
    book = ClobBook(base_asset=BASE, quote_asset=QUOTE, orders=tuple(makers))
    res = apply_order(book, taker)
    out = {
        "name": name,
        "base_asset": BASE,
        "quote_asset": QUOTE,
        "orders": [_order_json(o) for o in makers],
        "taker": _order_json(taker),
    }
    if isinstance(res, ClobMatchAccepted):
        root = res.book.state_root()
        out["result"] = {
            "accepted": True,
            "fills": [_fill_json(f) for f in res.fills],
            "post_book_root": root[2:] if root.startswith("0x") else root,
            "resting_taker_qty": res.resting_taker_qty,
        }
    else:
        assert isinstance(res, ClobMatchRejected)
        out["result"] = {"accepted": False, "reason": res.reason}
    return out


def build_corpus() -> list[dict]:
    return [
        _case("single_full_fill",
              [_o(ClobSide.SELL, E8, 5, 1, 1, "bb")],
              _o(ClobSide.BUY, E8, 5, 10, 99, "aa")),
        _case("partial_maker_taker_full",
              [_o(ClobSide.SELL, E8, 5, 1, 1, "bb")],
              _o(ClobSide.BUY, E8, 3, 10, 99, "aa")),
        _case("taker_bigger_leftover_rerests",
              [_o(ClobSide.SELL, E8, 5, 1, 1, "bb")],
              _o(ClobSide.BUY, E8, 8, 10, 99, "aa")),
        _case("price_priority_multi_fill",
              [_o(ClobSide.SELL, 102 * E8 // 100, 5, 1, 1, "bb"),
               _o(ClobSide.SELL, E8, 5, 2, 2, "cc"),
               _o(ClobSide.SELL, 101 * E8 // 100, 5, 3, 3, "dd")],
              _o(ClobSide.BUY, 102 * E8 // 100, 12, 10, 99, "aa")),
        _case("time_priority_same_price",
              [_o(ClobSide.SELL, E8, 5, 2, 1, "bb"),
               _o(ClobSide.SELL, E8, 5, 1, 2, "cc")],
              _o(ClobSide.BUY, E8, 3, 10, 99, "aa")),
        _case("no_cross_taker_rests",
              [_o(ClobSide.SELL, 105 * E8 // 100, 5, 1, 1, "bb")],
              _o(ClobSide.BUY, E8, 5, 10, 99, "aa")),
        _case("self_trade_reject",
              [_o(ClobSide.SELL, E8, 5, 1, 1, "aa")],
              _o(ClobSide.BUY, E8, 5, 10, 99, "aa")),
        _case("dup_order_id_reject",
              [_o(ClobSide.SELL, E8, 5, 1, 7, "bb")],
              _o(ClobSide.BUY, E8, 5, 10, 7, "aa")),
        _case("partial_cross_stop",
              [_o(ClobSide.SELL, E8, 5, 1, 1, "bb"),
               _o(ClobSide.SELL, 110 * E8 // 100, 5, 2, 2, "cc")],
              _o(ClobSide.BUY, 105 * E8 // 100, 10, 10, 99, "aa")),
    ]


def _strip0x(h: str) -> str:
    return h[2:] if h.startswith("0x") else h


def render() -> str:
    payload = {
        "version": 1,
        # Ledger rule-hash constants the Rust guest must reproduce byte-for-byte.
        "rule_hashes": {
            "matching": _strip0x(MATCHING_RULE_HASH),
            "fee": _strip0x(FEE_RULE_HASH),
        },
        "cases": build_corpus(),
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main(argv: list[str] | None = None) -> int:
    argv = argv if argv is not None else sys.argv[1:]
    text = render()
    if "--check" in argv:
        current = FIXTURE_PATH.read_text(encoding="utf-8") if FIXTURE_PATH.exists() else ""
        if current != text:
            print("clob match fixture is STALE; run tools/gen_clob_match_fixture.py", file=sys.stderr)
            return 1
        print("clob match fixture is current")
        return 0
    FIXTURE_PATH.write_text(text, encoding="utf-8")
    print(f"wrote {FIXTURE_PATH.relative_to(_REPO)} ({len(build_corpus())} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
