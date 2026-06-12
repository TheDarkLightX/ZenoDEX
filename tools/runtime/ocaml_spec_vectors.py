#!/usr/bin/env python3
"""Generate shared TSV vectors for the OCaml executable spec oracle.

The OCaml spec (`ocaml-runtime/`) is a third, independent pure implementation of
two small surfaces — the fee-router split conservation and the replay-guard
nonce policy. It is a differential *oracle*, never a production runtime path.

Rather than parse JSON in OCaml, the authority emits simple TSV (tab-separated)
vectors that the OCaml test reads with the stdlib. This script drives the real
Python authority (`src/core/fee_router.py`, `src/core/replay_guard.py`) and
writes:

    ocaml-runtime/test/vectors/fee_router.tsv
    ocaml-runtime/test/vectors/replay_guard.tsv

Usage::

    python3 tools/runtime/ocaml_spec_vectors.py            # (re)write the vectors
    python3 tools/runtime/ocaml_spec_vectors.py --check     # fail if out of date
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.core.fee_router import (
    BORROW,
    DEX,
    PERPS,
    REDEMPTION,
    FeeAccumulator,
    RouteAccepted,
    canonical_split_table,
    route_fee,
)
from src.core.replay_guard import AdmitAccepted, ReplayGuardState, admit

_VECTORS_DIR = _REPO / "ocaml-runtime" / "test" / "vectors"
_DOMAINS = [DEX, PERPS, BORROW, REDEMPTION]
_AMOUNTS = [0, 1, 3, 10_000, 12_347, 999_983, 1_000_000_000]
_SENDER = "0x" + "11" * 48


def _fee_router_tsv() -> str:
    header = (
        "domain\tamount\tbuyburn_bps\tstakers_bps\treserve_bps\thosts_bps\t"
        "buyburn\tstakers\treserve\thosts\tdust"
    )
    rows = [header]
    for domain in _DOMAINS:
        table = canonical_split_table(domain)
        for amount in _AMOUNTS:
            result = route_fee(
                source=domain,
                asset="zUSD",
                amount=amount,
                split_table=table,
                accumulator=FeeAccumulator(),
            )
            assert isinstance(result, RouteAccepted), (domain, amount)
            r = result.receipt
            assert amount == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust
            rows.append(
                "\t".join(
                    str(x)
                    for x in (
                        domain,
                        amount,
                        table.buyburn_bps,
                        table.stakers_bps,
                        table.reserve_bps,
                        table.hosts_bps,
                        r.buyburn,
                        r.stakers,
                        r.reserve,
                        r.hosts,
                        r.dust,
                    )
                )
            )
    return "\n".join(rows) + "\n"


def _admit_outcome(last: int, nonce: int) -> tuple[int, str]:
    """Drive the real admit() for a sender whose last accepted nonce is `last`."""
    state = ReplayGuardState()
    if last > 0:
        state = state.with_last(_SENDER, last)
    result = admit(state=state, sender=_SENDER, nonce=nonce)
    if isinstance(result, AdmitAccepted):
        return 1, "accept"
    return 0, result.reason


def _replay_guard_tsv() -> str:
    header = "last\tnonce\taccepted\tcode"
    rows = [header]
    U32_MAX = 0xFFFFFFFF
    pairs = [
        (0, 0),  # invalid (< 1)
        (0, 1),  # accept (first)
        (0, 2),  # gap
        (1, 1),  # duplicate
        (1, 2),  # accept
        (2, 1),  # stale
        (5, 7),  # gap
        (5, 6),  # accept
        (5, 0),  # invalid
        (5, U32_MAX + 1),  # invalid (> u32)
        (U32_MAX - 1, U32_MAX),  # accept at the boundary
        (U32_MAX, U32_MAX),  # duplicate at the boundary
    ]
    for last, nonce in pairs:
        accepted, code = _admit_outcome(last, nonce)
        rows.append(f"{last}\t{nonce}\t{accepted}\t{code}")
    return "\n".join(rows) + "\n"


def _targets() -> dict[Path, str]:
    return {
        _VECTORS_DIR / "fee_router.tsv": _fee_router_tsv(),
        _VECTORS_DIR / "replay_guard.tsv": _replay_guard_tsv(),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate OCaml spec TSV vectors.")
    parser.add_argument("--check", action="store_true", help="fail if files are stale")
    args = parser.parse_args(argv)

    _VECTORS_DIR.mkdir(parents=True, exist_ok=True)
    stale = []
    for path, content in _targets().items():
        if args.check:
            existing = path.read_text(encoding="utf-8") if path.is_file() else None
            if existing != content:
                stale.append(path)
        else:
            path.write_text(content, encoding="utf-8")
            print(f"wrote {path.relative_to(_REPO)}")
    if args.check and stale:
        print("stale OCaml spec vectors: " + ", ".join(str(p) for p in stale), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
