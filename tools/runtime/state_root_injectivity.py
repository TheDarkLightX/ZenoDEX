#!/usr/bin/env python3
"""State-root v5 preimage injectivity checks.

The consensus root is a hash of canonical preimage bytes. This script checks
the production preimage encoder, not a separate model:

1. The section framing has a strict decoder and `decode(encode(x)) == x`.
2. Uvarint encoding round-trips at boundary values.
3. A bounded structured corpus has no preimage collision, including dust-only
   deltas that must change exactly the FEE section.

This does not prove SHA-256 collision resistance. It proves the preimage bytes
do not merge the modeled semantic states before hashing.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.fees import FeeAccumulatorState  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.state.canonical import domain_sep_bytes, encode_bytes, encode_uvarint  # noqa: E402
from src.state.lp import LPTable  # noqa: E402
from src.state.nonces import NonceTable  # noqa: E402
from src.state.state_root import (  # noqa: E402
    STATE_ROOT_SECTION_LABELS,
    STATE_ROOT_VERSION,
    state_root_preimage,
)

_DOMAIN_PREFIX = domain_sep_bytes("state_root", version=STATE_ROOT_VERSION)


def decode_uvarint(buf: bytes, offset: int = 0) -> tuple[int, int]:
    """Decode one unsigned LEB128 value; return `(value, next_offset)`."""
    shift = 0
    value = 0
    while True:
        if offset >= len(buf):
            raise ValueError("truncated uvarint")
        byte = buf[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if not (byte & 0x80):
            return value, offset
        shift += 7
        if shift > 256:
            raise ValueError("uvarint exceeds 256-bit limit")


def decode_state_root_preimage(payload: bytes) -> dict[bytes, bytes]:
    """Strictly recover the ordered labeled section bodies from a preimage."""
    if not isinstance(payload, (bytes, bytearray)):
        raise TypeError("payload must be bytes")
    payload = bytes(payload)
    if not payload.startswith(_DOMAIN_PREFIX):
        raise ValueError("bad or missing state_root domain separator")
    off = len(_DOMAIN_PREFIX)
    sections: dict[bytes, bytes] = {}
    for label in STATE_ROOT_SECTION_LABELS:
        if payload[off : off + len(label)] != label:
            raise ValueError(f"expected section label {label!r} at offset {off}")
        off += len(label)
        length, off = decode_uvarint(payload, off)
        body = payload[off : off + length]
        if len(body) != length:
            raise ValueError(f"truncated body for section {label!r}")
        off += length
        sections[label] = body
    if off != len(payload):
        raise ValueError("trailing bytes after final section")
    return sections


def _encode_framed(sections: dict[bytes, bytes]) -> bytes:
    out = bytearray(_DOMAIN_PREFIX)
    for label in STATE_ROOT_SECTION_LABELS:
        out += label
        out += encode_bytes(sections[label])
    return bytes(out)


def _check_framing_injectivity() -> tuple[bool, str]:
    bodies = [
        b"",
        b"BAL",
        b"FEE\x00",
        b"POL" + b"\x00" * 200,
        _DOMAIN_PREFIX,
        b"\xff" * 300,
        b"NNC" + encode_bytes(b"nested"),
        bytes(range(256)),
    ]
    seen: dict[bytes, tuple[bytes, ...]] = {}
    for combo in itertools.product(bodies, repeat=2):
        section_bodies = list(combo) + [b"s2", b"s3", b"s4", b"s5"]
        sections = {label: section_bodies[i] for i, label in enumerate(STATE_ROOT_SECTION_LABELS)}
        payload = _encode_framed(sections)
        decoded = decode_state_root_preimage(payload)
        if decoded != sections:
            return False, f"decode(encode(sections)) failed for {sections!r}"
        tup = tuple(sections[label] for label in STATE_ROOT_SECTION_LABELS)
        if payload in seen and seen[payload] != tup:
            return False, "distinct section tuples share one framed payload"
        seen[payload] = tup
    return True, "framing decoder is a left inverse over adversarial bodies"


def _check_uvarint_injectivity() -> tuple[bool, str]:
    corpus = [0, 1, 2, 126, 127, 128, 129, 255, 256, 16_383, 16_384, 2**32, 2**64, (1 << 256) - 1]
    seen: dict[bytes, int] = {}
    for n in corpus:
        enc = encode_uvarint(n)
        dec, off = decode_uvarint(enc)
        if dec != n or off != len(enc):
            return False, f"uvarint round-trip failed for {n}"
        if enc in seen and seen[enc] != n:
            return False, f"uvarint collision: {seen[enc]} and {n}"
        seen[enc] = n
    return True, f"uvarint round-trips over {len(corpus)} boundary values"


PK = ["0x" + f"{i:02x}" * 48 for i in (0x11, 0x22)]
ASSET = ["0x" + f"{i:02x}" * 32 for i in (0x0A, 0x0B)]
POOL = "0x" + "1c" * 32


def _state(
    balset: tuple[tuple[str, str, int], ...],
    lpset: tuple[tuple[str, int], ...],
    nonce: int,
    dust: int,
) -> tuple[BalanceTable, LPTable, NonceTable, FeeAccumulatorState]:
    balances = BalanceTable()
    for pubkey, asset, amount in balset:
        if amount:
            balances.set(pubkey, asset, amount)
    lp = LPTable()
    for pubkey, amount in lpset:
        if amount:
            lp.set(pubkey, POOL, amount)
    nonces = NonceTable()
    if nonce:
        nonces.set_last(PK[0], nonce)
    return balances, lp, nonces, FeeAccumulatorState(dust=dust)


def _preimage(state: tuple[BalanceTable, LPTable, NonceTable, FeeAccumulatorState]) -> bytes:
    balances, lp, nonces, fee = state
    return state_root_preimage(
        balances=balances,
        pools={},
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee,
    )


def _check_bounded_no_collision() -> tuple[bool, str]:
    bal_opts = [
        ((PK[0], ASSET[0], 0),),
        ((PK[0], ASSET[0], 1),),
        ((PK[0], ASSET[0], 1000),),
        ((PK[1], ASSET[1], 1),),
    ]
    lp_opts = [((PK[0], 0),), ((PK[0], 5),)]
    nonce_opts = [0, 3]
    dust_opts = [0, 1, 2, 5, 999]

    preimages: dict[bytes, tuple[Any, ...]] = {}
    states = list(itertools.product(bal_opts, lp_opts, nonce_opts, dust_opts))
    for raw in states:
        payload = _preimage(_state(*raw))
        if _preimage(_state(*raw)) != payload:
            return False, f"preimage not deterministic for {raw!r}"
        if payload in preimages and preimages[payload] != raw:
            return False, f"collision: {preimages[payload]!r} and {raw!r}"
        preimages[payload] = raw

    base = ((PK[0], ASSET[0], 1000),), ((PK[0], 5),), 3, 0
    other = ((PK[0], ASSET[0], 1000),), ((PK[0], 5),), 3, 7
    d0 = decode_state_root_preimage(_preimage(_state(*base)))
    d7 = decode_state_root_preimage(_preimage(_state(*other)))
    changed = [label for label in STATE_ROOT_SECTION_LABELS if d0[label] != d7[label]]
    if changed != [b"FEE"]:
        return False, f"dust-only delta changed {changed!r}, expected [b'FEE']"
    return True, f"{len(states)} structured states have distinct preimages; dust-only delta changes FEE"


def run_injectivity_proof() -> dict[str, Any]:
    obligations = []
    for name, fn in (
        ("framing_injectivity_unconditional", _check_framing_injectivity),
        ("uvarint_injectivity", _check_uvarint_injectivity),
        ("bounded_no_collision_incl_FEE", _check_bounded_no_collision),
    ):
        ok, detail = fn()
        obligations.append({"obligation": name, "ok": ok, "detail": detail})
    return {
        "artifact": "state_root_preimage injectivity v5",
        "state_root_version": STATE_ROOT_VERSION,
        "section_labels": [label.decode("ascii") for label in STATE_ROOT_SECTION_LABELS],
        "assumption": "SHA-256 collision resistance",
        "ok": all(item["ok"] for item in obligations),
        "obligations": obligations,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="State-root v5 preimage injectivity checks")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = run_injectivity_proof()
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print(f"{'OK' if report['ok'] else 'FAIL'}: state-root v{STATE_ROOT_VERSION} preimage injectivity")
        for obligation in report["obligations"]:
            marker = "pass" if obligation["ok"] else "FAIL"
            print(f"  [{marker}] {obligation['obligation']}: {obligation['detail']}")
        print(f"  assumption: {report['assumption']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
