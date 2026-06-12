"""Regression checks for state-root v5 canonical preimage injectivity."""

from __future__ import annotations

import json

import pytest

from src.state.balances import BalanceTable
from src.state.canonical import encode_uvarint
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.state_root import STATE_ROOT_SECTION_LABELS, state_root_preimage
from tools.runtime.state_root_injectivity import (
    decode_state_root_preimage,
    decode_uvarint,
    run_injectivity_proof,
)


def test_state_root_preimage_injectivity_obligations() -> None:
    report = run_injectivity_proof()
    assert report["ok"], (
        "state-root injectivity proof failed:\n" + json.dumps(report["obligations"], indent=2)
    )
    names = {item["obligation"]: item["ok"] for item in report["obligations"]}
    assert names["framing_injectivity_unconditional"]
    assert names["uvarint_injectivity"]
    assert names["bounded_no_collision_incl_FEE"]


def test_decoder_is_left_inverse_of_encoder() -> None:
    balances = BalanceTable()
    balances.set("0x" + "11" * 48, "0x" + "0a" * 32, 1000)
    lp = LPTable()
    lp.set("0x" + "11" * 48, "0x" + "1c" * 32, 5)
    nonces = NonceTable()
    nonces.set_last("0x" + "11" * 48, 3)

    payload = state_root_preimage(balances=balances, pools={}, lp_balances=lp, nonces=nonces)
    sections = decode_state_root_preimage(payload)
    assert set(sections) == set(STATE_ROOT_SECTION_LABELS)
    assert b"FEE" in sections


def test_decoder_rejects_trailing_bytes_and_bad_label() -> None:
    payload = state_root_preimage(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    with pytest.raises(ValueError):
        decode_state_root_preimage(payload + b"\x00")
    with pytest.raises(ValueError):
        decode_state_root_preimage(b"not-the-domain-sep" + payload)


def test_uvarint_roundtrip_boundaries() -> None:
    for n in (0, 127, 128, 16_383, 16_384, (1 << 256) - 1):
        enc = encode_uvarint(n)
        dec, off = decode_uvarint(enc)
        assert dec == n and off == len(enc)
