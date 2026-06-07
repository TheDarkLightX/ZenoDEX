"""Canonical CLOB transition-journal encodings (Stage 2 proof statement).

The RISC0 guest (``zk/state_proof_risc0/shared/src/clob.rs``) commits an
``event_log_root`` over the incoming events of a matching transition. This module
is the Python MIRROR of that encoding, byte-for-byte, so a Python verifier -- and
the cross-language parity test -- can reproduce the guest's ``event_log_root``.

This closes the same drift-bug class the adversarial review caught for the rule
hashes (the Rust labels had silently diverged from the Python ledger): the
``event_log_root`` is a NEW canonical form the guest defines, so it MUST have a
Python definition pinned by a cross-language test, or a verifier could never
reproduce it.

Encoding (matches ``clob::clob_event_log_root`` + ``encode_clob_order``):
    domain_sep("clob_event_log", v1)
      ++ uvarint(len(events))
      ++ for each event:
           uvarint(side.code) ++ uvarint(price_q_per_base) ++ uvarint(base_qty)
           ++ uvarint(sequence) ++ order_id_bytes(32) ++ owner_bytes(48)
    then SHA-256.
"""
from __future__ import annotations

from typing import Sequence

from ..state.canonical import (
    domain_sep_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from ..state.clob_book import ORDER_ID_NBYTES, OWNER_NBYTES, ClobOrder

EVENT_LOG_DOMAIN_SEP_LABEL = "clob_event_log"
EVENT_LOG_VERSION = 1


def encode_clob_order(order: ClobOrder) -> bytes:
    """Canonical per-order field encoding (mirrors clob.rs::encode_clob_order)."""
    payload = bytearray()
    payload += encode_uvarint(order.side.code)
    payload += encode_uvarint(order.price_q_per_base)
    payload += encode_uvarint(order.base_qty)
    payload += encode_uvarint(order.sequence)
    payload += hex_to_bytes_fixed(order.order_id, nbytes=ORDER_ID_NBYTES, name="order_id")
    payload += hex_to_bytes_fixed(order.owner, nbytes=OWNER_NBYTES, name="owner")
    return bytes(payload)


def clob_event_log_root(events: Sequence[ClobOrder]) -> str:
    """Domain-separated SHA-256 commitment to the incoming event batch.

    Returns 0x-prefixed hex (``sha256_hex``). v1 batches are a single taker, but
    the encoding is length-prefixed so it generalizes to bounded batches.
    """
    payload = bytearray(domain_sep_bytes(EVENT_LOG_DOMAIN_SEP_LABEL, version=EVENT_LOG_VERSION))
    payload += encode_uvarint(len(events))
    for event in events:
        payload += encode_clob_order(event)
    return sha256_hex(bytes(payload))
