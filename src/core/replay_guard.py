"""
Replay / idempotency guard (deterministic, integer-only).

This is the **reference / authoritative** implementation of ZenoDEX's replay
protection for the Rust runtime migration (Phase 6, surface 1). It is the
single-transition form of the per-sender strict-sequential nonce policy already
enforced by :mod:`src.state.nonces`
(:func:`validate_and_apply_intent_nonce_batch`): each sender must use nonces
``1, 2, 3, …`` with no gaps, and any nonce at or below the last accepted one is
rejected (duplicate / replay).

Design rules honored here (see the migration "Hard Rules"):

* No floating point, no wall-clock / randomness / I/O — a pure transition.
* Every transition returns an explicit :class:`AdmitResult` (accepted *or*
  rejected). It never silently falls back; every rejection carries a stable
  machine code that matches the Rust ``ReplayRejectedReason::code()``.
* State is keyed **per sender**; one sender's nonce stream can never advance or
  block another's (a property pinned by the semantic-invariant tests).

Lesson carried from the fee-router asset-scoping bug: cross-language equality is
necessary but not sufficient. This surface ships independent *semantic
invariants* (per-sender isolation, monotonic acceptance, anti-replay) in
addition to the Python/Rust differential — see
``docs/runtime/SEMANTIC_DRIFT_CONTROLS.md``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)

__all__ = [
    "U32_MAX",
    "SENDER_NBYTES",
    "STATE_DOMAIN_SEP_LABEL",
    "RECEIPT_DOMAIN_SEP_LABEL",
    "STATE_VERSION",
    "RECEIPT_VERSION",
    "AdmissionReceipt",
    "ReplayGuardState",
    "AdmitAccepted",
    "AdmitRejected",
    "AdmitResult",
    "admit",
]

U32_MAX = 0xFFFFFFFF
SENDER_NBYTES = 48  # BLS12-381 pubkey, matching src/state/nonces.py

STATE_DOMAIN_SEP_LABEL = "replay_guard_state"
RECEIPT_DOMAIN_SEP_LABEL = "replay_admission"
STATE_VERSION = 1
RECEIPT_VERSION = 1

# --- Stable rejection codes (must match Rust ReplayRejectedReason::code()) -----
REJ_INVALID_SENDER = "invalid_sender"
REJ_INVALID_NONCE = "invalid_nonce"
REJ_DUPLICATE_NONCE = "duplicate_nonce"  # nonce == last accepted
REJ_STALE_NONCE = "stale_nonce"  # nonce < last accepted (replay of an old tx)
REJ_NONCE_GAP = "nonce_gap"  # nonce > last + 1

def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _canonical_sender(sender: object) -> Union[str, None]:
    """Return the canonical lowercase 0x-prefixed sender, or ``None`` if invalid."""
    if not isinstance(sender, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(sender, nbytes=SENDER_NBYTES, name="sender")
    except Exception:
        return None


@dataclass(frozen=True)
class _Entry:
    """One sender's last accepted nonce."""

    sender: str
    last_nonce: int


def _canonical_entries(entries: tuple[_Entry, ...]) -> tuple[_Entry, ...]:
    seen: set[str] = set()
    for e in entries:
        if not isinstance(e, _Entry):
            raise TypeError("replay-guard entries must be _Entry")
        if _canonical_sender(e.sender) != e.sender:
            raise ValueError(f"non-canonical sender in state: {e.sender!r}")
        if not _is_plain_int(e.last_nonce) or not (1 <= e.last_nonce <= U32_MAX):
            raise ValueError(f"invalid stored nonce: {e.last_nonce!r}")
        if e.sender in seen:
            raise ValueError(f"duplicate sender in state: {e.sender!r}")
        seen.add(e.sender)
    # Sort by the raw 48-byte sender value (== lowercase-hex order), matching
    # the nonce section of src/state/state_root.py.
    return tuple(sorted(entries, key=lambda e: e.sender))


@dataclass(frozen=True)
class ReplayGuardState:
    """Per-sender last-accepted-nonce table (canonical, immutable)."""

    entries: tuple[_Entry, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.entries, tuple):
            raise TypeError("entries must be a tuple")
        object.__setattr__(self, "entries", _canonical_entries(self.entries))

    def last_for(self, sender: str) -> int:
        canon = _canonical_sender(sender)
        if canon is None:
            return 0
        for e in self.entries:
            if e.sender == canon:
                return e.last_nonce
        return 0

    def with_last(self, sender: str, last_nonce: int) -> "ReplayGuardState":
        canon = _canonical_sender(sender)
        if canon is None:
            raise ValueError(f"invalid sender: {sender!r}")
        kept = tuple(e for e in self.entries if e.sender != canon)
        return ReplayGuardState(entries=kept + (_Entry(canon, last_nonce),))

    def state_root(self) -> str:
        payload = bytearray(domain_sep_bytes(STATE_DOMAIN_SEP_LABEL, version=STATE_VERSION))
        payload += encode_uvarint(len(self.entries))
        for e in self.entries:
            payload += hex_to_bytes_fixed(e.sender, nbytes=SENDER_NBYTES, name="sender")
            payload += encode_uvarint(e.last_nonce)
        return sha256_hex(bytes(payload))


@dataclass(frozen=True)
class AdmissionReceipt:
    sender: str
    nonce: int
    prev_nonce: int

    def receipt_hash(self) -> str:
        payload = (
            domain_sep_bytes(RECEIPT_DOMAIN_SEP_LABEL, version=RECEIPT_VERSION)
            + b"SND"
            + encode_bytes(hex_to_bytes_fixed(self.sender, nbytes=SENDER_NBYTES, name="sender"))
            + b"NON"
            + encode_uvarint(self.nonce)
            + b"PRV"
            + encode_uvarint(self.prev_nonce)
        )
        return sha256_hex(payload)


@dataclass(frozen=True)
class AdmitAccepted:
    receipt: AdmissionReceipt
    state: ReplayGuardState


@dataclass(frozen=True)
class AdmitRejected:
    reason: str
    detail: Union[str, None] = None


AdmitResult = Union[AdmitAccepted, AdmitRejected]


def admit(*, state: ReplayGuardState, sender: str, nonce: int) -> AdmitResult:
    """
    Admit (sender, nonce) under the strict-sequential per-sender policy.

    Accepts iff ``nonce == last_accepted(sender) + 1``. Rejects duplicates
    (``== last``), replays of older txs (``< last``), gaps (``> last + 1``), and
    malformed sender/nonce — each with a stable reason code. On rejection the
    state is unchanged (the caller keeps the prior state).
    """
    if not isinstance(state, ReplayGuardState):
        raise TypeError("state must be a ReplayGuardState")

    canon = _canonical_sender(sender)
    if canon is None:
        return AdmitRejected(REJ_INVALID_SENDER)
    if not _is_plain_int(nonce) or not (1 <= nonce <= U32_MAX):
        return AdmitRejected(REJ_INVALID_NONCE)

    last = state.last_for(canon)
    if nonce == last:
        return AdmitRejected(REJ_DUPLICATE_NONCE)
    if nonce < last:
        return AdmitRejected(REJ_STALE_NONCE)
    if nonce > last + 1:
        return AdmitRejected(REJ_NONCE_GAP)

    # nonce == last + 1: accept.
    new_state = state.with_last(canon, nonce)
    receipt = AdmissionReceipt(sender=canon, nonce=nonce, prev_nonce=last)
    return AdmitAccepted(receipt=receipt, state=new_state)
