"""
Balance accounting kernel (deterministic, integer-only).

Authoritative / reference implementation of multi-asset balance transitions for
the Rust runtime migration (Phase 6, surface 2). It is the transition form of
``src/state/balances.py`` (the ``BalanceTable``): balances are keyed by
``(pubkey, asset)`` and are non-negative; this kernel exposes the two operations
that compose from ``BalanceTable.add`` / ``.subtract``:

* ``credit(state, recipient, asset, amount)`` — funding primitive (genesis /
  settlement payout). Increases ``(recipient, asset)``.
* ``transfer(state, sender, recipient, asset, amount)`` — moves ``amount`` of
  ``asset`` from ``sender`` to ``recipient``. **Supply-conserving**: it never
  changes the per-asset total. Rejects insufficient balance.

Design rules honored here (see the migration "Hard Rules"):

* No floating point, no wall-clock / randomness / I/O — pure transitions.
* Every transition returns an explicit :class:`BalanceResult` (accepted *or*
  rejected); never a silent fallback. Stable reject codes match the Rust shadow.
* State is keyed per ``(pubkey, asset)``; an operation on one key can never
  perturb another (pinned by the semantic-invariant tests). This is the
  balance-kernel analogue of the fee-router asset-scoping lesson — see
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
    "MAX_BALANCE",
    "PUBKEY_NBYTES",
    "ASSET_NBYTES",
    "STATE_DOMAIN_SEP_LABEL",
    "RECEIPT_DOMAIN_SEP_LABEL",
    "STATE_VERSION",
    "RECEIPT_VERSION",
    "BalanceReceipt",
    "BalanceState",
    "BalanceAccepted",
    "BalanceRejected",
    "BalanceResult",
    "credit",
    "transfer",
]

# Bound balances and amounts so the Rust shadow's u128 arithmetic never wraps;
# matches the fee-router bound for a shared, documented rejection boundary.
MAX_BALANCE = (1 << 112) - 1
PUBKEY_NBYTES = 48  # BLS12-381 pubkey (matches src/state/balances.py)
ASSET_NBYTES = 32  # asset id (matches src/state/state_root.py)

STATE_DOMAIN_SEP_LABEL = "balance_table"
RECEIPT_DOMAIN_SEP_LABEL = "balance_receipt"
STATE_VERSION = 1
RECEIPT_VERSION = 1

# --- Stable rejection codes (must match Rust BalanceRejectedReason::code()) ----
REJ_INVALID_SENDER = "invalid_sender"
REJ_INVALID_RECIPIENT = "invalid_recipient"
REJ_INVALID_ASSET = "invalid_asset"
REJ_INVALID_AMOUNT = "invalid_amount"
REJ_SELF_TRANSFER = "self_transfer"
REJ_INSUFFICIENT_BALANCE = "insufficient_balance"
REJ_BALANCE_OVERFLOW = "balance_overflow"

KIND_CREDIT = "credit"
KIND_TRANSFER = "transfer"

def _is_plain_int(v: object) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _canonical_pubkey(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=PUBKEY_NBYTES, name="pubkey")
    except Exception:
        return None


def _canonical_asset(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=ASSET_NBYTES, name="asset")
    except Exception:
        return None


@dataclass(frozen=True)
class _Entry:
    pubkey: str
    asset: str
    amount: int


def _canonical_entries(entries: tuple[_Entry, ...]) -> tuple[_Entry, ...]:
    seen: set[tuple[str, str]] = set()
    for e in entries:
        if not isinstance(e, _Entry):
            raise TypeError("balance entries must be _Entry")
        if _canonical_pubkey(e.pubkey) != e.pubkey:
            raise ValueError(f"non-canonical pubkey in state: {e.pubkey!r}")
        if _canonical_asset(e.asset) != e.asset:
            raise ValueError(f"non-canonical asset in state: {e.asset!r}")
        if not _is_plain_int(e.amount) or not (1 <= e.amount <= MAX_BALANCE):
            # Zero balances are never stored (sparse table, matching BalanceTable).
            raise ValueError(f"invalid stored balance: {e.amount!r}")
        key = (e.pubkey, e.asset)
        if key in seen:
            raise ValueError(f"duplicate (pubkey, asset) in state: {key!r}")
        seen.add(key)
    return tuple(sorted(entries, key=lambda e: (e.pubkey, e.asset)))


@dataclass(frozen=True)
class BalanceState:
    """Sparse, canonical (pubkey, asset) -> amount table (no zero entries)."""

    entries: tuple[_Entry, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.entries, tuple):
            raise TypeError("entries must be a tuple")
        object.__setattr__(self, "entries", _canonical_entries(self.entries))

    def balance_of(self, pubkey: str, asset: str) -> int:
        pk = _canonical_pubkey(pubkey)
        a = _canonical_asset(asset)
        if pk is None or a is None:
            return 0
        for e in self.entries:
            if e.pubkey == pk and e.asset == a:
                return e.amount
        return 0

    def _set(self, pubkey: str, asset: str, amount: int) -> "BalanceState":
        kept = tuple(e for e in self.entries if not (e.pubkey == pubkey and e.asset == asset))
        if amount == 0:
            return BalanceState(entries=kept)  # sparse: drop zero
        return BalanceState(entries=kept + (_Entry(pubkey, asset, amount),))

    def state_root(self) -> str:
        payload = bytearray(domain_sep_bytes(STATE_DOMAIN_SEP_LABEL, version=STATE_VERSION))
        payload += encode_uvarint(len(self.entries))
        for e in self.entries:
            payload += hex_to_bytes_fixed(e.pubkey, nbytes=PUBKEY_NBYTES, name="pubkey")
            payload += hex_to_bytes_fixed(e.asset, nbytes=ASSET_NBYTES, name="asset")
            payload += encode_uvarint(e.amount)
        return sha256_hex(bytes(payload))


@dataclass(frozen=True)
class BalanceReceipt:
    kind: str  # KIND_CREDIT or KIND_TRANSFER
    sender: Union[str, None]  # None for credit
    recipient: str
    asset: str
    amount: int

    def receipt_hash(self) -> str:
        sender_field = (
            encode_uvarint(0)
            if self.sender is None
            else encode_uvarint(1)
            + hex_to_bytes_fixed(self.sender, nbytes=PUBKEY_NBYTES, name="sender")
        )
        payload = (
            domain_sep_bytes(RECEIPT_DOMAIN_SEP_LABEL, version=RECEIPT_VERSION)
            + b"KND"
            + encode_bytes(self.kind.encode("ascii"))
            + b"SND"
            + sender_field
            + b"RCP"
            + hex_to_bytes_fixed(self.recipient, nbytes=PUBKEY_NBYTES, name="recipient")
            + b"AST"
            + hex_to_bytes_fixed(self.asset, nbytes=ASSET_NBYTES, name="asset")
            + b"AMT"
            + encode_uvarint(self.amount)
        )
        return sha256_hex(payload)


@dataclass(frozen=True)
class BalanceAccepted:
    receipt: BalanceReceipt
    state: BalanceState


@dataclass(frozen=True)
class BalanceRejected:
    reason: str
    detail: Union[str, None] = None


BalanceResult = Union[BalanceAccepted, BalanceRejected]


def _validate_amount(amount: object) -> Union[str, None]:
    if not _is_plain_int(amount) or amount < 1 or amount > MAX_BALANCE:
        return REJ_INVALID_AMOUNT
    return None


def credit(
    *, state: BalanceState, recipient: str, asset: str, amount: int
) -> BalanceResult:
    """Credit ``amount`` of ``asset`` to ``recipient`` (funding primitive)."""
    if not isinstance(state, BalanceState):
        raise TypeError("state must be a BalanceState")

    rcp = _canonical_pubkey(recipient)
    if rcp is None:
        return BalanceRejected(REJ_INVALID_RECIPIENT)
    ast = _canonical_asset(asset)
    if ast is None:
        return BalanceRejected(REJ_INVALID_ASSET)
    amount_rej = _validate_amount(amount)
    if amount_rej is not None:
        return BalanceRejected(amount_rej)

    new_recipient = state.balance_of(rcp, ast) + amount
    if new_recipient > MAX_BALANCE:
        return BalanceRejected(REJ_BALANCE_OVERFLOW)

    new_state = state._set(rcp, ast, new_recipient)
    receipt = BalanceReceipt(KIND_CREDIT, None, rcp, ast, amount)
    return BalanceAccepted(receipt=receipt, state=new_state)


def transfer(
    *, state: BalanceState, sender: str, recipient: str, asset: str, amount: int
) -> BalanceResult:
    """
    Move ``amount`` of ``asset`` from ``sender`` to ``recipient``.

    Supply-conserving (per-asset total unchanged). Validation order is fixed and
    mirrored by the Rust shadow: sender, recipient, asset, amount, self-transfer,
    insufficient balance, overflow. On rejection the caller keeps the prior state.
    """
    if not isinstance(state, BalanceState):
        raise TypeError("state must be a BalanceState")

    snd = _canonical_pubkey(sender)
    if snd is None:
        return BalanceRejected(REJ_INVALID_SENDER)
    rcp = _canonical_pubkey(recipient)
    if rcp is None:
        return BalanceRejected(REJ_INVALID_RECIPIENT)
    ast = _canonical_asset(asset)
    if ast is None:
        return BalanceRejected(REJ_INVALID_ASSET)
    amount_rej = _validate_amount(amount)
    if amount_rej is not None:
        return BalanceRejected(amount_rej)
    if snd == rcp:
        return BalanceRejected(REJ_SELF_TRANSFER)

    sender_balance = state.balance_of(snd, ast)
    if sender_balance < amount:
        return BalanceRejected(REJ_INSUFFICIENT_BALANCE)
    new_recipient = state.balance_of(rcp, ast) + amount
    if new_recipient > MAX_BALANCE:
        return BalanceRejected(REJ_BALANCE_OVERFLOW)

    # Debit sender, then credit recipient (distinct keys: order-independent).
    new_state = state._set(snd, ast, sender_balance - amount)._set(rcp, ast, new_recipient)
    receipt = BalanceReceipt(KIND_TRANSFER, snd, rcp, ast, amount)
    return BalanceAccepted(receipt=receipt, state=new_state)
