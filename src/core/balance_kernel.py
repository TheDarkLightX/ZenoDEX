"""
Balance accounting kernel (deterministic, integer-only).

Python reference implementation of multi-asset balance transitions for the Rust
runtime migration (Phase 6, surface 2). By default it is still the runtime
authority; deployment profiles may promote the Rust transition with Python
shadow checking. It is the transition form of ``src/state/balances.py`` (the
``BalanceTable``): balances are keyed by
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
from typing import Any, Union

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
    "BALANCE_SURFACE",
    "credit",
    "transfer",
]

BALANCE_SURFACE = "balances"

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
    except ValueError:
        return None


def _canonical_asset(value: object) -> Union[str, None]:
    if not isinstance(value, str):
        return None
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=ASSET_NBYTES, name="asset")
    except ValueError:
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


def _state_entries_json(state: BalanceState) -> list[dict[str, Any]]:
    return [{"pubkey": e.pubkey, "asset": e.asset, "amount": e.amount} for e in state.entries]


def _result_to_authority_doc(pre_state: BalanceState, result: BalanceResult) -> dict[str, Any]:
    pre_root = pre_state.state_root()
    if isinstance(result, BalanceAccepted):
        return {
            "version": 1,
            "kernel": BALANCE_SURFACE,
            "accept": True,
            "reject_reason": None,
            "receipt_hash": result.receipt.receipt_hash(),
            "receipt": {
                "kind": result.receipt.kind,
                "sender": result.receipt.sender,
                "recipient": result.receipt.recipient,
                "asset": result.receipt.asset,
                "amount": str(result.receipt.amount),
            },
            "pre_state_root": pre_root,
            "post_state_root": result.state.state_root(),
            "post_state_entries": [
                {"pubkey": e.pubkey, "asset": e.asset, "amount": str(e.amount)}
                for e in result.state.entries
            ],
        }
    return {
        "version": 1,
        "kernel": BALANCE_SURFACE,
        "accept": False,
        "reject_reason": result.reason,
        "receipt_hash": None,
        "receipt": None,
        "pre_state_root": pre_root,
        "post_state_root": pre_root,
        "post_state_entries": [
            {"pubkey": e.pubkey, "asset": e.asset, "amount": str(e.amount)}
            for e in pre_state.entries
        ],
    }


def _authority_doc_to_result(doc: dict[str, Any]) -> BalanceResult:
    if bool(doc.get("accept")):
        receipt_doc = doc.get("receipt")
        if not isinstance(receipt_doc, dict):
            raise ValueError("accepted balances authority doc missing receipt")
        entries = tuple(
            _Entry(str(entry["pubkey"]), str(entry["asset"]), int(entry["amount"]))
            for entry in doc.get("post_state_entries", [])
        )
        state = BalanceState(entries=entries)
        sender = receipt_doc.get("sender")
        receipt = BalanceReceipt(
            kind=str(receipt_doc["kind"]),
            sender=None if sender is None else str(sender),
            recipient=str(receipt_doc["recipient"]),
            asset=str(receipt_doc["asset"]),
            amount=int(receipt_doc["amount"]),
        )
        return BalanceAccepted(receipt=receipt, state=state)
    reason = doc.get("reject_reason")
    if not isinstance(reason, str):
        raise ValueError("rejected balances authority doc missing reason")
    return BalanceRejected(reason)


def _decide_balance(
    *,
    state: BalanceState,
    tx: dict[str, Any],
    python_fn,
) -> BalanceResult:
    from src.runtime.authority import AuthorityMode, active_mode, decide
    from src.runtime.rust_invoker import balance_op

    mode = active_mode(BALANCE_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return python_fn()

    def python_doc() -> dict[str, Any]:
        return _result_to_authority_doc(state, python_fn())

    def rust_doc() -> dict[str, Any]:
        return balance_op(state_entries=_state_entries_json(state), tx=tx)

    decision = decide(
        BALANCE_SURFACE,
        mode,
        python_fn=python_doc,
        rust_fn=rust_doc,
    )
    return _authority_doc_to_result(decision.result)


def _validate_amount(amount: object) -> Union[str, None]:
    if not _is_plain_int(amount) or amount < 1 or amount > MAX_BALANCE:
        return REJ_INVALID_AMOUNT
    return None


def _credit_python(
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


def credit(
    *, state: BalanceState, recipient: str, asset: str, amount: int
) -> BalanceResult:
    """Authority-routed credit transition."""
    return _decide_balance(
        state=state,
        tx={"kind": KIND_CREDIT, "recipient": recipient, "asset": asset, "amount": amount},
        python_fn=lambda: _credit_python(state=state, recipient=recipient, asset=asset, amount=amount),
    )


def _transfer_python(
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


def transfer(
    *, state: BalanceState, sender: str, recipient: str, asset: str, amount: int
) -> BalanceResult:
    """Authority-routed transfer transition."""
    return _decide_balance(
        state=state,
        tx={
            "kind": KIND_TRANSFER,
            "sender": sender,
            "recipient": recipient,
            "asset": asset,
            "amount": amount,
        },
        python_fn=lambda: _transfer_python(
            state=state,
            sender=sender,
            recipient=recipient,
            asset=asset,
            amount=amount,
        ),
    )
