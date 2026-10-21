"""
Nonce table for replay protection (v1).

We track, per sender pubkey, the last accepted intent nonce. The spot DEX uses
strict sequential per-sender batch nonces and shares that policy between the
integration shell and the functional core.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Mapping, Sequence

from .balances import PubKey, _SnapshotSealMixin
from .canonical import canonical_hex_fixed_allow_0x
from .intents import Intent

# Keep the pinned concolic path offsets stable across this representation change.
_U32_MAX = 0xFFFFFFFF


@dataclass(slots=True)
class NonceTable(_SnapshotSealMixin):
    """
    Mutable mapping: sender_pubkey -> last_used_nonce.

    This is intentionally similar in spirit to `BalanceTable`: a small, explicit
    state table with deterministic iteration helpers.
    """

    _last: Dict[PubKey, int] = field(default_factory=dict)

    def get_last(self, pubkey: PubKey) -> int:
        pk = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
        v = self._last.get(pk, 0)
        if not isinstance(v, int) or isinstance(v, bool) or v < 0:
            raise ValueError(f"invalid stored nonce for {pubkey!r}: {v!r}")
        return int(v)

    # Backward-compatible alias used by older integration code/tests.
    def get(self, pubkey: PubKey) -> int:
        return self.get_last(pubkey)

    def set_last(self, pubkey: PubKey, last_nonce: int) -> None:
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise TypeError("last_nonce must be a non-negative int")
        if last_nonce > 0xFFFFFFFF:
            raise TypeError("last_nonce must fit in u32")
        pk = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
        self._last[pk] = int(last_nonce)

    # Backward-compatible alias: apply accepted nonce update.
    def apply_accept(self, pubkey: PubKey, nonce: int) -> None:
        self.set_last(pubkey, nonce)

    def get_all(self) -> Mapping[PubKey, int]:
        # Return a shallow copy to avoid accidental mutation during iteration.
        return dict(self._last)


def copy_nonce_table(nonces: NonceTable) -> NonceTable:
    copied = NonceTable()
    for pk, last in nonces.get_all().items():
        copied.set_last(pk, int(last))
    return copied


def _require_int_u32_pos(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > _U32_MAX:
        raise ValueError(f"{name} must fit in u32")
    return int(value)


def validate_and_apply_intent_nonce_batch(
    *,
    nonces: NonceTable,
    intents: Sequence[Intent],
    require_all_nonces: bool,
) -> tuple[bool, str | None, NonceTable | None]:
    """
    Validate and stage a deterministic per-sender nonce advance.

    Policy:
    - When enabled, every nonce-bearing batch must use a contiguous range
      `{last+1, ..., last+k}` per sender, regardless of input order.
    - `require_all_nonces=True` rejects any batch with a missing/invalid nonce.
    - `require_all_nonces=False` keeps backward compatibility for pure-core tests:
      nonce-free batches are accepted as a no-op, but mixed nonce presence rejects.
    """
    if not intents:
        return True, None, copy_nonce_table(nonces)

    per_sender: dict[str, list[int]] = {}
    saw_nonce = False
    saw_missing = False

    for intent in intents:
        fields = intent.fields or {}
        nonce_raw = fields.get("nonce") if isinstance(fields, dict) else None
        if nonce_raw is None:
            saw_missing = True
            if require_all_nonces:
                return False, "Missing/invalid nonce", None
            continue
        try:
            nonce = _require_int_u32_pos(nonce_raw, name="nonce")
        except Exception:
            return False, "Missing/invalid nonce", None
        try:
            sender = canonical_hex_fixed_allow_0x(intent.sender_pubkey, nbytes=48, name="sender_pubkey")
        except Exception as exc:
            return False, f"invalid sender_pubkey for nonce accounting: {exc}", None
        per_sender.setdefault(sender, []).append(int(nonce))
        saw_nonce = True

    if saw_nonce and saw_missing:
        return False, "nonce presence must be consistent across batch", None
    if not saw_nonce:
        return True, None, copy_nonce_table(nonces)

    updated = copy_nonce_table(nonces)
    for sender, nonce_list in per_sender.items():
        if len(nonce_list) != len(set(nonce_list)):
            return False, "duplicate nonce in batch", None
        nonce_list_sorted = sorted(nonce_list)
        last = int(updated.get_last(sender))
        expected = list(range(last + 1, last + 1 + len(nonce_list_sorted)))
        if nonce_list_sorted != expected:
            return False, "nonce sequence invalid", None
        updated.set_last(sender, expected[-1])
    return True, None, updated
