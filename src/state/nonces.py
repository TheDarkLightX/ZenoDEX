"""
Nonce table for replay protection (v1).

We track, per sender pubkey, the last accepted intent nonce. The spot DEX uses
strict sequential per-sender batch nonces and shares that policy between the
integration shell and the functional core.

Two phases share one read API:

- ``NonceTable`` is the mutable builder used while a batch is staged.
- ``NonceSnapshot`` is the immutable committed value held by ``DexState``;
  ``to_table()`` returns a fresh builder copy for the next transition.
"""

from __future__ import annotations

from bisect import bisect_left
from collections.abc import Mapping as _MappingABC
from dataclasses import dataclass, field
from typing import Any, Dict, Mapping, Sequence

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x
from .intents import Intent, IntentFieldsNotOwnedError, require_exact_intent

_U32_MAX = 0xFFFFFFFF


@dataclass
class NonceTable:
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


def _require_last_nonce(last_nonce: object) -> int:
    # Same admission rule as ``NonceTable.set_last``.
    if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
        raise TypeError("last_nonce must be a non-negative int")
    if last_nonce > _U32_MAX:
        raise TypeError("last_nonce must fit in u32")
    return int(last_nonce)


def _owned_nonce_entries(
    entries: Mapping[PubKey, int],
) -> tuple[tuple[PubKey, ...], tuple[int, ...]]:
    if not isinstance(entries, _MappingABC):
        raise TypeError("nonce entries must be a mapping")
    rows: dict[PubKey, int] = {}
    for pubkey, last_nonce in entries.items():
        pk = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
        if pk in rows:
            raise ValueError("duplicate canonical pubkey in nonce entries")
        # Zero entries are significant: the state root encodes them.
        rows[pk] = _require_last_nonce(last_nonce)
    ordered = sorted(rows.items())
    return tuple(pk for pk, _last in ordered), tuple(last for _pk, last in ordered)


class NonceSnapshot:
    """
    Immutable, owned committed nonce table: canonical sender_pubkey -> last nonce.

    The read API mirrors ``NonceTable``; there is no setter. ``to_table()``
    returns a fresh mutable builder for staging the next batch.
    """

    __slots__ = ("_last_nonces", "_pubkeys")
    _pubkeys: tuple[PubKey, ...]
    _last_nonces: tuple[int, ...]

    def __init__(self, entries: Mapping[PubKey, int] | None = None) -> None:
        pubkeys, last_nonces = _owned_nonce_entries({} if entries is None else entries)
        object.__setattr__(self, "_pubkeys", pubkeys)
        object.__setattr__(self, "_last_nonces", last_nonces)

    def __setattr__(self, name: str, value: object) -> None:
        del name, value
        raise TypeError("committed nonce snapshot is immutable")

    def __delattr__(self, name: str) -> None:
        del name
        raise TypeError("committed nonce snapshot is immutable")

    def __copy__(self) -> NonceSnapshot:
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> NonceSnapshot:
        memo[id(self)] = self
        return self

    def __eq__(self, other: object) -> bool:
        if type(other) is not NonceSnapshot:
            return NotImplemented
        return self._pubkeys == other._pubkeys and self._last_nonces == other._last_nonces

    def __len__(self) -> int:
        return len(self._pubkeys)

    def __repr__(self) -> str:
        return f"NonceSnapshot({len(self._pubkeys)} entries)"

    def get_last(self, pubkey: PubKey) -> int:
        pk = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
        index = bisect_left(self._pubkeys, pk)
        if index < len(self._pubkeys) and self._pubkeys[index] == pk:
            return self._last_nonces[index]
        return 0

    # Backward-compatible alias mirroring ``NonceTable.get``.
    def get(self, pubkey: PubKey) -> int:
        return self.get_last(pubkey)

    def get_all(self) -> Mapping[PubKey, int]:
        return dict(zip(self._pubkeys, self._last_nonces, strict=True))

    def to_table(self) -> NonceTable:
        """Return a fresh mutable builder holding the same nonce entries."""
        table = NonceTable()
        for pk, last in zip(self._pubkeys, self._last_nonces, strict=True):
            table.set_last(pk, last)
        return table


def snapshot_nonces(value: NonceTable | NonceSnapshot) -> NonceSnapshot:
    """Admit a committed nonce snapshot from a builder or an existing snapshot."""
    if type(value) is NonceSnapshot:
        return value
    if type(value) is NonceTable:
        return NonceSnapshot(value.get_all())
    raise TypeError("nonces must be a NonceTable builder or a NonceSnapshot")


def copy_nonce_table(nonces: NonceTable | NonceSnapshot) -> NonceTable:
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
    nonces: NonceTable | NonceSnapshot,
    intents: Sequence[Intent],
    require_all_nonces: bool,
) -> tuple[bool, str | None, NonceTable | None]:
    """
    Validate and stage a deterministic per-sender nonce advance.

    The input may be a committed ``NonceSnapshot`` or a builder; the staged
    result is always a fresh builder, so the committed input is never mutated.

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
        try:
            intent = require_exact_intent(intent)
            nonce_raw = intent.to_wire_fields().get("nonce")
        except IntentFieldsNotOwnedError:
            return False, "invalid intent fields snapshot", None
        if nonce_raw is None:
            saw_missing = True
            if require_all_nonces:
                return False, "Missing/invalid nonce", None
            continue
        try:
            nonce = _require_int_u32_pos(nonce_raw, name="nonce")
        except ValueError:
            return False, "Missing/invalid nonce", None
        try:
            sender = canonical_hex_fixed_allow_0x(intent.sender_pubkey, nbytes=48, name="sender_pubkey")
        except (TypeError, ValueError) as exc:
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
