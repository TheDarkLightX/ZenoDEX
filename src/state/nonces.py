"""
Nonce table for replay protection (v1).

We track, per sender pubkey, the last accepted intent nonce. The spot DEX uses
strict sequential per-sender batch nonces and shares that policy between the
integration shell and the functional core.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Mapping, NoReturn, Sequence

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x
from .immutable import FrozenDict
from .intents import Intent, require_exact_intent

_U32_MAX = 0xFFFFFFFF


def _canonical_nonce_pubkey(pubkey: object) -> str:
    if type(pubkey) is not str or not pubkey:
        raise TypeError("pubkey must be a non-empty exact string")
    return canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")


def _require_nonce_value(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise TypeError(f"{name} must be a non-negative int")
    if value > _U32_MAX:
        raise TypeError(f"{name} must fit in u32")
    return value


def _validated_nonce_entries(source: "NonceTable") -> dict[PubKey, int]:
    raw = object.__getattribute__(source, "_last")
    if type(raw) not in (dict, FrozenDict):
        raise TypeError("nonce storage must be an exact dict snapshot")
    owned: dict[PubKey, int] = {}
    for raw_pubkey, raw_nonce in raw.items():
        pubkey = _canonical_nonce_pubkey(raw_pubkey)
        if pubkey != raw_pubkey:
            raise ValueError("stored nonce pubkeys must use canonical lowercase wire form")
        if pubkey in owned:
            raise ValueError("duplicate decoded pubkey in nonces")
        owned[pubkey] = _require_nonce_value(raw_nonce, name="stored nonce")
    return owned


@dataclass(slots=True)
class NonceTable:
    """
    Mutable mapping: sender_pubkey -> last_used_nonce.

    This is intentionally similar in spirit to `BalanceTable`: a small, explicit
    state table with deterministic iteration helpers.
    """

    _last: Dict[PubKey, int] = field(default_factory=dict)

    def get_last(self, pubkey: PubKey) -> int:
        pk = _canonical_nonce_pubkey(pubkey)
        v = self._last.get(pk, 0)
        if type(v) is not int or not (0 <= v <= _U32_MAX):
            raise ValueError(f"invalid stored nonce for {pubkey!r}: {v!r}")
        return v

    # Backward-compatible alias used by older integration code/tests.
    def get(self, pubkey: PubKey) -> int:
        return self.get_last(pubkey)

    def set_last(self, pubkey: PubKey, last_nonce: int) -> None:
        pk = _canonical_nonce_pubkey(pubkey)
        self._last[pk] = _require_nonce_value(last_nonce, name="last_nonce")

    # Backward-compatible alias: apply accepted nonce update.
    def apply_accept(self, pubkey: PubKey, nonce: int) -> None:
        self.set_last(pubkey, nonce)

    def get_all(self) -> Mapping[PubKey, int]:
        # Return a shallow copy to avoid accidental mutation during iteration.
        return dict(self._last)


class FrozenNonceTable(NonceTable):
    """Transitively immutable replay-state snapshot."""

    __slots__ = ()

    def __init__(self, source: NonceTable) -> None:
        try:
            object.__getattribute__(self, "_last")
        except AttributeError:
            pass
        else:
            raise TypeError("FrozenNonceTable is already initialized")
        if type(source) not in (NonceTable, FrozenNonceTable):
            raise TypeError("source must be an exact NonceTable snapshot")
        object.__setattr__(self, "_last", FrozenDict(_validated_nonce_entries(source)))

    def __setattr__(self, name: str, value: object) -> NoReturn:
        raise TypeError("FrozenNonceTable cannot be mutated")

    def set_last(self, pubkey: PubKey, last_nonce: int) -> NoReturn:
        raise TypeError("FrozenNonceTable cannot be mutated")

    def apply_accept(self, pubkey: PubKey, nonce: int) -> NoReturn:
        raise TypeError("FrozenNonceTable cannot be mutated")


def copy_nonce_table(nonces: NonceTable) -> NonceTable:
    if type(nonces) not in (NonceTable, FrozenNonceTable):
        raise TypeError("nonces must be an exact NonceTable snapshot")
    copied = NonceTable()
    for pk, last in _validated_nonce_entries(nonces).items():
        copied.set_last(pk, last)
    return copied


def freeze_nonce_table(nonces: NonceTable) -> FrozenNonceTable:
    if type(nonces) is FrozenNonceTable:
        try:
            storage = object.__getattribute__(nonces, "_last")
        except AttributeError as exc:
            raise TypeError("FrozenNonceTable is not initialized") from exc
        if type(storage) is not FrozenDict:
            raise TypeError("FrozenNonceTable storage is not sealed")
        return nonces
    if type(nonces) is not NonceTable:
        raise TypeError("nonces must be an exact NonceTable snapshot")
    return FrozenNonceTable(nonces)


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
        require_exact_intent(intent)
        fields = intent.fields or {}
        nonce_raw = fields.get("nonce") if isinstance(fields, Mapping) else None
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
