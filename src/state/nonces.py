"""
Nonce table for replay protection (v1).

We track, per sender pubkey, the last accepted intent nonce. Policy is defined
by the integration layer (currently: strict sequential nonces).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Mapping

from .balances import PubKey
from .canonical import canonical_hex_fixed_allow_0x


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

    def set_last(self, pubkey: PubKey, last_nonce: int) -> None:
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise TypeError("last_nonce must be a non-negative int")
        if last_nonce > 0xFFFFFFFF:
            raise TypeError("last_nonce must fit in u32")
        pk = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
        self._last[pk] = int(last_nonce)

    def get_all(self) -> Mapping[PubKey, int]:
        # Return a shallow copy to avoid accidental mutation during iteration.
        return dict(self._last)
