"""Immutable identity binding for Tau-native balance dictionaries.

Tau persists BLS public keys using the exact spelling supplied by the chain,
while ZenoDEX committed state uses canonical ``0x``-prefixed keys. This module
keeps that spelling concern in the integration shell and rejects ambiguous
aliases before any value-moving transition runs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping

from ..state.canonical import canonical_hex_fixed_allow_0x


def canonical_tau_pubkey(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a 48-byte hex pubkey string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def tau_egress_pubkey(value: object, *, name: str) -> str:
    """Return the canonical Tau chain spelling for a newly created balance key."""

    return canonical_tau_pubkey(value, name=name)[2:]


@dataclass(frozen=True, order=True)
class TauNativePrincipalBinding:
    canonical_pubkey: str
    chain_key: str
    balance: int


@dataclass(frozen=True, order=True)
class TauChainKeyBinding:
    canonical_pubkey: str
    chain_key: str


@dataclass(frozen=True)
class TauChainKeyIndex:
    entries: tuple[TauChainKeyBinding, ...]

    @classmethod
    def from_chain_keys(cls, chain_keys: Iterable[object]) -> "TauChainKeyIndex":
        by_canonical: dict[str, TauChainKeyBinding] = {}
        for chain_key in chain_keys:
            canonical = canonical_tau_pubkey(chain_key, name="chain_balances key")
            if canonical in by_canonical:
                prior = by_canonical[canonical]
                raise ValueError(
                    "chain_balances has ambiguous identity spellings "
                    f"for {canonical}: {prior.chain_key!r}, {chain_key!r}"
                )
            if not isinstance(chain_key, str):
                raise TypeError("chain_balances key must be a string")
            by_canonical[canonical] = TauChainKeyBinding(
                canonical_pubkey=canonical,
                chain_key=chain_key,
            )
        return cls(entries=tuple(sorted(by_canonical.values())))

    def binding_for(
        self,
        canonical_pubkey: object,
        *,
        preferred_chain_key: object,
        name: str,
    ) -> TauChainKeyBinding:
        canonical = canonical_tau_pubkey(canonical_pubkey, name=f"{name}.canonical_pubkey")
        for binding in self.entries:
            if binding.canonical_pubkey == canonical:
                return binding

        preferred = canonical_tau_pubkey(
            preferred_chain_key,
            name=f"{name}.preferred_chain_key",
        )
        if preferred != canonical:
            raise ValueError(f"{name} preferred chain key does not match canonical identity")
        if not isinstance(preferred_chain_key, str):
            raise TypeError(f"{name}.preferred_chain_key must be a string")
        return TauChainKeyBinding(
            canonical_pubkey=canonical,
            chain_key=preferred_chain_key,
        )


@dataclass(frozen=True)
class TauNativeBalanceSnapshot:
    entries: tuple[TauNativePrincipalBinding, ...]

    @classmethod
    def from_chain_balances(
        cls,
        chain_balances: Mapping[object, object],
    ) -> "TauNativeBalanceSnapshot":
        key_index = TauChainKeyIndex.from_chain_keys(chain_balances.keys())
        entries: list[TauNativePrincipalBinding] = []
        for key_binding in key_index.entries:
            chain_key = key_binding.chain_key
            raw_balance = chain_balances[chain_key]
            if not isinstance(raw_balance, int) or isinstance(raw_balance, bool):
                raise TypeError(f"chain balance for {chain_key!r} must be an int")
            if raw_balance < 0:
                raise ValueError(f"chain balance for {chain_key!r} must be non-negative")
            entries.append(
                TauNativePrincipalBinding(
                    canonical_pubkey=key_binding.canonical_pubkey,
                    chain_key=chain_key,
                    balance=raw_balance,
                )
            )
        return cls(entries=tuple(entries))

    def binding_for(
        self,
        canonical_pubkey: object,
        *,
        preferred_chain_key: object,
        name: str,
    ) -> TauNativePrincipalBinding:
        canonical = canonical_tau_pubkey(canonical_pubkey, name=f"{name}.canonical_pubkey")
        for binding in self.entries:
            if binding.canonical_pubkey == canonical:
                return binding

        preferred = canonical_tau_pubkey(
            preferred_chain_key,
            name=f"{name}.preferred_chain_key",
        )
        if preferred != canonical:
            raise ValueError(f"{name} preferred chain key does not match canonical identity")
        if not isinstance(preferred_chain_key, str):
            raise TypeError(f"{name}.preferred_chain_key must be a string")
        return TauNativePrincipalBinding(
            canonical_pubkey=canonical,
            chain_key=preferred_chain_key,
            balance=0,
        )
