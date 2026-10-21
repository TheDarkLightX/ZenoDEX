"""Canonical balance-entry encoding shared by state commitment readers.

The logical balance map is independent of its in-memory representation.  This
module owns only the version-preserving projection from exact logical entries
to the existing root-section bytes.  Admission of legacy or committed state
remains the responsibility of the caller-specific boundary.
"""

from __future__ import annotations

from typing import TypeAlias

from .canonical import encode_uvarint, hex_to_bytes_fixed

BalanceKeyV1: TypeAlias = tuple[str, str]
LogicalBalanceEntryV1: TypeAlias = tuple[BalanceKeyV1, int]
CanonicalBalanceEntryV1: TypeAlias = tuple[bytes, bytes, int]


def _canonical_balance_entries_v1(
    entries: tuple[LogicalBalanceEntryV1, ...],
    *,
    duplicate_error: str,
) -> tuple[CanonicalBalanceEntryV1, ...]:
    """Validate and order one exact logical balance-entry tuple.

    The canonical order is decoded public-key bytes followed by decoded asset
    bytes.  It therefore does not depend on dict insertion order, persistent
    tree shape, or the ordering policy of an in-memory map implementation.
    """

    if type(entries) is not tuple:
        raise TypeError("balance entries must be an exact tuple")

    canonical: list[CanonicalBalanceEntryV1] = []
    seen: set[tuple[bytes, bytes]] = set()
    for entry in entries:
        if type(entry) is not tuple or len(entry) != 2:
            raise TypeError("balance entry must be an exact pair")
        key, amount = entry
        if type(key) is not tuple or len(key) != 2:
            raise TypeError("balance key must be an exact pair")
        pubkey, asset = key
        if type(pubkey) is not str or type(asset) is not str:
            raise TypeError("balance key components must be exact strings")
        if type(amount) is not int or amount < 0:
            raise ValueError(f"invalid balance amount: {amount!r}")

        pubkey_bytes = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        asset_bytes = hex_to_bytes_fixed(asset, nbytes=32, name="asset")
        decoded_key = (pubkey_bytes, asset_bytes)
        if decoded_key in seen:
            raise ValueError(duplicate_error)
        seen.add(decoded_key)
        canonical.append((pubkey_bytes, asset_bytes, amount))

    canonical.sort(key=lambda item: (item[0], item[1]))
    return tuple(canonical)


def _encode_balance_entries_v1(entries: tuple[CanonicalBalanceEntryV1, ...]) -> bytes:
    """Encode already-canonical entries with the unchanged root-v5 framing."""

    out = bytearray(encode_uvarint(len(entries)))
    for pubkey_bytes, asset_bytes, amount in entries:
        out += pubkey_bytes
        out += asset_bytes
        out += encode_uvarint(amount)
    return bytes(out)


def _encode_logical_balance_entries_v1(
    entries: tuple[LogicalBalanceEntryV1, ...],
    *,
    duplicate_error: str,
) -> bytes:
    return _encode_balance_entries_v1(
        _canonical_balance_entries_v1(entries, duplicate_error=duplicate_error)
    )


__all__: list[str] = []
