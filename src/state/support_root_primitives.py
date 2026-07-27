"""Dependency-light values and codecs shared by support-root versions.

The mounted v4 implementation and unmounted exact committed readers share
these protocol primitives.  Keeping them here prevents exact authority code
from importing the mixed legacy support-root implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from .balance_commitment import LogicalBalanceEntryV1, _encode_logical_balance_entries_v1
from .canonical import domain_sep_bytes, encode_bytes, sha256_hex

if TYPE_CHECKING:
    from .state_snapshot_values import CommittedBalanceTableV1

SUPPORT_ROOT_VERSION = 4
INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1 = 5
EXACT_SUPPORT_ROOT_VERSION_V1 = INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1


@dataclass(frozen=True)
class BatchStateSupport:
    """Deterministic, sorted state cells committed by a support root."""

    balance_keys: tuple[tuple[str, str], ...]
    pool_ids: tuple[str, ...]
    lp_keys: tuple[tuple[str, str], ...]
    nonce_keys: tuple[str, ...]


def encode_committed_support_balances_section_v1(
    balances: CommittedBalanceTableV1,
    support: BatchStateSupport,
) -> bytes:
    """Encode support balances from one exact committed balance table."""

    from .state_snapshot_values import CommittedBalanceTableV1
    from .state_snapshots import snapshot_balance_table

    if type(balances) is not CommittedBalanceTableV1:
        raise TypeError("balances must be an exact CommittedBalanceTableV1")
    if type(support) is not BatchStateSupport:
        raise TypeError("support must be an exact BatchStateSupport")
    admitted = snapshot_balance_table(balances)
    logical_entries: tuple[LogicalBalanceEntryV1, ...] = tuple(
        ((pubkey, asset), amount)
        for pubkey, asset in support.balance_keys
        if (amount := admitted.get(pubkey, asset)) != 0
    )
    return _encode_logical_balance_entries_v1(
        logical_entries,
        duplicate_error="duplicate decoded (pubkey, asset) in support balances",
    )


def hash_support_sections_for_version_v1(
    *,
    support_root_version: int,
    balances_section: bytes,
    pools_section: bytes,
    lp_section: bytes,
    lp_duration_section: bytes,
    nonce_section: bytes,
) -> str:
    """Hash canonical support sections under one explicit protocol version."""

    if type(support_root_version) is not int or support_root_version <= 0:
        raise TypeError("support_root_version must be an exact positive int")
    sections = (
        (b"BAL", balances_section),
        (b"POL", pools_section),
        (b"LPB", lp_section),
        (b"LPA", lp_duration_section),
        (b"NNC", nonce_section),
    )
    if any(type(section) is not bytes for _label, section in sections):
        raise TypeError("support-root sections must be exact bytes")
    payload = bytearray(domain_sep_bytes("state_support_root", version=support_root_version))
    for label, section in sections:
        payload += label
        payload += encode_bytes(section)
    return sha256_hex(bytes(payload))


__all__ = (
    "BatchStateSupport",
    "EXACT_SUPPORT_ROOT_VERSION_V1",
    "INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1",
    "SUPPORT_ROOT_VERSION",
    "encode_committed_support_balances_section_v1",
    "hash_support_sections_for_version_v1",
)
