"""Lightweight hash commitments for governance-only receipt paths."""

from __future__ import annotations

import re

from src.state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    sha256_hex,
)


LEDGER_ROOT_VERSION = 1
_DOMAIN_RE = re.compile(r"^[A-Za-z0-9_.:/-]+$")


def _validate_domain(domain: str) -> str:
    if not isinstance(domain, str) or not domain:
        raise TypeError("domain must be a non-empty str")
    if not _DOMAIN_RE.fullmatch(domain):
        raise ValueError("domain contains unsupported characters")
    return domain


def hash_v0(domain: str, value: object | bytes) -> str:
    """Hash a value with the ZenoLedger v0 domain format without importing the ledger runtime."""

    domain = _validate_domain(domain)
    prefix = domain_sep_bytes(f"zeno_ledger_{domain}", version=LEDGER_ROOT_VERSION)
    if isinstance(value, (bytes, bytearray)):
        payload = prefix + encode_bytes(bytes(value))
    else:
        payload = prefix + encode_bytes(canonical_json_bytes(value))
    return sha256_hex(payload)
