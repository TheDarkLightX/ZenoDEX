"""Fail-closed ingress guard for secret-bearing request fields."""

from __future__ import annotations

from typing import Mapping

_RAW_SIGNING_FIELD_SUFFIXES = (
    "privkey",
    "privkey_hex",
    "private_key",
    "private_key_hex",
    "privatekey",
    "privatekey_hex",
    "secret_key",
    "secret_key_hex",
    "mnemonic",
    "seed_phrase",
)


def reject_raw_signing_material(value: object) -> None:
    """Reject secret-shaped fields recursively before route processing."""

    def visit(current: object, *, path: str) -> None:
        if isinstance(current, Mapping):
            for field, child in current.items():
                name = str(field)
                normalized = name.strip().lower().replace("-", "_")
                child_path = f"{path}.{name}" if path else name
                if any(
                    normalized == suffix or normalized.endswith(f"_{suffix}")
                    for suffix in _RAW_SIGNING_FIELD_SUFFIXES
                ):
                    raise ValueError(f"raw_signing_material_forbidden:{child_path}")
                visit(child, path=child_path)
        elif isinstance(current, list):
            for index, child in enumerate(current):
                visit(child, path=f"{path}[{index}]")

    visit(value, path="")


def contains_raw_signing_material(value: object) -> bool:
    """Return a public-data boolean without exposing the matching value."""
    try:
        reject_raw_signing_material(value)
    except ValueError:
        return True
    return False
