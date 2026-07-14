"""Small shared exact-type and bounded-arithmetic validation helpers."""

from __future__ import annotations

from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0

from .errors import reject
from .model import MAX_U64


def exact_equal(left: object, right: object) -> bool:
    if type(left) is not type(right):
        return False
    try:
        return canonical_json_bytes_v0(left) == canonical_json_bytes_v0(right)
    except (TypeError, ValueError, RecursionError):
        return False


def checked_add(left: int, right: int, name: str) -> int:
    result = left + right
    if result > MAX_U64:
        reject("ARITHMETIC_OVERFLOW", f"{name} exceeds u64")
    return result


def require_list(value: object, *, name: str) -> list[object]:
    if type(value) is not list:
        reject("EVIDENCE_SCHEMA_MISMATCH", f"{name} must be an exact list")
    return value
