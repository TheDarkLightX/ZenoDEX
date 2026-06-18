"""Typed fill-field readers for strong settlement replay."""

from __future__ import annotations

from typing import Optional, Tuple

from .domain_limits import is_strict_int


def read_optional_non_negative_fill_int(
    value: object,
    *,
    operation: str,
    field_name: str,
    intent_id: str,
) -> Tuple[Optional[int], Optional[str]]:
    if value is None:
        return 0, None
    if not is_strict_int(value):
        return None, f"{operation} fill.{field_name} must be int for intent_id={intent_id}"
    if int(value) < 0:
        return None, f"{operation} fill.{field_name} must be non-negative for intent_id={intent_id}"
    return int(value), None
