from __future__ import annotations

from dataclasses import dataclass

import pytest

from src.fire.compiler.fmos_file_v1 import FireValueRef, _resolve_value_ref


@dataclass(frozen=True)
class _Terms:
    amount: int


def test_resolve_value_ref_rejects_malformed_const_ref_without_release_assert() -> None:
    with pytest.raises(ValueError, match="const value ref missing value"):
        _resolve_value_ref(FireValueRef(kind="const"), _Terms(amount=7))


def test_resolve_value_ref_rejects_malformed_term_ref_without_release_assert() -> None:
    with pytest.raises(ValueError, match="term value ref missing term"):
        _resolve_value_ref(FireValueRef(kind="term"), _Terms(amount=7))


def test_resolve_value_ref_still_rejects_bool_term_values() -> None:
    with pytest.raises(TypeError, match="term field amount must resolve to int"):
        _resolve_value_ref(FireValueRef(kind="term", term="amount"), _Terms(amount=True))
