from __future__ import annotations

import pytest

from src.kernels.python.strategy_nonce_guard_v1_adapter import check_strategy_nonce


def test_check_strategy_nonce_accepts_sequential_nonce() -> None:
    result = check_strategy_nonce(intent_nonce=9, last_used_nonce=8, expected_nonce=9)
    assert result.ok is True
    assert result.error is None


def test_check_strategy_nonce_rejects_invalid_expected_nonce() -> None:
    result = check_strategy_nonce(intent_nonce=9, last_used_nonce=8, expected_nonce=10)
    assert result.ok is False
    assert result.error == "nonce_expected_invalid:10!=9"


def test_check_strategy_nonce_rejects_stale_and_non_sequential_nonces() -> None:
    stale = check_strategy_nonce(intent_nonce=8, last_used_nonce=8, expected_nonce=9)
    assert stale.ok is False
    assert stale.error == "nonce_not_fresh:8<=8"

    non_sequential = check_strategy_nonce(intent_nonce=11, last_used_nonce=8, expected_nonce=9)
    assert non_sequential.ok is False
    assert non_sequential.error == "nonce_expected_mismatch:11!=9"


def test_check_strategy_nonce_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="intent_nonce must be an int"):
        check_strategy_nonce(intent_nonce="9", last_used_nonce=8, expected_nonce=9)
    with pytest.raises(ValueError, match="expected_nonce out of u32 range"):
        check_strategy_nonce(intent_nonce=9, last_used_nonce=8, expected_nonce=0)
