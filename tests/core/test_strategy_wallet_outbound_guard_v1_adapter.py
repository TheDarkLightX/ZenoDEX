from __future__ import annotations

import pytest

from src.kernels.python.strategy_wallet_outbound_guard_v1_adapter import (
    check_strategy_wallet_outbound_guard,
)


def test_wallet_outbound_guard_accepts_disabled_and_sender_mismatch_as_neutral() -> None:
    disabled = check_strategy_wallet_outbound_guard(
        amount=500,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=0,
        session_active=0,
        policy_hash_ok=0,
        enabled=0,
    )
    assert disabled.ok is True
    assert disabled.rule_enabled is False

    mismatch = check_strategy_wallet_outbound_guard(
        amount=500,
        max_outbound_amount=100,
        sender_id=8,
        scoped_sender_id=7,
        destination_allowed=0,
        session_active=0,
        policy_hash_ok=0,
        enabled=1,
    )
    assert mismatch.ok is True
    assert mismatch.sender_scope_match is False


def test_wallet_outbound_guard_accepts_matching_sender_within_cap() -> None:
    result = check_strategy_wallet_outbound_guard(
        amount=99,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=1,
        session_active=1,
        policy_hash_ok=1,
        enabled=1,
    )
    assert result.ok is True
    assert result.context_ok is True
    assert result.error is None


def test_wallet_outbound_guard_rejects_matching_sender_failures() -> None:
    amount = check_strategy_wallet_outbound_guard(
        amount=101,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=1,
        session_active=1,
        policy_hash_ok=1,
        enabled=1,
    )
    assert amount.ok is False
    assert amount.error == "wallet_outbound_amount_exceeded:101>100"

    dst = check_strategy_wallet_outbound_guard(
        amount=10,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=0,
        session_active=1,
        policy_hash_ok=1,
        enabled=1,
    )
    assert dst.ok is False
    assert dst.error == "wallet_outbound_destination_blocked"

    sess = check_strategy_wallet_outbound_guard(
        amount=10,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=1,
        session_active=0,
        policy_hash_ok=1,
        enabled=1,
    )
    assert sess.ok is False
    assert sess.error == "wallet_outbound_session_inactive"

    pol = check_strategy_wallet_outbound_guard(
        amount=10,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=1,
        session_active=1,
        policy_hash_ok=0,
        enabled=1,
    )
    assert pol.ok is False
    assert pol.error == "wallet_outbound_policy_hash_mismatch"


def test_wallet_outbound_guard_rejects_bad_inputs() -> None:
    with pytest.raises(TypeError, match="amount must be an int"):
        check_strategy_wallet_outbound_guard(
            amount=True,
            max_outbound_amount=1,
            sender_id=1,
            scoped_sender_id=1,
            destination_allowed=1,
            session_active=1,
            policy_hash_ok=1,
            enabled=1,
        )
    with pytest.raises(ValueError, match="max_outbound_amount out of u32 range"):
        check_strategy_wallet_outbound_guard(
            amount=1,
            max_outbound_amount=0x1_0000_0000,
            sender_id=1,
            scoped_sender_id=1,
            destination_allowed=1,
            session_active=1,
            policy_hash_ok=1,
            enabled=1,
        )
    with pytest.raises(ValueError, match="enabled must be 0 or 1"):
        check_strategy_wallet_outbound_guard(
            amount=1,
            max_outbound_amount=1,
            sender_id=1,
            scoped_sender_id=1,
            destination_allowed=1,
            session_active=1,
            policy_hash_ok=1,
            enabled=2,
        )
