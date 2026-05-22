from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_WALLET_OUTBOUND_GUARD_V1,
    build_autotrader_wallet_outbound_guard_v1_step,
)


def test_build_autotrader_wallet_outbound_guard_v1_step() -> None:
    step = build_autotrader_wallet_outbound_guard_v1_step(
        amount=50,
        max_outbound_amount=100,
        sender_id=7,
        scoped_sender_id=7,
        destination_allowed=1,
        session_active=1,
        policy_hash_ok=1,
        enabled=1,
    )
    assert AUTOTRADER_WALLET_OUTBOUND_GUARD_V1.spec_id == "autotrader_wallet_outbound_guard_v1"
    assert step["i1"] == 50
    assert step["i8"] == 1


def test_build_autotrader_wallet_outbound_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="enabled must be 0 or 1"):
        build_autotrader_wallet_outbound_guard_v1_step(
            amount=50,
            max_outbound_amount=100,
            sender_id=7,
            scoped_sender_id=7,
            destination_allowed=1,
            session_active=1,
            policy_hash_ok=1,
            enabled=2,
        )
