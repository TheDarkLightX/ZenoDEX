from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_WALLET_CAPABILITY_GUARD_V1,
    build_autotrader_wallet_capability_guard_v1_step,
)


def test_build_autotrader_wallet_capability_guard_v1_step() -> None:
    step = build_autotrader_wallet_capability_guard_v1_step(
        enabled=1,
        signer_ok=1,
        asset_in_allowed=1,
        asset_out_allowed=1,
        action_allowed=1,
        chain_id_ok=1,
        current_epoch=5,
        valid_from_epoch=1,
        valid_until_epoch=10,
        order_amount=100,
        notional_remaining=150,
    )
    assert AUTOTRADER_WALLET_CAPABILITY_GUARD_V1.spec_id == "autotrader_wallet_capability_guard_v1"
    assert step["i10"] == 100
    assert step["i11"] == 150


def test_build_autotrader_wallet_capability_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="enabled must be 0 or 1"):
        build_autotrader_wallet_capability_guard_v1_step(
            enabled=2,
            signer_ok=1,
            asset_in_allowed=1,
            asset_out_allowed=1,
            action_allowed=1,
            chain_id_ok=1,
            current_epoch=5,
            valid_from_epoch=1,
            valid_until_epoch=10,
            order_amount=100,
            notional_remaining=150,
        )
