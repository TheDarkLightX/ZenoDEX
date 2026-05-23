from __future__ import annotations

import pytest

from src.agents.strategy_ir import StrategyAction
from src.integration.autotrader_signals import AutoTraderWalletCapability
from src.kernels.python.strategy_wallet_capability_guard_v1_adapter import check_wallet_capability


def _capability(**overrides: object) -> AutoTraderWalletCapability:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "valid_from_epoch": 1,
        "valid_until_epoch": 10,
        "notional_remaining": 100,
        "allowed_assets": ("A", "B"),
        "allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN,),
        "enabled": True,
    }
    data.update(overrides)
    return AutoTraderWalletCapability(**data)


def test_check_wallet_capability_accepts_in_scope_order() -> None:
    result = check_wallet_capability(
        capability=_capability(),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=100,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert result.ok is True
    assert result.error is None


def test_check_wallet_capability_rejects_disabled_and_signer_mismatch() -> None:
    disabled = check_wallet_capability(
        capability=_capability(enabled=False),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert disabled.ok is False
    assert disabled.error == "wallet_capability_disabled"

    signer = check_wallet_capability(
        capability=_capability(),
        signer_pubkey="other.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert signer.ok is False
    assert signer.error == "wallet_capability_signer_mismatch"


def test_check_wallet_capability_rejects_scope_violations() -> None:
    chain = check_wallet_capability(
        capability=_capability(),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-other",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert chain.ok is False
    assert chain.error == "wallet_capability_chain_mismatch:tau-other!=tau-net-alpha"

    asset_scope = check_wallet_capability(
        capability=_capability(allowed_assets=("A",)),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert asset_scope.ok is False
    assert asset_scope.error == "wallet_capability_asset_scope_violation:A/B"

    action_scope = check_wallet_capability(
        capability=_capability(),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_ORDER_INTENT,
    )
    assert action_scope.ok is False
    assert action_scope.error == "wallet_capability_action_not_allowed:place_order_intent"


def test_check_wallet_capability_rejects_window_and_notional_failures() -> None:
    not_open = check_wallet_capability(
        capability=_capability(valid_from_epoch=6),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert not_open.ok is False
    assert not_open.error == "wallet_capability_window_not_open:5<6"

    expired = check_wallet_capability(
        capability=_capability(valid_until_epoch=4),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert expired.ok is False
    assert expired.error == "wallet_capability_expired:5>4"

    notional = check_wallet_capability(
        capability=_capability(notional_remaining=9),
        signer_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        current_epoch=5,
        asset_in="A",
        asset_out="B",
        order_amount=10,
        action=StrategyAction.PLACE_SWAP_EXACT_IN,
    )
    assert notional.ok is False
    assert notional.error == "wallet_capability_notional_exceeded:10>9"


def test_check_wallet_capability_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        check_wallet_capability(
            capability="bad",
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=5,
            asset_in="A",
            asset_out="B",
            order_amount=10,
            action=StrategyAction.PLACE_SWAP_EXACT_IN,
        )
    with pytest.raises(TypeError, match="action must be a StrategyAction"):
        check_wallet_capability(
            capability=_capability(),
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=5,
            asset_in="A",
            asset_out="B",
            order_amount=10,
            action="bad",
        )
    with pytest.raises(TypeError, match="current_epoch must be an int"):
        check_wallet_capability(
            capability=_capability(),
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=True,
            asset_in="A",
            asset_out="B",
            order_amount=10,
            action=StrategyAction.PLACE_SWAP_EXACT_IN,
        )
    with pytest.raises(ValueError, match="order_amount out of u32 range"):
        check_wallet_capability(
            capability=_capability(),
            signer_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            current_epoch=5,
            asset_in="A",
            asset_out="B",
            order_amount=0x1_0000_0000,
            action=StrategyAction.PLACE_SWAP_EXACT_IN,
        )
