from __future__ import annotations

from dataclasses import dataclass

from ...agents.strategy_ir import StrategyIR
from ...integration.autotrader_signals import AutoTraderWalletCapability


def _require_chain_id(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("chain_id must be a string")
    text = value.strip()
    if not text:
        raise ValueError("chain_id must be non-empty")
    return text


@dataclass(frozen=True)
class StrategySessionCapabilityBindingResult:
    ok: bool
    session_present_ok: bool
    owner_binding_ok: bool
    chain_binding_ok: bool
    asset_scope_ok: bool
    action_scope_ok: bool
    strategy_window_binding_ok: bool
    error: str | None = None


def check_strategy_session_capability_binding(
    *,
    strategy: StrategyIR,
    capability: AutoTraderWalletCapability,
    chain_id: str,
) -> StrategySessionCapabilityBindingResult:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    chain_id = _require_chain_id(chain_id)

    session_present_ok = isinstance(capability.session_id, str) and capability.session_id.strip() != ""
    owner_binding_ok = capability.owner_pubkey == strategy.owner_pubkey
    chain_binding_ok = capability.chain_id == chain_id
    asset_scope_ok = set(capability.allowed_assets).issubset(set(strategy.asset_universe))
    action_scope_ok = set(capability.allowed_actions).issubset(set(strategy.allowed_actions))
    strategy_window_binding_ok = (
        strategy.strategy_window.valid_from_epoch
        <= capability.valid_from_epoch
        <= capability.valid_until_epoch
        <= strategy.strategy_window.valid_until_epoch
    )

    if not session_present_ok:
        error = "session_capability_missing_session_id"
    elif not owner_binding_ok:
        error = "session_capability_owner_mismatch"
    elif not chain_binding_ok:
        error = f"session_capability_chain_mismatch:{capability.chain_id}!={chain_id}"
    elif not asset_scope_ok:
        error = "session_capability_asset_scope_exceeds_strategy"
    elif not action_scope_ok:
        error = "session_capability_action_scope_exceeds_strategy"
    elif not strategy_window_binding_ok:
        error = "session_capability_window_exceeds_strategy"
    else:
        error = None

    return StrategySessionCapabilityBindingResult(
        ok=error is None,
        session_present_ok=session_present_ok,
        owner_binding_ok=owner_binding_ok,
        chain_binding_ok=chain_binding_ok,
        asset_scope_ok=asset_scope_ok,
        action_scope_ok=action_scope_ok,
        strategy_window_binding_ok=strategy_window_binding_ok,
        error=error,
    )
