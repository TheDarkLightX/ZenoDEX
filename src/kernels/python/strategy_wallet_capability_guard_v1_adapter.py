from __future__ import annotations

from dataclasses import dataclass

from ...agents.strategy_ir import StrategyAction
from ...integration.autotrader_signals import AutoTraderWalletCapability

_U32_MAX = 0xFFFFFFFF


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class StrategyWalletCapabilityResult:
    ok: bool
    enabled_ok: bool
    signer_ok: bool
    asset_scope_ok: bool
    action_scope_ok: bool
    chain_scope_ok: bool
    within_window_ok: bool
    notional_ok: bool
    error: str | None = None


def check_wallet_capability(
    *,
    capability: AutoTraderWalletCapability,
    signer_pubkey: str,
    chain_id: str,
    current_epoch: int,
    asset_in: str,
    asset_out: str,
    order_amount: int,
    action: StrategyAction,
) -> StrategyWalletCapabilityResult:
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    if not isinstance(action, StrategyAction):
        raise TypeError("action must be a StrategyAction")
    current_epoch = _require_u32("current_epoch", current_epoch)
    order_amount = _require_u32("order_amount", order_amount, minimum=1)

    enabled_ok = bool(capability.enabled)
    signer_ok = signer_pubkey == capability.owner_pubkey
    asset_scope_ok = asset_in in capability.allowed_assets and asset_out in capability.allowed_assets
    action_scope_ok = action in capability.allowed_actions
    chain_scope_ok = chain_id == capability.chain_id
    within_window_ok = capability.valid_from_epoch <= current_epoch <= capability.valid_until_epoch
    notional_ok = order_amount <= capability.notional_remaining

    if not enabled_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=False,
            signer_ok=signer_ok,
            asset_scope_ok=asset_scope_ok,
            action_scope_ok=action_scope_ok,
            chain_scope_ok=chain_scope_ok,
            within_window_ok=within_window_ok,
            notional_ok=notional_ok,
            error="wallet_capability_disabled",
        )
    if not signer_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=False,
            asset_scope_ok=asset_scope_ok,
            action_scope_ok=action_scope_ok,
            chain_scope_ok=chain_scope_ok,
            within_window_ok=within_window_ok,
            notional_ok=notional_ok,
            error="wallet_capability_signer_mismatch",
        )
    if not chain_scope_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=True,
            asset_scope_ok=asset_scope_ok,
            action_scope_ok=action_scope_ok,
            chain_scope_ok=False,
            within_window_ok=within_window_ok,
            notional_ok=notional_ok,
            error=f"wallet_capability_chain_mismatch:{chain_id}!={capability.chain_id}",
        )
    if not asset_scope_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=True,
            asset_scope_ok=False,
            action_scope_ok=action_scope_ok,
            chain_scope_ok=True,
            within_window_ok=within_window_ok,
            notional_ok=notional_ok,
            error=f"wallet_capability_asset_scope_violation:{asset_in}/{asset_out}",
        )
    if not action_scope_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=True,
            asset_scope_ok=True,
            action_scope_ok=False,
            chain_scope_ok=True,
            within_window_ok=within_window_ok,
            notional_ok=notional_ok,
            error=f"wallet_capability_action_not_allowed:{action.value}",
        )
    if not within_window_ok:
        if current_epoch < capability.valid_from_epoch:
            error = f"wallet_capability_window_not_open:{current_epoch}<{capability.valid_from_epoch}"
        else:
            error = f"wallet_capability_expired:{current_epoch}>{capability.valid_until_epoch}"
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=True,
            asset_scope_ok=True,
            action_scope_ok=True,
            chain_scope_ok=True,
            within_window_ok=False,
            notional_ok=notional_ok,
            error=error,
        )
    if not notional_ok:
        return StrategyWalletCapabilityResult(
            ok=False,
            enabled_ok=True,
            signer_ok=True,
            asset_scope_ok=True,
            action_scope_ok=True,
            chain_scope_ok=True,
            within_window_ok=True,
            notional_ok=False,
            error=f"wallet_capability_notional_exceeded:{order_amount}>{capability.notional_remaining}",
        )
    return StrategyWalletCapabilityResult(
        ok=True,
        enabled_ok=True,
        signer_ok=True,
        asset_scope_ok=True,
        action_scope_ok=True,
        chain_scope_ok=True,
        within_window_ok=True,
        notional_ok=True,
    )
