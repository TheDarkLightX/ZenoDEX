from __future__ import annotations

from dataclasses import dataclass

_U32_MAX = 0xFFFFFFFF


def _require_u32(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0 or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _require_sbf(name: str, value: object) -> bool:
    if value not in (0, 1, False, True):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


@dataclass(frozen=True)
class StrategyWalletOutboundGuardResult:
    ok: bool
    rule_enabled: bool
    sender_scope_match: bool
    amount_ok: bool
    destination_allowed: bool
    session_active: bool
    policy_hash_ok: bool
    context_ok: bool
    error: str | None = None


def check_strategy_wallet_outbound_guard(
    *,
    amount: int,
    max_outbound_amount: int,
    sender_id: int,
    scoped_sender_id: int,
    destination_allowed: int,
    session_active: int,
    policy_hash_ok: int,
    enabled: int,
) -> StrategyWalletOutboundGuardResult:
    amount = _require_u32("amount", amount)
    max_outbound_amount = _require_u32("max_outbound_amount", max_outbound_amount)
    sender_id = _require_u32("sender_id", sender_id)
    scoped_sender_id = _require_u32("scoped_sender_id", scoped_sender_id)
    destination_allowed_b = _require_sbf("destination_allowed", destination_allowed)
    session_active_b = _require_sbf("session_active", session_active)
    policy_hash_ok_b = _require_sbf("policy_hash_ok", policy_hash_ok)
    enabled_b = _require_sbf("enabled", enabled)

    if not enabled_b:
        return StrategyWalletOutboundGuardResult(
            ok=True,
            rule_enabled=False,
            sender_scope_match=sender_id == scoped_sender_id,
            amount_ok=amount <= max_outbound_amount,
            destination_allowed=destination_allowed_b,
            session_active=session_active_b,
            policy_hash_ok=policy_hash_ok_b,
            context_ok=destination_allowed_b and session_active_b and policy_hash_ok_b,
        )

    sender_scope_match = sender_id == scoped_sender_id
    amount_ok = amount <= max_outbound_amount
    context_ok = destination_allowed_b and session_active_b and policy_hash_ok_b

    if not sender_scope_match:
        return StrategyWalletOutboundGuardResult(
            ok=True,
            rule_enabled=True,
            sender_scope_match=False,
            amount_ok=amount_ok,
            destination_allowed=destination_allowed_b,
            session_active=session_active_b,
            policy_hash_ok=policy_hash_ok_b,
            context_ok=context_ok,
        )
    if not amount_ok:
        return StrategyWalletOutboundGuardResult(
            ok=False,
            rule_enabled=True,
            sender_scope_match=True,
            amount_ok=False,
            destination_allowed=destination_allowed_b,
            session_active=session_active_b,
            policy_hash_ok=policy_hash_ok_b,
            context_ok=context_ok,
            error=f"wallet_outbound_amount_exceeded:{amount}>{max_outbound_amount}",
        )
    if not destination_allowed_b:
        return StrategyWalletOutboundGuardResult(
            ok=False,
            rule_enabled=True,
            sender_scope_match=True,
            amount_ok=True,
            destination_allowed=False,
            session_active=session_active_b,
            policy_hash_ok=policy_hash_ok_b,
            context_ok=False,
            error="wallet_outbound_destination_blocked",
        )
    if not session_active_b:
        return StrategyWalletOutboundGuardResult(
            ok=False,
            rule_enabled=True,
            sender_scope_match=True,
            amount_ok=True,
            destination_allowed=True,
            session_active=False,
            policy_hash_ok=policy_hash_ok_b,
            context_ok=False,
            error="wallet_outbound_session_inactive",
        )
    if not policy_hash_ok_b:
        return StrategyWalletOutboundGuardResult(
            ok=False,
            rule_enabled=True,
            sender_scope_match=True,
            amount_ok=True,
            destination_allowed=True,
            session_active=True,
            policy_hash_ok=False,
            context_ok=False,
            error="wallet_outbound_policy_hash_mismatch",
        )
    return StrategyWalletOutboundGuardResult(
        ok=True,
        rule_enabled=True,
        sender_scope_match=True,
        amount_ok=True,
        destination_allowed=True,
        session_active=True,
        policy_hash_ok=True,
        context_ok=True,
    )
