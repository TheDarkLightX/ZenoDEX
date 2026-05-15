from __future__ import annotations

from dataclasses import dataclass

from ...integration.autotrader_signals import AutoTraderSessionState, AutoTraderWalletCapability

_U32_MAX = 0xFFFFFFFF


def _require_u32(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0 or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _require_chain_id(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("chain_id must be a string")
    text = value.strip()
    if not text:
        raise ValueError("chain_id must be non-empty")
    return text


@dataclass(frozen=True)
class StrategySessionStateGuardResult:
    ok: bool
    enabled_ok: bool
    session_binding_ok: bool
    owner_binding_ok: bool
    chain_binding_ok: bool
    revocation_ok: bool
    error: str | None = None


def check_strategy_session_state(
    *,
    session_state: AutoTraderSessionState,
    capability: AutoTraderWalletCapability,
    chain_id: str,
    current_epoch: int,
) -> StrategySessionStateGuardResult:
    if not isinstance(session_state, AutoTraderSessionState):
        raise TypeError("session_state must be an AutoTraderSessionState")
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    chain_id = _require_chain_id(chain_id)
    current_epoch = _require_u32("current_epoch", current_epoch)

    enabled_ok = bool(session_state.enabled)
    session_binding_ok = session_state.session_id == capability.session_id
    owner_binding_ok = session_state.owner_pubkey == capability.owner_pubkey
    chain_binding_ok = session_state.chain_id == capability.chain_id == chain_id
    revocation_ok = (
        session_state.revoked_at_epoch is None
        or current_epoch < session_state.revoked_at_epoch
    )

    if not enabled_ok:
        error = "session_state_disabled"
    elif not session_binding_ok:
        error = (
            "session_state_session_id_mismatch:"
            f"{session_state.session_id}!={capability.session_id}"
        )
    elif not owner_binding_ok:
        error = "session_state_owner_mismatch"
    elif not chain_binding_ok:
        error = f"session_state_chain_mismatch:{session_state.chain_id}!={chain_id}"
    elif not revocation_ok:
        error = f"session_state_revoked:{current_epoch}>={session_state.revoked_at_epoch}"
    else:
        error = None

    return StrategySessionStateGuardResult(
        ok=error is None,
        enabled_ok=enabled_ok,
        session_binding_ok=session_binding_ok,
        owner_binding_ok=owner_binding_ok,
        chain_binding_ok=chain_binding_ok,
        revocation_ok=revocation_ok,
        error=error,
    )
