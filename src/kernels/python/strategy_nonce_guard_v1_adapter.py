from __future__ import annotations

from dataclasses import dataclass

_U32_MAX = 0xFFFFFFFF


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class StrategyNonceGuardResult:
    ok: bool
    params_ok: bool
    nonce_fresh: bool
    nonce_sequential: bool
    error: str | None = None


def check_strategy_nonce(
    *,
    intent_nonce: int,
    last_used_nonce: int,
    expected_nonce: int,
) -> StrategyNonceGuardResult:
    intent_nonce = _require_u32("intent_nonce", intent_nonce, minimum=1)
    last_used_nonce = _require_u32("last_used_nonce", last_used_nonce)
    expected_nonce = _require_u32("expected_nonce", expected_nonce, minimum=1)

    params_ok = expected_nonce == last_used_nonce + 1
    nonce_fresh = intent_nonce > last_used_nonce
    nonce_sequential = intent_nonce == expected_nonce

    if not params_ok:
        return StrategyNonceGuardResult(
            ok=False,
            params_ok=False,
            nonce_fresh=nonce_fresh,
            nonce_sequential=nonce_sequential,
            error=f"nonce_expected_invalid:{expected_nonce}!={last_used_nonce + 1}",
        )
    if not nonce_fresh:
        return StrategyNonceGuardResult(
            ok=False,
            params_ok=True,
            nonce_fresh=False,
            nonce_sequential=nonce_sequential,
            error=f"nonce_not_fresh:{intent_nonce}<={last_used_nonce}",
        )
    if not nonce_sequential:
        return StrategyNonceGuardResult(
            ok=False,
            params_ok=True,
            nonce_fresh=True,
            nonce_sequential=False,
            error=f"nonce_expected_mismatch:{intent_nonce}!={expected_nonce}",
        )
    return StrategyNonceGuardResult(
        ok=True,
        params_ok=True,
        nonce_fresh=True,
        nonce_sequential=True,
    )
