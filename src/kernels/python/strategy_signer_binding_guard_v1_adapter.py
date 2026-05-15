from __future__ import annotations

from dataclasses import dataclass

from ...state.canonical import canonical_hex_fixed_allow_0x


@dataclass(frozen=True)
class StrategySignerBindingResult:
    ok: bool
    signer_pubkey_ok: bool
    owner_pubkey_ok: bool
    binding_ok: bool
    signer_pubkey: str | None = None
    owner_pubkey: str | None = None
    error: str | None = None


def _canonical_pubkey(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def check_strategy_signer_binding(
    *,
    signer_pubkey: object,
    owner_pubkey: object,
) -> StrategySignerBindingResult:
    try:
        canonical_signer = _canonical_pubkey("signer_pubkey", signer_pubkey)
        signer_pubkey_ok = True
    except (TypeError, ValueError):
        canonical_signer = None
        signer_pubkey_ok = False
    try:
        canonical_owner = _canonical_pubkey("owner_pubkey", owner_pubkey)
        owner_pubkey_ok = True
    except (TypeError, ValueError):
        canonical_owner = None
        owner_pubkey_ok = False
    binding_ok = (
        signer_pubkey_ok
        and owner_pubkey_ok
        and canonical_signer is not None
        and canonical_owner is not None
        and canonical_signer == canonical_owner
    )
    if not signer_pubkey_ok:
        error = "signer_pubkey_invalid"
    elif not owner_pubkey_ok:
        error = "owner_pubkey_invalid"
    elif not binding_ok:
        error = "signer_pubkey_mismatch"
    else:
        error = None
    return StrategySignerBindingResult(
        ok=bool(binding_ok),
        signer_pubkey_ok=signer_pubkey_ok,
        owner_pubkey_ok=owner_pubkey_ok,
        binding_ok=bool(binding_ok),
        signer_pubkey=canonical_signer,
        owner_pubkey=canonical_owner,
        error=error,
    )
