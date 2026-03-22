from __future__ import annotations

from dataclasses import dataclass

ADVISORY_EXTERNAL_SOURCE_CODE = 1
ATTESTED_EXTERNAL_SOURCE_CODE = 2

ADVISORY_TRUST_TIER_CODE = 0
ATTESTED_TRUST_TIER_CODE = 1
VERIFIED_TRUST_TIER_CODE = 2


def _require_u8(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0 or out > 0xFF:
        raise ValueError(f"{name} out of u8 range: {out}")
    return out


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class StrategyExternalSignalContractResult:
    ok: bool
    source_kind_ok: bool
    trust_tier_ok: bool
    advisory_external_ok: bool
    attested_external_ok: bool
    error: str | None = None


def _resolve_error(result: StrategyExternalSignalContractResult) -> str | None:
    checks = (
        ("source_kind_unsupported", result.source_kind_ok),
        ("trust_tier_invalid", result.trust_tier_ok),
        ("advisory_external_invalid", result.advisory_external_ok),
        ("attested_external_invalid", result.attested_external_ok),
    )
    for error, ok in checks:
        if not ok:
            return error
    return None


def check_strategy_external_signal_contract(
    *,
    source_kind_code: int,
    trust_tier_code: int,
    freshness_ok: bool,
    auth_ok: bool,
    advisory_only: bool,
) -> StrategyExternalSignalContractResult:
    source_kind_code = _require_u8("source_kind_code", source_kind_code)
    trust_tier_code = _require_u8("trust_tier_code", trust_tier_code)
    freshness_ok = _require_bool("freshness_ok", freshness_ok)
    auth_ok = _require_bool("auth_ok", auth_ok)
    advisory_only = _require_bool("advisory_only", advisory_only)

    source_kind_ok = source_kind_code in (
        ADVISORY_EXTERNAL_SOURCE_CODE,
        ATTESTED_EXTERNAL_SOURCE_CODE,
    )
    trust_tier_ok = trust_tier_code in (
        ADVISORY_TRUST_TIER_CODE,
        ATTESTED_TRUST_TIER_CODE,
        VERIFIED_TRUST_TIER_CODE,
    )
    advisory_external_ok = True
    attested_external_ok = True
    if source_kind_code == ADVISORY_EXTERNAL_SOURCE_CODE:
        advisory_external_ok = advisory_only and trust_tier_code == ADVISORY_TRUST_TIER_CODE
    elif source_kind_code == ATTESTED_EXTERNAL_SOURCE_CODE:
        attested_external_ok = trust_tier_code in (
            ATTESTED_TRUST_TIER_CODE,
            VERIFIED_TRUST_TIER_CODE,
        ) and (advisory_only or (auth_ok and freshness_ok))

    ok = source_kind_ok and trust_tier_ok and advisory_external_ok and attested_external_ok
    result = StrategyExternalSignalContractResult(
        ok=ok,
        source_kind_ok=source_kind_ok,
        trust_tier_ok=trust_tier_ok,
        advisory_external_ok=advisory_external_ok,
        attested_external_ok=attested_external_ok,
    )
    return StrategyExternalSignalContractResult(
        ok=result.ok,
        source_kind_ok=result.source_kind_ok,
        trust_tier_ok=result.trust_tier_ok,
        advisory_external_ok=result.advisory_external_ok,
        attested_external_ok=result.attested_external_ok,
        error=_resolve_error(result),
    )
