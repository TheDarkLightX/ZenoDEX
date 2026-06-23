from __future__ import annotations

from dataclasses import dataclass

ADVISORY_TRUST_TIER_CODE = 0
ATTESTED_TRUST_TIER_CODE = 1
VERIFIED_TRUST_TIER_CODE = 2
PROTOCOL_TRUST_TIER_CODE = 3


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
class StrategyExternalSignalSourceRegistryGuardResult:
    ok: bool
    registry_entry_found: bool
    registry_enabled_ok: bool
    source_kind_matches: bool
    trust_tier_allowed: bool
    advisory_mode_allowed: bool
    auth_requirement_ok: bool
    freshness_requirement_ok: bool
    error: str | None = None


def _resolve_error(result: StrategyExternalSignalSourceRegistryGuardResult) -> str | None:
    checks = (
        ("source_registry_entry_missing", result.registry_entry_found),
        ("source_registry_entry_disabled", result.registry_enabled_ok),
        ("source_registry_kind_mismatch", result.source_kind_matches),
        ("source_registry_trust_tier_rejected", result.trust_tier_allowed),
        ("source_registry_advisory_mode_required", result.advisory_mode_allowed),
        ("source_registry_auth_required", result.auth_requirement_ok),
        ("source_registry_freshness_required", result.freshness_requirement_ok),
    )
    for error, ok in checks:
        if not ok:
            return error
    return None


def _trust_tier_allowed(
    *,
    observed_trust_tier_code: int,
    allow_advisory: bool,
    allow_attested: bool,
    allow_verified: bool,
    allow_protocol: bool,
) -> bool:
    if observed_trust_tier_code == ADVISORY_TRUST_TIER_CODE:
        return allow_advisory
    if observed_trust_tier_code == ATTESTED_TRUST_TIER_CODE:
        return allow_attested
    if observed_trust_tier_code == VERIFIED_TRUST_TIER_CODE:
        return allow_verified
    if observed_trust_tier_code == PROTOCOL_TRUST_TIER_CODE:
        return allow_protocol
    return False


def check_strategy_external_signal_source_registry_guard(
    *,
    registry_entry_present: bool,
    registry_entry_enabled: bool,
    observed_source_kind_code: int,
    observed_trust_tier_code: int,
    advisory_only: bool,
    auth_ok: bool,
    freshness_ok: bool,
    registered_source_kind_code: int,
    allow_advisory: bool,
    allow_attested: bool,
    allow_verified: bool,
    allow_protocol: bool,
    require_advisory_only: bool,
    require_auth: bool,
    require_freshness: bool,
) -> StrategyExternalSignalSourceRegistryGuardResult:
    registry_entry_present = _require_bool("registry_entry_present", registry_entry_present)
    registry_entry_enabled = _require_bool("registry_entry_enabled", registry_entry_enabled)
    observed_source_kind_code = _require_u8("observed_source_kind_code", observed_source_kind_code)
    observed_trust_tier_code = _require_u8("observed_trust_tier_code", observed_trust_tier_code)
    advisory_only = _require_bool("advisory_only", advisory_only)
    auth_ok = _require_bool("auth_ok", auth_ok)
    freshness_ok = _require_bool("freshness_ok", freshness_ok)
    registered_source_kind_code = _require_u8(
        "registered_source_kind_code",
        registered_source_kind_code,
    )
    allow_advisory = _require_bool("allow_advisory", allow_advisory)
    allow_attested = _require_bool("allow_attested", allow_attested)
    allow_verified = _require_bool("allow_verified", allow_verified)
    allow_protocol = _require_bool("allow_protocol", allow_protocol)
    require_advisory_only = _require_bool("require_advisory_only", require_advisory_only)
    require_auth = _require_bool("require_auth", require_auth)
    require_freshness = _require_bool("require_freshness", require_freshness)

    registry_entry_found = bool(registry_entry_present)
    registry_enabled_ok = bool(registry_entry_present and registry_entry_enabled)
    source_kind_matches = bool(
        registry_entry_present and observed_source_kind_code == registered_source_kind_code
    )
    trust_tier_allowed = bool(
        registry_entry_present
        and _trust_tier_allowed(
            observed_trust_tier_code=observed_trust_tier_code,
            allow_advisory=allow_advisory,
            allow_attested=allow_attested,
            allow_verified=allow_verified,
            allow_protocol=allow_protocol,
        )
    )
    advisory_mode_allowed = (not require_advisory_only) or advisory_only
    auth_requirement_ok = (not require_auth) or auth_ok
    freshness_requirement_ok = (not require_freshness) or freshness_ok

    ok = (
        registry_entry_found
        and registry_enabled_ok
        and source_kind_matches
        and trust_tier_allowed
        and advisory_mode_allowed
        and auth_requirement_ok
        and freshness_requirement_ok
    )
    result = StrategyExternalSignalSourceRegistryGuardResult(
        ok=ok,
        registry_entry_found=registry_entry_found,
        registry_enabled_ok=registry_enabled_ok,
        source_kind_matches=source_kind_matches,
        trust_tier_allowed=trust_tier_allowed,
        advisory_mode_allowed=advisory_mode_allowed,
        auth_requirement_ok=auth_requirement_ok,
        freshness_requirement_ok=freshness_requirement_ok,
    )
    return StrategyExternalSignalSourceRegistryGuardResult(
        ok=result.ok,
        registry_entry_found=result.registry_entry_found,
        registry_enabled_ok=result.registry_enabled_ok,
        source_kind_matches=result.source_kind_matches,
        trust_tier_allowed=result.trust_tier_allowed,
        advisory_mode_allowed=result.advisory_mode_allowed,
        auth_requirement_ok=result.auth_requirement_ok,
        freshness_requirement_ok=result.freshness_requirement_ok,
        error=_resolve_error(result),
    )


__all__ = [
    "ADVISORY_TRUST_TIER_CODE",
    "ATTESTED_TRUST_TIER_CODE",
    "PROTOCOL_TRUST_TIER_CODE",
    "StrategyExternalSignalSourceRegistryGuardResult",
    "VERIFIED_TRUST_TIER_CODE",
    "check_strategy_external_signal_source_registry_guard",
]
