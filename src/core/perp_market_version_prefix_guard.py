from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REJECT_OK = "Ok"
REJECT_INVALID_VERSION = "InvalidVersion"
REJECT_CH2P_PREFIX_MISMATCH = "Ch2pPrefixMismatch"
REJECT_CH3P_PREFIX_MISMATCH = "Ch3pPrefixMismatch"
REJECT_ISOLATED_PREFIX_CONFLICT = "IsolatedPrefixConflict"


@dataclass(frozen=True)
class PerpMarketVersionPrefixGuardOutcome:
    version_ok: bool
    isolated_version: bool
    clearinghouse_2p_version: bool
    clearinghouse_3p_version: bool
    market_prefix_ok: bool
    admission_ok: bool
    reject_code: str
    checks: Mapping[str, bool]


@dataclass(frozen=True)
class _VersionPrefixFlags:
    version_is_v0_1: bool
    version_is_ch2p: bool
    version_is_ch3p: bool
    market_has_ch2p_prefix: bool
    market_has_ch3p_prefix: bool


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _prefix_checks(flags: _VersionPrefixFlags) -> Mapping[str, bool]:
    return {
        "version_is_v0_1": flags.version_is_v0_1,
        "version_is_ch2p": flags.version_is_ch2p,
        "version_is_ch3p": flags.version_is_ch3p,
        "market_has_ch2p_prefix": flags.market_has_ch2p_prefix,
        "market_has_ch3p_prefix": flags.market_has_ch3p_prefix,
    }


def _prefix_reject_code(flags: _VersionPrefixFlags) -> str:
    version_ok = bool(flags.version_is_v0_1 or flags.version_is_ch2p or flags.version_is_ch3p)
    isolated_version = bool(flags.version_is_v0_1 and not flags.version_is_ch2p and not flags.version_is_ch3p)
    if not version_ok:
        return REJECT_INVALID_VERSION
    if flags.version_is_ch2p and not flags.market_has_ch2p_prefix:
        return REJECT_CH2P_PREFIX_MISMATCH
    if flags.version_is_ch3p and not flags.market_has_ch3p_prefix:
        return REJECT_CH3P_PREFIX_MISMATCH
    if isolated_version and (flags.market_has_ch2p_prefix or flags.market_has_ch3p_prefix):
        return REJECT_ISOLATED_PREFIX_CONFLICT
    return REJECT_OK


def evaluate_perp_market_version_prefix_guard(
    *,
    version_is_v0_1: Any,
    version_is_ch2p: Any,
    version_is_ch3p: Any,
    market_has_ch2p_prefix: Any,
    market_has_ch3p_prefix: Any,
) -> PerpMarketVersionPrefixGuardOutcome:
    flags = _VersionPrefixFlags(
        version_is_v0_1=_require_bool(version_is_v0_1, name="version_is_v0_1"),
        version_is_ch2p=_require_bool(version_is_ch2p, name="version_is_ch2p"),
        version_is_ch3p=_require_bool(version_is_ch3p, name="version_is_ch3p"),
        market_has_ch2p_prefix=_require_bool(market_has_ch2p_prefix, name="market_has_ch2p_prefix"),
        market_has_ch3p_prefix=_require_bool(market_has_ch3p_prefix, name="market_has_ch3p_prefix"),
    )
    version_ok = bool(flags.version_is_v0_1 or flags.version_is_ch2p or flags.version_is_ch3p)
    isolated_version = bool(flags.version_is_v0_1 and not flags.version_is_ch2p and not flags.version_is_ch3p)
    market_prefix_ok = bool(
        (flags.version_is_ch2p and flags.market_has_ch2p_prefix)
        or (flags.version_is_ch3p and flags.market_has_ch3p_prefix)
        or (
            isolated_version
            and not flags.market_has_ch2p_prefix
            and not flags.market_has_ch3p_prefix
        )
    )
    reject_code = _prefix_reject_code(flags)
    return PerpMarketVersionPrefixGuardOutcome(
        version_ok=version_ok,
        isolated_version=isolated_version,
        clearinghouse_2p_version=flags.version_is_ch2p,
        clearinghouse_3p_version=flags.version_is_ch3p,
        market_prefix_ok=market_prefix_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=_prefix_checks(flags),
    )
