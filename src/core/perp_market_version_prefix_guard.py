from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping


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


def evaluate_perp_market_version_prefix_guard(
    *,
    version_is_v0_1: bool,
    version_is_ch2p: bool,
    version_is_ch3p: bool,
    market_has_ch2p_prefix: bool,
    market_has_ch3p_prefix: bool,
) -> PerpMarketVersionPrefixGuardOutcome:
    checks = {
        "version_is_v0_1": bool(version_is_v0_1),
        "version_is_ch2p": bool(version_is_ch2p),
        "version_is_ch3p": bool(version_is_ch3p),
        "market_has_ch2p_prefix": bool(market_has_ch2p_prefix),
        "market_has_ch3p_prefix": bool(market_has_ch3p_prefix),
    }
    version_ok = bool(checks["version_is_v0_1"] or checks["version_is_ch2p"] or checks["version_is_ch3p"])
    isolated_version = bool(checks["version_is_v0_1"] and not checks["version_is_ch2p"] and not checks["version_is_ch3p"])
    market_prefix_ok = bool(
        (checks["version_is_ch2p"] and checks["market_has_ch2p_prefix"])
        or (checks["version_is_ch3p"] and checks["market_has_ch3p_prefix"])
        or (
            isolated_version
            and not checks["market_has_ch2p_prefix"]
            and not checks["market_has_ch3p_prefix"]
        )
    )
    if not version_ok:
        reject_code = REJECT_INVALID_VERSION
    elif checks["version_is_ch2p"] and not checks["market_has_ch2p_prefix"]:
        reject_code = REJECT_CH2P_PREFIX_MISMATCH
    elif checks["version_is_ch3p"] and not checks["market_has_ch3p_prefix"]:
        reject_code = REJECT_CH3P_PREFIX_MISMATCH
    elif isolated_version and (checks["market_has_ch2p_prefix"] or checks["market_has_ch3p_prefix"]):
        reject_code = REJECT_ISOLATED_PREFIX_CONFLICT
    else:
        reject_code = REJECT_OK
    return PerpMarketVersionPrefixGuardOutcome(
        version_ok=version_ok,
        isolated_version=isolated_version,
        clearinghouse_2p_version=bool(checks["version_is_ch2p"]),
        clearinghouse_3p_version=bool(checks["version_is_ch3p"]),
        market_prefix_ok=market_prefix_ok,
        admission_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=checks,
    )
