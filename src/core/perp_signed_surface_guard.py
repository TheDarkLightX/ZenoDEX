from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


ACTION_INVALID = 0
ACTION_INIT_MARKET_2P = 1
ACTION_INIT_MARKET_3P = 2
ACTION_SET_POSITION_PAIR = 3
ACTION_SET_POSITION_TRIPLET = 4
ACTION_PUBLISH_CLEARING_PRICE = 5

REJECT_OK = "Ok"
REJECT_INVALID_ACTION = "InvalidAction"
REJECT_INVALID_VERSION = "InvalidVersion"
REJECT_UNKNOWN_FIELDS = "UnknownFields"
REJECT_DISTINCT_ACCOUNTS_INVALID = "DistinctAccountsInvalid"
REJECT_MARKET_ACCOUNTS_MISMATCH = "MarketAccountsMismatch"
REJECT_NET_POSITION_INVALID = "NetPositionInvalid"
REJECT_IDLE_LEG_INVALID = "IdleLegInvalid"
REJECT_PRICE_INVALID = "PriceInvalid"


@dataclass(frozen=True)
class PerpSignedSurfaceGuardOutcome:
    action_kind: int
    action_known: bool
    version_ok: bool
    unknown_fields_ok: bool
    distinct_accounts_ok: bool
    market_accounts_match_ok: bool
    net_zero_ok: bool
    idle_leg_ok: bool
    positive_price_ok: bool
    signed_surface_ok: bool
    reject_code: str
    checks: Mapping[str, bool | int]


def _require_flag(value: Any, *, name: str) -> bool:
    if isinstance(value, bool):
        return bool(value)
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a bool or 0/1 int")
    if value not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return bool(value)


def _require_action_kind(value: Any, *, name: str = "action_kind") -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < ACTION_INVALID or value > ACTION_PUBLISH_CLEARING_PRICE:
        raise ValueError(f"{name} out of range")
    return int(value)


def evaluate_perp_signed_surface_guard(
    *,
    action_kind: Any,
    version_ok: Any,
    unknown_fields_ok: Any,
    distinct_accounts_ok: Any,
    market_accounts_match_ok: Any,
    net_zero_ok: Any,
    idle_leg_ok: Any,
    positive_price_ok: Any,
) -> PerpSignedSurfaceGuardOutcome:
    action = _require_action_kind(action_kind)
    version = _require_flag(version_ok, name="version_ok")
    unknown_fields = _require_flag(unknown_fields_ok, name="unknown_fields_ok")
    distinct_accounts = _require_flag(distinct_accounts_ok, name="distinct_accounts_ok")
    market_accounts_match = _require_flag(market_accounts_match_ok, name="market_accounts_match_ok")
    net_zero = _require_flag(net_zero_ok, name="net_zero_ok")
    idle_leg = _require_flag(idle_leg_ok, name="idle_leg_ok")
    positive_price = _require_flag(positive_price_ok, name="positive_price_ok")

    action_known = bool(action != ACTION_INVALID)
    checks = {
        "action_kind": action,
        "version_ok": version,
        "unknown_fields_ok": unknown_fields,
        "distinct_accounts_ok": distinct_accounts,
        "market_accounts_match_ok": market_accounts_match,
        "net_zero_ok": net_zero,
        "idle_leg_ok": idle_leg,
        "positive_price_ok": positive_price,
    }

    if not action_known:
        reject_code = REJECT_INVALID_ACTION
    elif not version:
        reject_code = REJECT_INVALID_VERSION
    elif not unknown_fields:
        reject_code = REJECT_UNKNOWN_FIELDS
    elif not distinct_accounts:
        reject_code = REJECT_DISTINCT_ACCOUNTS_INVALID
    elif not market_accounts_match:
        reject_code = REJECT_MARKET_ACCOUNTS_MISMATCH
    elif not net_zero:
        reject_code = REJECT_NET_POSITION_INVALID
    elif not idle_leg:
        reject_code = REJECT_IDLE_LEG_INVALID
    elif not positive_price:
        reject_code = REJECT_PRICE_INVALID
    else:
        reject_code = REJECT_OK

    return PerpSignedSurfaceGuardOutcome(
        action_kind=action,
        action_known=action_known,
        version_ok=version,
        unknown_fields_ok=unknown_fields,
        distinct_accounts_ok=distinct_accounts,
        market_accounts_match_ok=market_accounts_match,
        net_zero_ok=net_zero,
        idle_leg_ok=idle_leg,
        positive_price_ok=positive_price,
        signed_surface_ok=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        checks=checks,
    )


def perp_signed_surface_guard_error(outcome: PerpSignedSurfaceGuardOutcome, *, action: str) -> str | None:
    if outcome.reject_code == REJECT_INVALID_ACTION:
        return "unsupported signed perps action"
    if outcome.reject_code == REJECT_INVALID_VERSION:
        if action == "init_market_2p":
            return "init_market_2p requires perps.version=0.2 or 1.0"
        if action == "init_market_3p":
            return "init_market_3p requires perps.version=1.1"
        if action == "set_position_pair":
            return "set_position_pair requires perps.version=0.2 or 1.0"
        if action == "set_position_triplet":
            return "set_position_triplet requires perps.version=1.1"
        if action == "publish_clearing_price":
            return "publish_clearing_price requires a clearinghouse perps.version"
        return "invalid perps version for signed action"
    if outcome.reject_code == REJECT_UNKNOWN_FIELDS:
        return f"{action} has unknown fields"
    if outcome.reject_code == REJECT_DISTINCT_ACCOUNTS_INVALID:
        return "accounts must be distinct"
    if outcome.reject_code == REJECT_MARKET_ACCOUNTS_MISMATCH:
        return "accounts do not match this market"
    if outcome.reject_code == REJECT_NET_POSITION_INVALID:
        if action == "set_position_pair":
            return "clearinghouse_2p requires net position == 0"
        return "clearinghouse_3p requires net position == 0"
    if outcome.reject_code == REJECT_IDLE_LEG_INVALID:
        return "clearinghouse_3p requires at least one flat position"
    if outcome.reject_code == REJECT_PRICE_INVALID:
        return "publish_clearing_price requires price_e8 > 0"
    return None
