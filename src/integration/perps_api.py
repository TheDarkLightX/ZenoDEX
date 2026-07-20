"""REST API handlers for perpetuals endpoints (DEMO / DEVELOPMENT ONLY).

Pure stdlib module -- no third-party dependencies.
Imported lazily by ``api_server.py`` when a ``/api/perps/`` path is hit.

All handlers are pure functions that take state + request body and return
``(status_code, response_dict)`` tuples; the caller serializes to JSON.

Wire into ``api_server.py`` via the ``handle_perps_request()`` dispatcher.

Security note:
    This module is a **demo/development** API operating on in-memory mock state.
    POST handlers accept a ``pubkey`` field but do NOT cryptographically verify
    the caller's identity (no BLS signature check). Any caller can mutate any
    account. This is intentional for local development and UI testing.

    The **production** transaction path uses ``src/integration/perp_engine.py``
    (``apply_perp_ops``), which enforces per-account BLS signature verification,
    nonce replay protection, and operator authorization.
"""

from __future__ import annotations

import json
import re
import threading
import time
from typing import Any, Dict, List, Optional, Tuple

from ..core.domain_limits import PERP_PARAM_AMOUNT_MAX, PERP_POSITION_MAX
from ..core.perp_v2 import (
    Action,
    ActionParams,
    EpochPhase,
    PerpState,
    step,
)
from ..core.perp_v2.math import (
    BPS_SCALE,
    liquidation_price_e8,
    maint_margin_req,
    notional_quote,
    pnl_quote,
)
from ..core.perps import (
    PERPS_STATE_VERSION,
    PerpAccountState,
    PerpAnyMarketState,
    PerpClearinghouse2pMarketState,
    PerpMarketState,
    PerpsState,
)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

MAX_POST_BODY: int = 65_536  # 64 KiB
MAX_DEMO_ACCOUNTS_PER_MARKET: int = 2_000

_HEX_RE = re.compile(r"^[0-9a-fA-F]+$")
_MARKET_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]{0,63}$")
_PUBKEY_TOKEN_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$")

# ---------------------------------------------------------------------------
# Demo state -- thread-safe via a global lock
# ---------------------------------------------------------------------------

_lock = threading.Lock()

_DEMO_GLOBAL_BTC: Dict[str, bool | int | str] = {
    "now_epoch": 1042,
    "epoch_phase": "Open",
    "breaker_active": False,
    "breaker_last_trigger_epoch": 0,
    "clearing_price_seen": True,
    "clearing_price_epoch": 1041,
    "clearing_price_e8": 4_198_500_000_000,
    "oracle_seen": True,
    "oracle_last_update_epoch": 1041,
    "index_price_e8": 4_200_000_000_000,
    "max_oracle_staleness_epochs": 100,
    "max_oracle_move_bps": 500,
    "initial_margin_bps": 1000,
    "maintenance_margin_bps": 500,
    "depeg_buffer_bps": 100,
    "liquidation_penalty_bps": 50,
    "max_position_abs": PERP_POSITION_MAX,
    "fee_pool_quote": 1_200_000_000,
    "funding_rate_bps": 0,
    "funding_cap_bps": 100,
    "insurance_balance": 5_000_000_000,
    "initial_insurance": 4_000_000_000,
    "fee_income": 1_200_000_000,
    "claims_paid": 200_000_000,
    "min_notional_for_bounty": 100_000_000,
}

_DEMO_GLOBAL_ETH: Dict[str, bool | int | str] = {
    "now_epoch": 1042,
    "epoch_phase": "Open",
    "breaker_active": False,
    "breaker_last_trigger_epoch": 0,
    "clearing_price_seen": True,
    "clearing_price_epoch": 1041,
    "clearing_price_e8": 319_800_000_000,
    "oracle_seen": True,
    "oracle_last_update_epoch": 1041,
    "index_price_e8": 320_000_000_000,
    "max_oracle_staleness_epochs": 100,
    "max_oracle_move_bps": 500,
    "initial_margin_bps": 1000,
    "maintenance_margin_bps": 500,
    "depeg_buffer_bps": 100,
    "liquidation_penalty_bps": 50,
    "max_position_abs": PERP_POSITION_MAX,
    "fee_pool_quote": 600_000_000,
    "funding_rate_bps": 0,
    "funding_cap_bps": 100,
    "insurance_balance": 2_000_000_000,
    "initial_insurance": 1_500_000_000,
    "fee_income": 600_000_000,
    "claims_paid": 100_000_000,
    "min_notional_for_bounty": 100_000_000,
}

_DEMO_GLOBAL_TAU: Dict[str, bool | int | str] = {
    "now_epoch": 1042,
    "epoch_phase": "Open",
    "breaker_active": False,
    "breaker_last_trigger_epoch": 0,
    "clearing_price_seen": True,
    "clearing_price_epoch": 1041,
    "clearing_price_e8": 49_900_000,
    "oracle_seen": True,
    "oracle_last_update_epoch": 1041,
    "index_price_e8": 50_000_000,
    "max_oracle_staleness_epochs": 100,
    "max_oracle_move_bps": 500,
    "initial_margin_bps": 2000,
    "maintenance_margin_bps": 1000,
    "depeg_buffer_bps": 200,
    "liquidation_penalty_bps": 50,
    "max_position_abs": PERP_POSITION_MAX,
    "fee_pool_quote": 150_000_000,
    "funding_rate_bps": 0,
    "funding_cap_bps": 100,
    "insurance_balance": 500_000_000,
    "initial_insurance": 400_000_000,
    "fee_income": 150_000_000,
    "claims_paid": 50_000_000,
    "min_notional_for_bounty": 100_000_000,
}


def _make_demo_perps() -> PerpsState:
    return PerpsState(
        version=PERPS_STATE_VERSION,
        markets={
            "BTC-USD": PerpMarketState(
                quote_asset="USD",
                global_state=dict(_DEMO_GLOBAL_BTC),
                accounts={},
            ),
            "ETH-USD": PerpMarketState(
                quote_asset="USD",
                global_state=dict(_DEMO_GLOBAL_ETH),
                accounts={},
            ),
            "TAU-USD": PerpMarketState(
                quote_asset="USD",
                global_state=dict(_DEMO_GLOBAL_TAU),
                accounts={},
            ),
        },
    )


# Module-level mutable demo state -- protected by _lock.
# This is the imperative shell boundary. All handlers below are pure over
# explicit ``(perps, history)`` inputs and return updated copies.
_demo_perps: PerpsState = _make_demo_perps()
_history: List[Dict[str, Any]] = []
_MAX_HISTORY: int = 200


def _history_with_entry(
    history: List[Dict[str, Any]],
    market_id: str,
    pubkey: str,
    action: str,
    detail: Dict[str, Any],
) -> List[Dict[str, Any]]:
    entry: Dict[str, Any] = {
        "ts": time.time(),
        "marketId": market_id,
        "pubkey": pubkey,
        "action": action,
        "detail": dict(detail),
    }
    new_history = [*history, entry]
    if len(new_history) > _MAX_HISTORY:
        new_history = new_history[len(new_history) - _MAX_HISTORY :]
    return new_history


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

ResponseT = Tuple[int, Dict[str, Any]]
PostStateResultT = Tuple[PerpsState, List[Dict[str, Any]], ResponseT]


def _epoch_phase_to_str(value: Any) -> str:
    if isinstance(value, EpochPhase):
        return value.value
    if isinstance(value, str):
        return EpochPhase(value).value
    if isinstance(value, int) and not isinstance(value, bool):
        mapping = {
            0: EpochPhase.OPEN,
            1: EpochPhase.PRICE_PUBLISHED,
            2: EpochPhase.SETTLED,
        }
        if value in mapping:
            return mapping[value].value
    raise ValueError(f"invalid epoch_phase: {value!r}")


def _canonical_pubkey(value: str) -> str:
    """Canonicalize a Tau BLS pubkey string for demo API purposes.

    Accepted forms:
    - BLS pubkey hex: 96 hex chars (optionally 0x-prefixed)
    - dev/demo token: small ASCII token (e.g. 'alice')

    Normal form:
    - hex pubkeys: lowercase, no 0x prefix
    - demo tokens: lowercase
    """
    s = (value or "").strip()
    if not s:
        raise ValueError("invalid_pubkey")
    s_body = s[2:] if s.lower().startswith("0x") else s
    if len(s_body) == 96 and _HEX_RE.fullmatch(s_body):
        return s_body.lower()
    if _PUBKEY_TOKEN_RE.fullmatch(s):
        return s.lower()
    raise ValueError("invalid_pubkey")


def _canonical_market_id(value: str) -> str:
    s = (value or "").strip()
    if not _MARKET_ID_RE.fullmatch(s):
        raise ValueError("invalid_marketId")
    return s


def _market_summary(market_id: str, market: PerpAnyMarketState) -> Dict[str, Any]:
    """Build a JSON-friendly market summary.

    Includes all guard/math fields so the UI can function even when the
    per-market detail endpoint is unreachable (graceful fallback).
    """
    if isinstance(market, PerpMarketState):
        gs = market.global_state
        return {
            "id": market_id,
            "kind": market.kind,
            "quoteAsset": market.quote_asset,
            "indexPriceE8": int(gs.get("index_price_e8", 0)),
            "clearingPriceE8": int(gs.get("clearing_price_e8", 0)),
            "fundingRateBps": int(gs.get("funding_rate_bps", 0)),
            "epochPhase": _epoch_phase_to_str(gs.get("epoch_phase", "Open")),
            "nowEpoch": int(gs.get("now_epoch", 0)),
            "insuranceBalance": int(gs.get("insurance_balance", 0)),
            "breakerActive": bool(gs.get("breaker_active", False)),
            # Guard/math fields needed by the UI for validation/display.
            "oracleSeen": bool(gs.get("oracle_seen", False)),
            "oracleLastUpdateEpoch": int(gs.get("oracle_last_update_epoch", 0)),
            "maxOracleStalenessEpochs": int(gs.get("max_oracle_staleness_epochs", 0)),
            "maxOracleMoveBps": int(gs.get("max_oracle_move_bps", 0)),
            "initialMarginBps": int(gs.get("initial_margin_bps", 0)),
            "maintenanceMarginBps": int(gs.get("maintenance_margin_bps", 0)),
            "depegBufferBps": int(gs.get("depeg_buffer_bps", 0)),
            "liquidationPenaltyBps": int(gs.get("liquidation_penalty_bps", 0)),
            "maxPositionAbs": int(gs.get("max_position_abs", 0)),
            "fundingCapBps": int(gs.get("funding_cap_bps", 0)),
        }
    if isinstance(market, PerpClearinghouse2pMarketState):
        st = market.state
        return {
            "id": market_id,
            "kind": market.kind,
            "indexPriceE8": int(st.get("index_price_e8", 0)),
            "nowEpoch": int(st.get("now_epoch", 0)),
            "breakerActive": bool(st.get("breaker_active", False)),
        }
    return {"id": market_id, "kind": getattr(market, "kind", "unknown")}


def _full_market(market_id: str, market: PerpMarketState) -> Dict[str, Any]:
    """Full market detail (isolated markets only)."""
    gs = market.global_state
    return {
        "id": market_id,
        "kind": market.kind,
        "quoteAsset": market.quote_asset,
        "nowEpoch": int(gs.get("now_epoch", 0)),
        "epochPhase": _epoch_phase_to_str(gs.get("epoch_phase", "Open")),
        "breakerActive": bool(gs.get("breaker_active", False)),
        "breakerLastTriggerEpoch": int(gs.get("breaker_last_trigger_epoch", 0)),
        "clearingPriceSeen": bool(gs.get("clearing_price_seen", False)),
        "clearingPriceEpoch": int(gs.get("clearing_price_epoch", 0)),
        "clearingPriceE8": int(gs.get("clearing_price_e8", 0)),
        "oracleSeen": bool(gs.get("oracle_seen", False)),
        "oracleLastUpdateEpoch": int(gs.get("oracle_last_update_epoch", 0)),
        "indexPriceE8": int(gs.get("index_price_e8", 0)),
        "maxOracleStalenessEpochs": int(gs.get("max_oracle_staleness_epochs", 0)),
        "maxOracleMoveBps": int(gs.get("max_oracle_move_bps", 0)),
        "initialMarginBps": int(gs.get("initial_margin_bps", 0)),
        "maintenanceMarginBps": int(gs.get("maintenance_margin_bps", 0)),
        "depegBufferBps": int(gs.get("depeg_buffer_bps", 0)),
        "liquidationPenaltyBps": int(gs.get("liquidation_penalty_bps", 0)),
        "maxPositionAbs": int(gs.get("max_position_abs", 0)),
        "fundingRateBps": int(gs.get("funding_rate_bps", 0)),
        "fundingCapBps": int(gs.get("funding_cap_bps", 0)),
        "insuranceBalance": int(gs.get("insurance_balance", 0)),
        "initialInsurance": int(gs.get("initial_insurance", 0)),
        "feeIncome": int(gs.get("fee_income", 0)),
        "claimsPaid": int(gs.get("claims_paid", 0)),
        "numAccounts": len(market.accounts),
    }


def _position_info(
    market_id: str,
    pubkey: str,
    account: PerpAccountState,
    market: PerpMarketState,
) -> Dict[str, Any]:
    """Build JSON-friendly position info with computed fields."""
    gs = market.global_state
    index_price = int(gs.get("index_price_e8", 0))
    maint_bps = int(gs.get("maintenance_margin_bps", 500))
    depeg_bps = int(gs.get("depeg_buffer_bps", 100))

    notional = (
        notional_quote(account.position_base, index_price) if account.position_base != 0 else 0
    )
    maint_req = (
        maint_margin_req(account.position_base, index_price, maint_bps, depeg_bps)
        if account.position_base != 0
        else 0
    )

    unrealized_pnl = 0
    if account.position_base != 0 and account.entry_price_e8 != 0:
        unrealized_pnl = pnl_quote(account.position_base, index_price, account.entry_price_e8)

    liq_price = liquidation_price_e8(
        account.position_base,
        account.collateral_quote,
        index_price,
        maint_bps,
        depeg_bps,
    )

    margin_ratio_bps = 0
    if notional > 0:
        margin_ratio_bps = (account.collateral_quote * BPS_SCALE) // notional

    leverage_x100 = 0
    if account.collateral_quote > 0:
        leverage_x100 = (notional * 100) // account.collateral_quote

    return {
        "marketId": market_id,
        "pubkey": pubkey,
        "positionBase": account.position_base,
        "entryPriceE8": account.entry_price_e8,
        "collateralQuote": account.collateral_quote,
        "unrealizedPnl": unrealized_pnl,
        "notionalQuote": notional,
        "maintMarginReqQuote": maint_req,
        "liquidationPriceE8": liq_price,
        "marginRatioBps": margin_ratio_bps,
        "leverageX100": leverage_x100,
    }


def _kernel_state_for_account(
    market: PerpMarketState,
    account: PerpAccountState,
) -> PerpState:
    """Build a PerpState from market globals + account state for kernel step()."""
    merged = market.kernel_state_for_account(account)
    # Filter to only PerpState fields and add epoch_phase default.
    kwargs: Dict[str, Any] = {}
    for k in PerpState.__dataclass_fields__:
        if k in merged:
            v = merged[k]
            if k == "epoch_phase":
                kwargs[k] = EpochPhase(_epoch_phase_to_str(v))
            else:
                kwargs[k] = v
    # Ensure epoch_phase is set (it lives in the kernel but not in
    # the protocol-level global_state dict).
    if "epoch_phase" not in kwargs:
        kwargs["epoch_phase"] = EpochPhase.OPEN
    return PerpState(**kwargs)


def _default_account() -> PerpAccountState:
    return PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )


def _account_from_step_result(
    base: PerpAccountState,
    new_ps: PerpState,
) -> PerpAccountState:
    """Extract account-level fields from a kernel PerpState after step()."""
    return PerpAccountState(
        position_base=new_ps.position_base,
        entry_price_e8=new_ps.entry_price_e8,
        collateral_quote=new_ps.collateral_quote,
        funding_paid_cumulative=new_ps.funding_paid_cumulative,
        funding_last_applied_epoch=new_ps.funding_last_applied_epoch,
        liquidated_this_step=new_ps.liquidated_this_step,
    )


def _update_market_account(
    market: PerpMarketState,
    pubkey: str,
    new_account: PerpAccountState,
) -> PerpMarketState:
    """Return a new PerpMarketState with the given account updated."""
    new_accounts = dict(market.accounts)
    new_accounts[pubkey] = new_account
    return PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=new_accounts,
    )


def _update_market_globals(
    market: PerpMarketState,
    new_gs: Dict[str, bool | int | str],
) -> PerpMarketState:
    return PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=new_gs,
        accounts=dict(market.accounts),
    )


def _parse_json_body(body: Optional[bytes]) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """Parse JSON from POST body. Returns (parsed, error_msg)."""
    if body is None or len(body) == 0:
        return None, "empty_body"
    if len(body) > MAX_POST_BODY:
        return None, "body_too_large"
    try:
        obj = json.loads(body)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None, "invalid_json"
    if not isinstance(obj, dict):
        return None, "expected_object"
    return obj, None


# ---------------------------------------------------------------------------
# GET handlers
# ---------------------------------------------------------------------------


def _handle_list_markets(perps: PerpsState) -> ResponseT:
    markets = [_market_summary(mid, m) for mid, m in sorted(perps.markets.items())]
    return 200, {"ok": True, "markets": markets}


def _handle_get_market(perps: PerpsState, market_id: str) -> ResponseT:
    try:
        market_id = _canonical_market_id(market_id)
    except Exception:
        return 404, {"ok": False, "error": "market_not_found"}
    market = perps.get_market(market_id)
    if market is None:
        return 404, {"ok": False, "error": "market_not_found"}
    if not isinstance(market, PerpMarketState):
        summary = _market_summary(market_id, market)
        return 200, {"ok": True, "market": summary}
    return 200, {"ok": True, "market": _full_market(market_id, market)}


def _handle_get_position(perps: PerpsState, market_id: str, pubkey: str) -> ResponseT:
    try:
        market_id = _canonical_market_id(market_id)
    except Exception:
        return 404, {"ok": False, "error": "market_not_found"}
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return 400, {"ok": False, "error": "invalid_pubkey"}
    market = perps.get_market(market_id)
    if market is None:
        return 404, {"ok": False, "error": "market_not_found"}
    if not isinstance(market, PerpMarketState):
        return 400, {"ok": False, "error": "unsupported_market_kind"}
    account = market.accounts.get(pubkey)
    if account is None:
        account = _default_account()
    return 200, {"ok": True, "position": _position_info(market_id, pubkey, account, market)}


def _handle_get_positions(perps: PerpsState, pubkey: str) -> ResponseT:
    """Return positions for all markets for a given pubkey."""
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return 400, {"ok": False, "error": "invalid_pubkey"}

    positions: Dict[str, Any] = {}
    for market_id, market in sorted(perps.markets.items()):
        if not isinstance(market, PerpMarketState):
            continue
        account = market.accounts.get(pubkey)
        if account is None:
            account = _default_account()
        positions[market_id] = _position_info(market_id, pubkey, account, market)

    return 200, {"ok": True, "positions": positions}


def _handle_history(history: List[Dict[str, Any]], pubkey: str) -> ResponseT:
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return 400, {"ok": False, "error": "invalid_pubkey"}
    entries = [h for h in history if h.get("pubkey") == pubkey]
    # Return newest-first (consistent with UI's optimistic prepend ordering).
    return 200, {"ok": True, "history": list(reversed(entries[-50:]))}


# ---------------------------------------------------------------------------
# POST handlers
# ---------------------------------------------------------------------------


def _handle_collateral(
    perps: PerpsState,
    history: List[Dict[str, Any]],
    body: Dict[str, Any],
) -> PostStateResultT:
    market_id = body.get("marketId")
    pubkey = body.get("pubkey")
    action = body.get("action")
    amount = body.get("amount")

    if not isinstance(market_id, str) or not market_id:
        return perps, history, (400, {"ok": False, "error": "missing_marketId"})
    try:
        market_id = _canonical_market_id(market_id)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_marketId"})
    if not isinstance(pubkey, str) or not pubkey:
        return perps, history, (400, {"ok": False, "error": "missing_pubkey"})
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_pubkey"})
    if action not in ("deposit", "withdraw"):
        return perps, history, (400, {"ok": False, "error": "invalid_action"})
    if isinstance(amount, bool) or not isinstance(amount, int) or amount <= 0:
        return perps, history, (400, {"ok": False, "error": "invalid_amount"})
    if int(amount) > int(PERP_PARAM_AMOUNT_MAX):
        return perps, history, (400, {"ok": False, "error": "invalid_amount"})

    market = perps.get_market(market_id)
    if market is None:
        return perps, history, (404, {"ok": False, "error": "market_not_found"})
    if not isinstance(market, PerpMarketState):
        return perps, history, (400, {"ok": False, "error": "unsupported_market_kind"})

    account = market.accounts.get(pubkey)
    if account is None:
        if len(market.accounts) >= MAX_DEMO_ACCOUNTS_PER_MARKET:
            return perps, history, (429, {"ok": False, "error": "too_many_accounts"})
        account = _default_account()

    ps = _kernel_state_for_account(market, account)

    if action == "deposit":
        params = ActionParams(action=Action.DEPOSIT_COLLATERAL, amount=amount, auth_ok=True)
    else:
        params = ActionParams(action=Action.WITHDRAW_COLLATERAL, amount=amount, auth_ok=True)

    result = step(ps, params)
    if not result.accepted:
        return (
            perps,
            history,
            (400, {"ok": False, "error": "guard_rejected", "detail": result.rejection}),
        )

    if result.state is None:
        return perps, history, (500, {"ok": False, "error": "internal_error"})
    new_account = _account_from_step_result(account, result.state)
    new_market = _update_market_account(market, pubkey, new_account)

    new_markets = dict(perps.markets)
    new_markets[market_id] = new_market
    new_perps = PerpsState(version=perps.version, markets=new_markets)
    new_history = _history_with_entry(history, market_id, pubkey, action, {"amount": amount})

    return (
        new_perps,
        new_history,
        (
            200,
            {
                "ok": True,
                "position": _position_info(market_id, pubkey, new_account, new_market),
            },
        ),
    )


def _handle_set_position(
    perps: PerpsState,
    history: List[Dict[str, Any]],
    body: Dict[str, Any],
) -> PostStateResultT:
    market_id = body.get("marketId")
    pubkey = body.get("pubkey")
    new_position_base = body.get("newPositionBase")

    if not isinstance(market_id, str) or not market_id:
        return perps, history, (400, {"ok": False, "error": "missing_marketId"})
    try:
        market_id = _canonical_market_id(market_id)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_marketId"})
    if not isinstance(pubkey, str) or not pubkey:
        return perps, history, (400, {"ok": False, "error": "missing_pubkey"})
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_pubkey"})
    if isinstance(new_position_base, bool) or not isinstance(new_position_base, int):
        return perps, history, (400, {"ok": False, "error": "invalid_newPositionBase"})
    if abs(int(new_position_base)) > int(PERP_POSITION_MAX):
        return perps, history, (400, {"ok": False, "error": "invalid_newPositionBase"})

    market = perps.get_market(market_id)
    if market is None:
        return perps, history, (404, {"ok": False, "error": "market_not_found"})
    if not isinstance(market, PerpMarketState):
        return perps, history, (400, {"ok": False, "error": "unsupported_market_kind"})

    max_abs = int(market.global_state.get("max_position_abs", PERP_POSITION_MAX))
    # Param domain bound is always enforced by the kernel (`PERP_POSITION_MAX`).
    # Also enforce a stricter per-market bound when configured.
    effective_max_abs = min(PERP_POSITION_MAX, max_abs) if max_abs > 0 else PERP_POSITION_MAX
    if abs(int(new_position_base)) > effective_max_abs:
        return perps, history, (400, {"ok": False, "error": "invalid_newPositionBase"})

    account = market.accounts.get(pubkey)
    if account is None:
        if len(market.accounts) >= MAX_DEMO_ACCOUNTS_PER_MARKET:
            return perps, history, (429, {"ok": False, "error": "too_many_accounts"})
        account = _default_account()

    ps = _kernel_state_for_account(market, account)

    params = ActionParams(
        action=Action.SET_POSITION,
        new_position_base=new_position_base,
        auth_ok=True,
    )
    result = step(ps, params)
    if not result.accepted:
        return (
            perps,
            history,
            (400, {"ok": False, "error": "guard_rejected", "detail": result.rejection}),
        )

    if result.state is None:
        return perps, history, (500, {"ok": False, "error": "internal_error"})
    new_account = _account_from_step_result(account, result.state)
    new_market = _update_market_account(market, pubkey, new_account)

    new_markets = dict(perps.markets)
    new_markets[market_id] = new_market
    new_perps = PerpsState(version=perps.version, markets=new_markets)
    new_history = _history_with_entry(
        history,
        market_id,
        pubkey,
        "set_position",
        {"newPositionBase": new_position_base},
    )

    return (
        new_perps,
        new_history,
        (
            200,
            {
                "ok": True,
                "position": _position_info(market_id, pubkey, new_account, new_market),
            },
        ),
    )


def _handle_insurance(
    perps: PerpsState,
    history: List[Dict[str, Any]],
    body: Dict[str, Any],
) -> PostStateResultT:
    market_id = body.get("marketId")
    pubkey = body.get("pubkey")
    amount = body.get("amount")

    if not isinstance(market_id, str) or not market_id:
        return perps, history, (400, {"ok": False, "error": "missing_marketId"})
    try:
        market_id = _canonical_market_id(market_id)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_marketId"})
    if not isinstance(pubkey, str) or not pubkey:
        return perps, history, (400, {"ok": False, "error": "missing_pubkey"})
    try:
        pubkey = _canonical_pubkey(pubkey)
    except Exception:
        return perps, history, (400, {"ok": False, "error": "invalid_pubkey"})
    if isinstance(amount, bool) or not isinstance(amount, int) or amount <= 0:
        return perps, history, (400, {"ok": False, "error": "invalid_amount"})
    if int(amount) > int(PERP_PARAM_AMOUNT_MAX):
        return perps, history, (400, {"ok": False, "error": "invalid_amount"})

    market = perps.get_market(market_id)
    if market is None:
        return perps, history, (404, {"ok": False, "error": "market_not_found"})
    if not isinstance(market, PerpMarketState):
        return perps, history, (400, {"ok": False, "error": "unsupported_market_kind"})

    # Build a kernel state from globals (no account needed for insurance deposit).
    account = _default_account()
    ps = _kernel_state_for_account(market, account)

    params = ActionParams(action=Action.DEPOSIT_INSURANCE, amount=amount)
    result = step(ps, params)
    if not result.accepted:
        return (
            perps,
            history,
            (400, {"ok": False, "error": "guard_rejected", "detail": result.rejection}),
        )

    if result.state is None:
        return perps, history, (500, {"ok": False, "error": "internal_error"})
    # Update global-level insurance fields in the market.
    new_gs = dict(market.global_state)
    new_gs["insurance_balance"] = result.state.insurance_balance
    new_gs["initial_insurance"] = result.state.initial_insurance
    new_market = _update_market_globals(market, new_gs)

    new_markets = dict(perps.markets)
    new_markets[market_id] = new_market
    new_perps = PerpsState(version=perps.version, markets=new_markets)
    new_history = _history_with_entry(
        history, market_id, pubkey, "deposit_insurance", {"amount": amount}
    )

    return (
        new_perps,
        new_history,
        (
            200,
            {
                "ok": True,
                "market": _full_market(market_id, new_market),
            },
        ),
    )


# ---------------------------------------------------------------------------
# Main dispatcher
# ---------------------------------------------------------------------------


def handle_perps_request(
    method: str,
    path: str,
    body: Optional[bytes],
) -> Tuple[int, Dict[str, Any]]:
    """Route a perps API request. Returns (status_code, response_dict).

    ``path`` is the URL path with query string already stripped.
    ``body`` is the raw POST body bytes (or None for GET).
    """
    segments = [s for s in path.split("/") if s]
    # Expected prefix: ['api', 'perps', ...]
    if len(segments) < 3 or segments[0] != "api" or segments[1] != "perps":
        return 404, {"ok": False, "error": "not_found"}

    rest = segments[2:]  # after 'api/perps'

    global _demo_perps, _history
    with _lock:
        try:
            if method == "GET":
                return _dispatch_get(_demo_perps, _history, rest)
            if method == "POST":
                next_perps, next_history, response = _dispatch_post(
                    _demo_perps, _history, rest, body
                )
                _demo_perps = next_perps
                _history = next_history
                return response
        except Exception:
            return 500, {"ok": False, "error": "internal_error"}

    return 405, {"ok": False, "error": "method_not_allowed"}


def _dispatch_get(perps: PerpsState, history: List[Dict[str, Any]], rest: List[str]) -> ResponseT:
    # GET /api/perps/markets
    if rest == ["markets"]:
        return _handle_list_markets(perps)

    # GET /api/perps/markets/{id}
    if len(rest) == 2 and rest[0] == "markets":
        return _handle_get_market(perps, rest[1])

    # GET /api/perps/markets/{id}/positions/{pubkey}
    if len(rest) == 4 and rest[0] == "markets" and rest[2] == "positions":
        return _handle_get_position(perps, rest[1], rest[3])

    # GET /api/perps/positions/{pubkey}
    if len(rest) == 2 and rest[0] == "positions":
        return _handle_get_positions(perps, rest[1])

    # GET /api/perps/history/{pubkey}
    if len(rest) == 2 and rest[0] == "history":
        return _handle_history(history, rest[1])

    return 404, {"ok": False, "error": "not_found"}


def _dispatch_post(
    perps: PerpsState,
    history: List[Dict[str, Any]],
    rest: List[str],
    body: Optional[bytes],
) -> PostStateResultT:
    # Check route first so unknown routes get 404 regardless of body validity.
    _KNOWN_POST_ROUTES = (["collateral"], ["position"], ["insurance"])
    if rest not in _KNOWN_POST_ROUTES:
        return perps, history, (404, {"ok": False, "error": "not_found"})

    parsed, err = _parse_json_body(body)
    if err is not None:
        return perps, history, (400, {"ok": False, "error": err})
    if parsed is None:
        return perps, history, (400, {"ok": False, "error": "bad_json"})

    # POST /api/perps/collateral
    if rest == ["collateral"]:
        return _handle_collateral(perps, history, parsed)

    # POST /api/perps/position
    if rest == ["position"]:
        return _handle_set_position(perps, history, parsed)

    # POST /api/perps/insurance
    return _handle_insurance(perps, history, parsed)


def get_oracle_sync_snapshot(market_id: str) -> Optional[Dict[str, int | str]]:
    """Return a deterministic oracle snapshot for cross-module sync checks."""
    target = str(market_id or "").strip()
    if not target:
        return None
    with _lock:
        market = _demo_perps.markets.get(target)
        if not isinstance(market, PerpMarketState):
            return None
        gs = market.global_state
        if not bool(gs.get("oracle_seen", False)):
            return None
        price_e8 = int(gs.get("index_price_e8", 0))
        oracle_epoch = int(gs.get("oracle_last_update_epoch", 0))
        now_epoch = int(gs.get("now_epoch", 0))
        if price_e8 <= 0 or oracle_epoch < 0 or now_epoch < 0:
            return None
        return {
            "market_id": target,
            "price_e8": price_e8,
            "oracle_last_update_epoch": oracle_epoch,
            "now_epoch": now_epoch,
        }


def reset_demo_state() -> None:
    """Reset module-level demo state. For tests only."""
    global _demo_perps, _history
    with _lock:
        _demo_perps = _make_demo_perps()
        _history.clear()
