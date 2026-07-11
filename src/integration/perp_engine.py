"""
Perpetuals execution adapter for Tau Net-style transactions.

This module applies operation group "8" (perps) to `DexState` in a deterministic,
fail-closed way. It is intentionally conservative:
- Account-scoped actions require tx_sender_pubkey == account_pubkey.
- Isolated-market admin actions require an explicit operator pubkey configured (optional).
- Market-parameter updates (`set_market_params`) are operator-only and fail-closed on
  invariant violations (including making any open position under-maintenance).
- Clearinghouse market formation and matched position updates require per-operation
  signatures from the participating accounts (replay-protected via nonces).
- Clearing-price publication for clearinghouse markets is oracle-authorized when
  `oracle_pubkey` is configured.
- Unknown fields/actions are rejected.

Two perps operation versions are supported:
- v0.1: isolated-margin per-account execution (single-account abstraction; optional and disabled by default).
- v1.0 (and legacy v0.2): a minimal 2-party clearinghouse posture with enforced net-zero exposure.
  - Markets are namespaced with a `perp:ch2p:` prefix to avoid mixing semantics.
  - Market init and matched position updates are jointly authorized by the two accounts.
  - Clearinghouse collateral is tracked internally in quote-e8 units so epoch PnL is exact and conserved.
  - The clearinghouse state transition is spec-driven: the persistent market state stores a kernel-state dict.
- v1.1: a 3-party transfer clearinghouse posture with a standby account (A,B,C).
  - Markets are namespaced with a `perp:ch3p:` prefix to avoid mixing semantics.
  - Market init and matched position updates are jointly authorized by the three accounts and
    must keep net position == 0 with at least one idle account.
  - If exactly one account is below maintenance at settlement and the idle account can meet initial margin,
    the distressed position is transferred to the idle account; otherwise positions close to flat.

Per-account risk checks (guards/limits) reuse the epoch-perp risk kernel wrapper in
`src/core/perp_epoch.py` (native Python implementation by default). The optional
kernel-spec verification/codegen toolchain is used for evidence and parity testing,
not required at runtime.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Callable, Dict, List, Mapping, Optional

from ..core.dex import DexState
from ..core import perp_np_clearinghouse as _np_core
from ..core.perp_apply_funding_auto_gate import (
    MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    evaluate_perp_apply_funding_auto_gate,
    is_derivatives_safe_mark_price_source,
    perp_apply_funding_auto_gate_error,
)
from ..core.perp_clearinghouse_market_params_guard import (
    MARKET_KIND_CH2P,
    MARKET_KIND_CH3P,
    evaluate_perp_clearinghouse_market_params_guard,
    perp_clearinghouse_market_params_guard_error,
)
from ..core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perp_np_matching import Intent as _NpIntent
from ..core.perp_v2.funding_rule import compute_funding_rate_bps
from ..core.perp_v2.math import MAX_COLLATERAL
from ..core.perp_v2.math import funding_payment as _perp_v2_funding_payment
from ..core.perp_v2.math import is_oracle_fresh as _perp_v2_is_oracle_fresh
from ..core.perp_v2.math import maint_margin_req as _perp_v2_maint_margin_req
from ..core.perp_v2.math import settle_price as _perp_v2_settle_price
from ..core.perps import (
    PerpAnyMarketState,
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_GLOBAL_KEYS,
    PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
    PERPS_STATE_VERSION,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount as _NpAccount,
    PerpClearinghouseNpMarketState as _NpMarketState,
    PerpClearinghouseNpPendingIntent as _NpPendingIntent,
    PerpMarketState,
    PerpsState,
)
from ..core.perp_market_version_prefix_guard import (
    REJECT_CH2P_PREFIX_MISMATCH,
    REJECT_CH3P_PREFIX_MISMATCH,
    REJECT_INVALID_VERSION,
    REJECT_ISOLATED_PREFIX_CONFLICT,
    evaluate_perp_market_version_prefix_guard,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_ADVANCE_EPOCH as RUNTIME_ACTION_ADVANCE_EPOCH,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_APPLY_FUNDING_AUTO as RUNTIME_ACTION_APPLY_FUNDING_AUTO,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_CLEAR_BREAKER as RUNTIME_ACTION_CLEAR_BREAKER,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_DEPOSIT_COLLATERAL as RUNTIME_ACTION_DEPOSIT_COLLATERAL,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_PARTIAL_LIQUIDATE as RUNTIME_ACTION_PARTIAL_LIQUIDATE,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_PUBLISH_CLEARING_PRICE as RUNTIME_ACTION_PUBLISH_CLEARING_PRICE,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_SET_MARKET_PARAMS as RUNTIME_ACTION_SET_MARKET_PARAMS,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_SET_POSITION as RUNTIME_ACTION_SET_POSITION,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_SETTLE_EPOCH as RUNTIME_ACTION_SETTLE_EPOCH,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_WITHDRAW_COLLATERAL as RUNTIME_ACTION_WITHDRAW_COLLATERAL,
)
from ..core.perp_runtime_risk_gate import (
    evaluate_perp_runtime_risk_gate,
    perp_runtime_risk_gate_error,
)
from ..core.perp_signed_surface_guard import (
    ACTION_INIT_MARKET_2P,
    ACTION_INIT_MARKET_3P,
    ACTION_PUBLISH_CLEARING_PRICE,
    ACTION_SET_POSITION_PAIR,
    ACTION_SET_POSITION_TRIPLET,
    evaluate_perp_signed_surface_guard,
    perp_signed_surface_guard_error,
)
from ..core.perp_submission_auth_gate import (
    evaluate_perp_submission_auth_gate,
    perp_submission_auth_gate_error,
)
from ..core.perp_submission_auth_message import (
    PERP_OP_AUTH_SIGNED_FIELD_KEYS_V1,
    build_perp_op_auth_signing_dict_v1,
    hash_perp_op_auth_message_v1,
)
from ..state.balances import BalanceTable
from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
)
from ..state.nonces import NonceTable
from .zeno_oracle_authorization import check_critical_consumer_authorization, semantic_hash

PERP_OP_MODULE = "TauPerp"
PERP_OP_VERSION_V0_1 = "0.1"
# Clearinghouse (2-party) posture versions:
# - 0.2: initial rollout (kept for compatibility)
# - 1.0: "production" tag for the same semantics
PERP_OP_VERSION_CH2P_V0_2 = "0.2"
PERP_OP_VERSION_CH2P_V1_0 = "1.0"
PERP_OP_VERSION_CH3P_V1_1 = "1.1"
PERP_OP_VERSION_CHNP_V1_2 = "1.2"
PERP_STATEFUL_SURFACE = "perp_stateful"

PERP_OPS_KEY = "8"
LEGACY_PERP_OPS_KEY = "5"

# v0.2 markets are explicitly namespaced to avoid mixing semantics without a snapshot schema change.
# This is a fail-closed API convention, not a security boundary.
PERP_CH2P_MARKET_PREFIX = "perp:ch2p:"
PERP_CH3P_MARKET_PREFIX = "perp:ch3p:"
PERP_CHNP_MARKET_PREFIX = "perp:chnp:"

_E8_SCALE = 100_000_000

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")
_U32_MAX = 0xFFFFFFFF
_BPS_SCALE = 10_000
OracleAdapterBridgeVerifier = Callable[[Mapping[str, Any]], Any]


def _funded_liquidation_params_ok(
    *,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    max_oracle_move_bps: int,
    liquidation_penalty_bps: int,
) -> bool:
    """DbC invariant: liquidation penalty remains funded after one clamped oracle move.

    Ensures that after a single-epoch oracle move of ``max_oracle_move_bps`` bps,
    the liquidation penalty is still covered by the effective maintenance margin.
    This is the funded-liquidation inequality (R1 of the perps mechanism doc):
    ``liquidation_penalty_bps * (BPS_SCALE + max_oracle_move_bps)
    <= BPS_SCALE * (eff_maint_bps - max_oracle_move_bps)``
    where ``eff_maint_bps = maintenance_margin_bps + depeg_buffer_bps``.
    """
    eff_maint_bps = int(maintenance_margin_bps) + int(depeg_buffer_bps)
    return int(liquidation_penalty_bps) * (_BPS_SCALE + int(max_oracle_move_bps)) <= _BPS_SCALE * (
        eff_maint_bps - int(max_oracle_move_bps)
    )


def _safe_error_str(exc: Exception) -> str:
    """Convert an exception to a stable, single-line error string.

    Goal: avoid leaking non-deterministic details (e.g., memory addresses) while
    still surfacing useful validation errors for malformed inputs.
    """
    if isinstance(exc, (ValueError, TypeError, KeyError)):
        msg = str(exc)
    else:
        msg = f"internal error: {type(exc).__name__}"
    msg = " ".join((msg or "").split())
    if not msg:
        msg = "internal error"
    if len(msg) > 512:
        msg = msg[:512]
    return msg


_ASCII_TOKEN_CHARS_MODULE = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")
_ASCII_TOKEN_CHARS_VERSION = frozenset("0123456789.")
_ASCII_TOKEN_CHARS_ACTION = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")
_ASCII_TOKEN_CHARS_MARKET_ID = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789:._-")
_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_ORACLE_PERPS_INDEX_QUERY_ID = (
    "sha256:"
    + hashlib.sha256("zenodex.oracle.query.perps.index_price_e8".encode("utf-8")).hexdigest()
)


def _oracle_consumer_profile_id(*, action_kind: str, max_freshness_window_epochs: int) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(
            {
                "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
                "consumer_module": "zenodex.perps",
                "action_kind": action_kind,
                "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
                "required_evidence_floor": "O3",
                "max_freshness_window_epochs": int(max_freshness_window_epochs),
                "critical": True,
            }
        )
    ).hexdigest()


_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID = _oracle_consumer_profile_id(
    action_kind="settle_epoch",
    max_freshness_window_epochs=2,
)
_ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID = _oracle_consumer_profile_id(
    action_kind="liquidate_account",
    max_freshness_window_epochs=1,
)


def _require_ascii_token(value: Any, *, name: str, max_len: int, allowed: frozenset[str]) -> str:
    s = _require_str(value, name=name, non_empty=True, max_len=max_len)
    if s != s.strip():
        raise ValueError(f"{name} must not have leading/trailing whitespace")
    if not s.isascii():
        raise ValueError(f"{name} must be ASCII")
    for ch in s:
        if ch in allowed:
            continue
        raise ValueError(f"{name} has invalid characters")
    return s


_ISOLATED_CONTROL_PARAM_BOUNDS: dict[str, tuple[int, int]] = {
    # Per src/kernels/dex/perp_epoch_isolated_v2.yaml (role: control)
    "max_oracle_staleness_epochs": (1, 1_000_000),
    "max_oracle_move_bps": (0, 10_000),
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "depeg_buffer_bps": (0, 5_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_position_abs": (1, 1_000_000),
    "funding_cap_bps": (1, 10_000),
    "min_notional_for_bounty": (0, 1_000_000_000_000),
}

_CLEARINGHOUSE_CONTROL_PARAM_BOUNDS: dict[str, tuple[int, int]] = {
    # Per src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml and
    #     src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml (role: control)
    "max_oracle_staleness_epochs": (1, 1_000_000),
    "max_oracle_move_bps": (0, 10_000),
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_position_abs": (1, 1_000_000),
}

_CLEARINGHOUSE_NP_CONTROL_PARAM_BOUNDS: dict[str, tuple[int, int]] = {
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "depeg_buffer_bps": (0, 5_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_oracle_move_bps": (0, 10_000),
    "funding_cap_bps": (1, 10_000),
    "max_position_abs": (1, 1_000_000),
    "min_notional_for_bounty_e8": (0, 1_000_000_000_000 * _E8_SCALE),
}


def _validated_control_params(
    params: Mapping[str, Any],
    *,
    bounds: Mapping[str, tuple[int, int]],
    name: str,
) -> dict[str, int]:
    if not isinstance(params, Mapping):
        raise ValueError(f"{name} must be an object")
    out: dict[str, int] = {}
    for k, v in params.items():
        if not isinstance(k, str):
            raise ValueError(f"{name} keys must be strings")
        if k not in bounds:
            raise ValueError(f"unknown {name} key: {k}")
        n = _require_int(v, name=f"{name}.{k}", non_negative=True)
        lo, hi = bounds[k]
        if n < lo or n > hi:
            raise ValueError(f"{name}.{k} out of range: {n} not in [{lo}, {hi}]")
        out[k] = int(n)
    return out


def _min_collectible_liquidation_penalty_quote(
    config: "PerpEngineConfig",
) -> int:
    value = config.min_collectible_liquidation_penalty_quote
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError("invalid config: min_collectible_liquidation_penalty_quote must be an int")
    if value < 0 or value > MAX_COLLATERAL:
        raise ValueError(
            f"invalid config: min_collectible_liquidation_penalty_quote must be in [0, {MAX_COLLATERAL}]"
        )
    return int(value)


def _apply_isolated_market_params(
    market: PerpMarketState,
    *,
    params: Mapping[str, Any],
    min_collectible_liquidation_penalty_quote: int,
) -> PerpMarketState:
    updates = _validated_control_params(params, bounds=_ISOLATED_CONTROL_PARAM_BOUNDS, name="params")
    if not updates:
        return market

    new_global = dict(market.global_state)
    for k, v in updates.items():
        new_global[k] = int(v)

    old_liquidation_penalty_bps = int(market.global_state["liquidation_penalty_bps"])
    old_min_notional_for_bounty = int(market.global_state["min_notional_for_bounty"])
    new_liquidation_penalty_bps = int(new_global["liquidation_penalty_bps"])
    new_min_notional_for_bounty = int(new_global["min_notional_for_bounty"])
    has_open_positions = any(int(acct.position_base) != 0 for acct in market.accounts.values())

    # Scientist hardening (bounty-farming lane):
    # while positions are open, reject parameter shocks that increase liquidation keeper payoff
    # by raising penalty bps or lowering the bounty-eligible notional threshold.
    if has_open_positions:
        if new_liquidation_penalty_bps > old_liquidation_penalty_bps:
            raise ValueError("invalid params: cannot increase liquidation_penalty_bps while positions are open")
        if new_min_notional_for_bounty < old_min_notional_for_bounty:
            raise ValueError("invalid params: cannot decrease min_notional_for_bounty while positions are open")

    # Enforce kernel-level invariants that depend on control params.
    max_oracle_move_bps = int(new_global["max_oracle_move_bps"])
    initial_margin_bps = int(new_global["initial_margin_bps"])
    maintenance_margin_bps = int(new_global["maintenance_margin_bps"])
    depeg_buffer_bps = int(new_global["depeg_buffer_bps"])
    liquidation_penalty_bps = int(new_global["liquidation_penalty_bps"])
    funding_cap_bps = int(new_global["funding_cap_bps"])
    max_position_abs = int(new_global["max_position_abs"])
    index_price_e8 = int(new_global["index_price_e8"])

    # Funding cap changes can make the stored "last rate" out of bounds. The rate is informational,
    # not a consensus-critical input to margin math, so we clamp it to preserve invariants.
    funding_rate_bps = int(new_global["funding_rate_bps"])
    if abs(funding_rate_bps) > funding_cap_bps:
        new_global["funding_rate_bps"] = funding_cap_bps if funding_rate_bps >= 0 else -funding_cap_bps
        funding_rate_bps = int(new_global["funding_rate_bps"])

    eff_maint_bps = maintenance_margin_bps + depeg_buffer_bps
    if depeg_buffer_bps <= 0:
        raise ValueError("invalid params: require depeg_buffer_bps > 0")
    if max_oracle_move_bps > eff_maint_bps:
        raise ValueError("invalid params: require max_oracle_move_bps <= maintenance_margin_bps + depeg_buffer_bps")
    if eff_maint_bps > initial_margin_bps:
        raise ValueError("invalid params: require maintenance_margin_bps + depeg_buffer_bps <= initial_margin_bps")
    if liquidation_penalty_bps >= eff_maint_bps:
        raise ValueError("invalid params: require liquidation_penalty_bps < maintenance_margin_bps + depeg_buffer_bps")
    if liquidation_penalty_bps <= 0:
        raise ValueError("invalid params: require liquidation_penalty_bps > 0")
    if not _funded_liquidation_params_ok(
        maintenance_margin_bps=maintenance_margin_bps,
        depeg_buffer_bps=depeg_buffer_bps,
        max_oracle_move_bps=max_oracle_move_bps,
        liquidation_penalty_bps=liquidation_penalty_bps,
    ):
        raise ValueError("invalid params: require funded liquidation after max_oracle_move_bps")

    # Scientist-driven anti-farming guard:
    # if a liquidation is eligible for bounty accounting, the notional threshold must be
    # high enough to guarantee a non-zero collectible penalty under integer rounding.
    min_notional_for_bounty = int(new_global["min_notional_for_bounty"])
    min_notional_for_positive_penalty = (_BPS_SCALE + liquidation_penalty_bps - 1) // liquidation_penalty_bps
    if min_notional_for_bounty < min_notional_for_positive_penalty:
        raise ValueError(
            "invalid params: require min_notional_for_bounty >= ceil(10000 / liquidation_penalty_bps)"
        )
    if int(min_collectible_liquidation_penalty_quote) > 0:
        min_notional_for_policy_floor = (
            (int(min_collectible_liquidation_penalty_quote) * _BPS_SCALE) + liquidation_penalty_bps - 1
        ) // liquidation_penalty_bps
        if min_notional_for_bounty < min_notional_for_policy_floor:
            raise ValueError(
                "invalid params: require min_notional_for_bounty >= "
                f"ceil({int(min_collectible_liquidation_penalty_quote)} * 10000 / liquidation_penalty_bps)"
            )

    # Fail-closed: do not allow parameter changes that would invalidate any open position.
    for pk in sorted(market.accounts.keys()):
        acct = market.accounts[pk]
        if abs(int(acct.position_base)) > max_position_abs:
            raise ValueError(f"invalid params: account {pk} position exceeds new max_position_abs")
        if acct.position_base == 0:
            continue
        maint_req = _perp_v2_maint_margin_req(
            acct.position_base,
            index_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
        )
        if acct.collateral_quote < maint_req:
            raise ValueError(f"invalid params: account {pk} would be under maintenance margin")

    return PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=new_global,
        accounts=dict(market.accounts),
    )


def _apply_clearinghouse_market_params(
    state: Mapping[str, Any],
    *,
    params: Mapping[str, Any],
    kind: str,
    operator_ok: bool,
    epoch_settled_ok: bool,
) -> Dict[str, Any]:
    updates = _validated_control_params(params, bounds=_CLEARINGHOUSE_CONTROL_PARAM_BOUNDS, name="params")
    if not updates:
        return dict(state)

    new_state = dict(state)
    for k, v in updates.items():
        new_state[k] = int(v)

    kind_code = MARKET_KIND_CH2P if kind == "ch2p" else MARKET_KIND_CH3P if kind == "ch3p" else 0
    guard = evaluate_perp_clearinghouse_market_params_guard(
        market_kind=kind_code,
        operator_ok=operator_ok,
        epoch_settled_ok=epoch_settled_ok,
        position_base_a=int(state.get("position_base_a", 0)),
        position_base_b=int(state.get("position_base_b", 0)),
        position_base_c=int(state.get("position_base_c", 0)),
        old_liquidation_penalty_bps=int(state.get("liquidation_penalty_bps", 0)),
        new_liquidation_penalty_bps=int(new_state.get("liquidation_penalty_bps", 0)),
        new_maintenance_margin_bps=int(new_state.get("maintenance_margin_bps", 0)),
    )
    if not guard.admission_ok:
        raise ValueError(perp_clearinghouse_market_params_guard_error(guard) or "invalid clearinghouse market params")

    # Funded-liquidation invariant: the liquidation penalty must remain covered
    # after one clamped oracle move. Clearinghouse markets do not carry an
    # explicit depeg_buffer_bps, so the effective maintenance margin is just
    # maintenance_margin_bps.
    ch_max_oracle_move_bps = int(new_state.get("max_oracle_move_bps", 0))
    ch_maintenance_margin_bps = int(new_state.get("maintenance_margin_bps", 0))
    ch_liquidation_penalty_bps = int(new_state.get("liquidation_penalty_bps", 0))
    if not _funded_liquidation_params_ok(
        maintenance_margin_bps=ch_maintenance_margin_bps,
        depeg_buffer_bps=0,
        max_oracle_move_bps=ch_max_oracle_move_bps,
        liquidation_penalty_bps=ch_liquidation_penalty_bps,
    ):
        raise ValueError("invalid params: require funded liquidation after max_oracle_move_bps")

    try:
        if kind == "ch2p":
            _ch2p_state_from_dict(new_state)
        elif kind == "ch3p":
            _ch3p_state_from_dict(new_state)
        else:  # pragma: no cover
            raise ValueError(f"unknown clearinghouse kind: {kind}")
    except Exception as exc:
        raise ValueError(str(exc)) from exc

    return new_state



@lru_cache
def _load_ch2p_ref_model():
    """Load the generated Python reference model for the clearinghouse kernel.

    This is a deterministic, dependency-free reference implementation generated
    from the YAML kernel spec and committed into this repo under `generated/`.
    We load it by file path so this module does not depend on any packaging or
    import-path configuration.
    """

    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_clearinghouse_2p_v0_1_ref.py"
    if not ref_path.is_file():
        raise FileNotFoundError(
            f"missing generated clearinghouse ref model at {ref_path}; run tools/export_kernel_artifacts.py"
        )
    spec = spec_from_file_location("perp_epoch_clearinghouse_2p_v0_1_ref", ref_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"failed to load module spec for {ref_path}")
    module = module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    field_names = [f.name for f in fields(module.State)]
    if set(field_names) != set(PERP_CLEARINGHOUSE_2P_STATE_KEYS):
        raise RuntimeError(
            "clearinghouse ref model state fields do not match PERP_CLEARINGHOUSE_2P_STATE_KEYS; "
            "regenerate artifacts and update src/core/perps.py"
        )
    return module


def _ch2p_state_from_dict(state: Mapping[str, Any]):
    ref = _load_ch2p_ref_model()
    kwargs = {name: state[name] for name in (f.name for f in fields(ref.State))}
    s = ref.State(**kwargs)
    ok, failed = ref.check_invariants(s)
    if not ok:
        raise ValueError(f"invalid clearinghouse state (invariant {failed})")
    return s


def _ch2p_state_to_dict(state) -> Dict[str, Any]:
    ref = _load_ch2p_ref_model()
    return {f.name: getattr(state, f.name) for f in fields(ref.State)}


def _ch2p_init_state_dict() -> Dict[str, Any]:
    ref = _load_ch2p_ref_model()
    return _ch2p_state_to_dict(ref.init_state())


def _ch2p_step(state_dict: Mapping[str, Any], *, tag: str, args: Mapping[str, Any]) -> tuple[Dict[str, Any], Dict[str, Any]]:
    ref = _load_ch2p_ref_model()
    cmd = ref.Command(tag=tag, args=dict(args))
    res = ref.step(_ch2p_state_from_dict(state_dict), cmd)
    if not res.ok or res.state is None:
        raise ValueError(res.error or f"{tag} rejected")
    ok, failed = ref.check_invariants(res.state)
    if not ok:
        raise ValueError(f"post-invariant violated: {failed}")
    return _ch2p_state_to_dict(res.state), dict(res.effects or {})


@lru_cache
def _load_ch3p_ref_model():
    """Load the generated Python reference model for the 3-party transfer clearinghouse kernel."""

    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py"
    if not ref_path.is_file():
        raise FileNotFoundError(
            f"missing generated clearinghouse ref model at {ref_path}; run tools/export_kernel_artifacts.py"
        )
    spec = spec_from_file_location("perp_epoch_clearinghouse_3p_transfer_v0_1_ref", ref_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"failed to load module spec for {ref_path}")
    module = module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    field_names = [f.name for f in fields(module.State)]
    if set(field_names) != set(PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS):
        raise RuntimeError(
            "clearinghouse ref model state fields do not match PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS; "
            "regenerate artifacts and update src/core/perps.py"
        )
    return module


def _ch3p_state_from_dict(state: Mapping[str, Any]):
    ref = _load_ch3p_ref_model()
    kwargs = {name: state[name] for name in (f.name for f in fields(ref.State))}
    s = ref.State(**kwargs)
    ok, failed = ref.check_invariants(s)
    if not ok:
        raise ValueError(f"invalid clearinghouse state (invariant {failed})")
    return s


def _ch3p_state_to_dict(state) -> Dict[str, Any]:
    ref = _load_ch3p_ref_model()
    return {f.name: getattr(state, f.name) for f in fields(ref.State)}


def _ch3p_init_state_dict() -> Dict[str, Any]:
    ref = _load_ch3p_ref_model()
    return _ch3p_state_to_dict(ref.init_state())


def _ch3p_step(state_dict: Mapping[str, Any], *, tag: str, args: Mapping[str, Any]) -> tuple[Dict[str, Any], Dict[str, Any]]:
    ref = _load_ch3p_ref_model()
    cmd = ref.Command(tag=tag, args=dict(args))
    res = ref.step(_ch3p_state_from_dict(state_dict), cmd)
    if not res.ok or res.state is None:
        raise ValueError(res.error or f"{tag} rejected")
    ok, failed = ref.check_invariants(res.state)
    if not ok:
        raise ValueError(f"post-invariant violated: {failed}")
    return _ch3p_state_to_dict(res.state), dict(res.effects or {})


@dataclass(frozen=True)
class PerpEngineConfig:
    operator_pubkey: Optional[str] = None
    # Signature domain separation for per-op authorization (bind to a specific network/deployment).
    chain_id: str = "tau-net-alpha"
    # Optional oracle signer for clearing-price publication (recommended for clearinghouse markets).
    oracle_pubkey: Optional[str] = None
    # Production posture: perps are intended to run peer-to-peer via clearinghouse kernels.
    # Isolated markets are a single-account risk abstraction and are disabled by default to
    # prevent accidental deployment of "protocol counterparty" semantics without an explicit
    # balance sheet / loss-allocation design.
    allow_isolated_markets: bool = False
    max_ops: int = 256
    max_op_bytes: int = 64_000
    max_total_ops_bytes: int = 512_000
    # Hard cap for untrusted integer widths in ops (DoS resistance).
    # All current kernels fit comfortably within 128 bits; keep headroom.
    max_int_bits: int = 256
    # Scientist-derived oracle-manipulation posture guard:
    # require reward subsidy + safety margin to stay below fee friction.
    oracle_spot_fee_bps: int = 30
    oracle_spot_reward_bps: int = 0
    oracle_spot_reward_safety_margin_bps: int = 1
    # Optional ZenoOracle aggregate-adapter verifier. If a settle_epoch op
    # carries `oracle_adapter_bridge`, the engine verifies that bridge before
    # settlement and checks that it binds to zenodex.perps / settle_epoch.
    oracle_adapter_bridge_verifier: Optional[OracleAdapterBridgeVerifier] = None
    require_oracle_adapter_for_isolated_settle_epoch: bool = False
    require_oracle_adapter_for_isolated_partial_liquidate: bool = False
    require_oracle_adapter_for_clearinghouse_settle_epoch: bool = False
    # Scientist-derived anti-bounty-farming posture guard:
    # require a non-trivial minimum collectible liquidation penalty for bounty-eligible notional.
    min_collectible_liquidation_penalty_quote: int = 1_000
    # Optional production bridge: require a typed ZenoOracle authorization before
    # isolated perps settlement can consume the current oracle/index snapshot.
    require_oracle_authorization_for_isolated_settle: bool = False
    # Explicit settle_epoch spelling used by adapter bridge policy gates.
    require_oracle_authorization_for_isolated_settle_epoch: bool = False
    require_oracle_authorization_for_clearinghouse_settle_epoch: bool = False


@dataclass(frozen=True)
class PerpOp:
    market_id: str
    action: str
    version: str
    data: Dict[str, Any]


@dataclass(frozen=True)
class PerpTxResult:
    ok: bool
    state: Optional[DexState] = None
    effects: Optional[List[Dict[str, Any]]] = None
    error: Optional[str] = None


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _require_int(value: Any, *, name: str, non_negative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if non_negative and value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _require_int_u32_pos(value: Any, *, name: str) -> int:
    n = _require_int(value, name=name, non_negative=True)
    if n <= 0:
        raise ValueError(f"{name} must be a positive int")
    if n > _U32_MAX:
        raise ValueError(f"{name} must fit in u32")
    return int(n)


def _hex_to_bytes_allow_0x(hex_str: str, *, name: str, expected_nbytes: Optional[int] = None) -> bytes:
    if not isinstance(hex_str, str):
        raise TypeError(f"{name} must be a string")
    s = hex_str[2:] if hex_str.lower().startswith("0x") else hex_str
    if not s:
        raise ValueError(f"{name} must be non-empty hex")

    if expected_nbytes is not None:
        if not isinstance(expected_nbytes, int) or isinstance(expected_nbytes, bool) or expected_nbytes <= 0:
            raise ValueError("expected_nbytes must be a positive int")
        expected_hex_len = 2 * expected_nbytes
        if len(s) != expected_hex_len:
            raise ValueError(f"{name} must be {expected_nbytes} bytes (hex length {expected_hex_len})")

    if len(s) % 2 != 0:
        raise ValueError(f"{name} must have an even number of hex chars")
    if not _HEX_CHARS_RE.fullmatch(s):
        raise ValueError(f"{name} must be valid hex")
    try:
        out = bytes.fromhex(s)
    except ValueError as exc:
        raise ValueError(f"{name} must be valid hex") from exc
    if expected_nbytes is not None and len(out) != expected_nbytes:
        raise ValueError(f"{name} must decode to exactly {expected_nbytes} bytes")
    return out


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def _copy_nonce_table(nonces: NonceTable) -> NonceTable:
    copied = NonceTable()
    for pk, last in nonces.get_all().items():
        copied.set_last(pk, int(last))
    return copied


def _perps_settle_query_id(*, market_id: str) -> str:
    return f"zenodex.perps.{market_id}.index_price_e8"


def _isolated_market_state_hash(*, market_id: str, market: PerpMarketState) -> str:
    return semantic_hash(
        "zenodex.perps.isolated.pre_state.v1",
        {
            "accounts": {
                str(pk): acct.to_kernel_state()
                for pk, acct in sorted(market.accounts.items(), key=lambda item: str(item[0]))
            },
            "global_state": {str(k): market.global_state[k] for k in sorted(market.global_state.keys())},
            "kind": market.kind,
            "market_id": str(market_id),
            "quote_asset": str(market.quote_asset),
        },
    )


def _isolated_settle_oracle_runtime_facts(*, market_id: str, market: PerpMarketState) -> Dict[str, Any]:
    global_state = market.global_state
    pre_state_hash = _isolated_market_state_hash(market_id=market_id, market=market)
    facts_payload: Dict[str, Any] = {
        "action_kind": "settle_epoch",
        "clearing_price_e8": int(global_state.get("clearing_price_e8", 0)),
        "clearing_price_epoch": int(global_state.get("clearing_price_epoch", 0)),
        "clearing_price_seen": bool(global_state.get("clearing_price_seen", False)),
        "consumer_module": "zenodex.perps",
        "index_price_e8": int(global_state.get("index_price_e8", 0)),
        "market_id": str(market_id),
        "max_oracle_move_bps": int(global_state.get("max_oracle_move_bps", 0)),
        "max_oracle_staleness_epochs": int(global_state.get("max_oracle_staleness_epochs", 0)),
        "now_epoch": int(global_state.get("now_epoch", 0)),
        "oracle_last_update_epoch": int(global_state.get("oracle_last_update_epoch", 0)),
        "oracle_seen": bool(global_state.get("oracle_seen", False)),
        "pre_state_hash": pre_state_hash,
        "query_id": _perps_settle_query_id(market_id=market_id),
        "quote_asset": str(market.quote_asset),
    }
    action_facts_hash = semantic_hash("zenodex.perps.settle_epoch.facts.v1", facts_payload)
    action_id = semantic_hash(
        "zenodex.perps.settle_epoch.action.v1",
        {
            "action_facts_hash": action_facts_hash,
            "market_id": str(market_id),
        },
    )
    return {
        "action_facts_hash": action_facts_hash,
        "action_id": action_id,
        "now_epoch": int(global_state.get("now_epoch", 0)),
        "pre_state_hash": pre_state_hash,
        "query_id": _perps_settle_query_id(market_id=market_id),
        "runtime_value_e8": int(global_state.get("index_price_e8", 0)),
    }


def _requires_isolated_settle_oracle_authorization(config: PerpEngineConfig) -> bool:
    return bool(
        config.require_oracle_authorization_for_isolated_settle
        or config.require_oracle_authorization_for_isolated_settle_epoch
    )


def _check_isolated_settle_oracle_authorization(
    *,
    ctx: "_PerpApplyCtx",
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    authorization_required = _requires_isolated_settle_oracle_authorization(ctx.config)
    authorization = op.data.get("oracle_authorization")
    if authorization is None:
        if authorization_required:
            return "oracle_authorization_required"
        return None
    if not isinstance(authorization, Mapping):
        return "oracle_authorization must be an object"
    # DbC: typed semantic binding is necessary, but not sufficient, for the
    # production authorization gate. The gate must also be backed by the
    # independently configured adapter bridge verifier already checked by the
    # caller; otherwise a caller can self-forge a structurally consistent bundle.
    if authorization_required and "oracle_adapter_bridge" not in op.data:
        return "settle_epoch requires oracle_adapter_bridge"
    if not bool(market.global_state.get("oracle_seen", False)):
        return "oracle_authorization_rejected: oracle snapshot not seen"
    if int(market.global_state.get("index_price_e8", 0)) <= 0:
        return "oracle_authorization_rejected: index_price_e8 must be positive"

    runtime = _isolated_settle_oracle_runtime_facts(market_id=op.market_id, market=market)
    try:
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            action_id=str(runtime["action_id"]),
            action_facts_hash=str(runtime["action_facts_hash"]),
            pre_state_hash=str(runtime["pre_state_hash"]),
            query_id=str(runtime["query_id"]),
            runtime_value_e8=int(runtime["runtime_value_e8"]),
            now_epoch=int(runtime["now_epoch"]),
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            max_freshness_window_epochs=2,
        )
    except Exception as exc:
        return f"oracle_authorization_rejected: {exc}"
    if not bool(result.get("typed_ok", False)):
        errors = result.get("typed_errors") or result.get("opaque_errors") or ["typed authorization rejected"]
        return "oracle_authorization_rejected: " + "; ".join(str(err) for err in errors)
    return None


def _assert_ints_within_bits(obj: Any, *, max_bits: int, name: str) -> None:
    if not isinstance(max_bits, int) or isinstance(max_bits, bool) or max_bits <= 0:
        raise ValueError("max_int_bits must be a positive int")
    if max_bits > 4096:
        raise ValueError("max_int_bits too large")

    stack = [obj]
    while stack:
        cur = stack.pop()
        if isinstance(cur, bool) or cur is None:
            continue
        if isinstance(cur, int):
            if abs(int(cur)).bit_length() > max_bits:
                raise ValueError(f"{name} contains an int wider than {max_bits} bits")
            continue
        if isinstance(cur, Mapping):
            stack.extend(cur.values())
            continue
        if isinstance(cur, list):
            stack.extend(cur)
            continue


def parse_perp_ops(
    operations: Mapping[str, Any],
    *,
    max_ops: int = 256,
    max_op_bytes: int = 64_000,
    max_total_ops_bytes: int = 512_000,
    max_int_bits: int = 256,
) -> List[PerpOp]:
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    if PERP_OPS_KEY in operations and LEGACY_PERP_OPS_KEY in operations:
        raise ValueError("ambiguous perps streams: use either upstream stream 8 or legacy stream 5")
    selected_key = PERP_OPS_KEY if PERP_OPS_KEY in operations else LEGACY_PERP_OPS_KEY
    raw = operations.get(selected_key)
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError(f"operations[{selected_key!r}] must be a list")
    if len(raw) > max_ops:
        raise ValueError(f"too many perps ops: {len(raw)} > {max_ops}")

    total_bytes = 0
    out: List[PerpOp] = []
    for i, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise ValueError(f"perps op {i} must be an object")
        op_obj = dict(entry)
        _assert_ints_within_bits(op_obj, max_bits=max_int_bits, name=f"perps op {i}")
        try:
            op_bytes = bounded_json_utf8_size(op_obj, max_bytes=max_op_bytes)
        except ValueError:
            raise ValueError(f"perps op {i} too large") from None
        except Exception as exc:
            raise ValueError(f"invalid perps op {i}: {exc}") from exc
        total_bytes += op_bytes
        if total_bytes > max_total_ops_bytes:
            raise ValueError("perps ops too large (total bytes limit)")

        module = _require_ascii_token(
            op_obj.get("module"),
            name="perps.module",
            max_len=64,
            allowed=_ASCII_TOKEN_CHARS_MODULE,
        )
        if module != PERP_OP_MODULE:
            raise ValueError(f"invalid perps module: {module}")
        version = _require_ascii_token(
            op_obj.get("version"),
            name="perps.version",
            max_len=64,
            allowed=_ASCII_TOKEN_CHARS_VERSION,
        )
        if version not in (
            PERP_OP_VERSION_V0_1,
            PERP_OP_VERSION_CH2P_V0_2,
            PERP_OP_VERSION_CH2P_V1_0,
            PERP_OP_VERSION_CH3P_V1_1,
            PERP_OP_VERSION_CHNP_V1_2,
        ):
            raise ValueError(f"invalid perps version: {version}")

        market_id = _require_ascii_token(
            op_obj.get("market_id"),
            name="perps.market_id",
            max_len=256,
            allowed=_ASCII_TOKEN_CHARS_MARKET_ID,
        )
        is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        is_ch3p = version == PERP_OP_VERSION_CH3P_V1_1
        is_chnp = version == PERP_OP_VERSION_CHNP_V1_2
        if is_chnp:
            if not market_id.startswith(PERP_CHNP_MARKET_PREFIX):
                raise ValueError(f"clearinghouse_np markets must start with {PERP_CHNP_MARKET_PREFIX!r}")
        elif market_id.startswith(PERP_CHNP_MARKET_PREFIX):
            raise ValueError("non-NP perps markets cannot start with clearinghouse_np prefix")
        else:
            version_prefix_guard = evaluate_perp_market_version_prefix_guard(
                version_is_v0_1=version == PERP_OP_VERSION_V0_1,
                version_is_ch2p=is_ch2p,
                version_is_ch3p=is_ch3p,
                market_has_ch2p_prefix=market_id.startswith(PERP_CH2P_MARKET_PREFIX),
                market_has_ch3p_prefix=market_id.startswith(PERP_CH3P_MARKET_PREFIX),
            )
            if not version_prefix_guard.admission_ok:
                if version_prefix_guard.reject_code == REJECT_INVALID_VERSION:
                    raise ValueError(f"invalid perps version: {version}")
                if version_prefix_guard.reject_code == REJECT_CH2P_PREFIX_MISMATCH:
                    raise ValueError(f"clearinghouse markets must start with {PERP_CH2P_MARKET_PREFIX!r}")
                if version_prefix_guard.reject_code == REJECT_CH3P_PREFIX_MISMATCH:
                    raise ValueError(f"clearinghouse markets must start with {PERP_CH3P_MARKET_PREFIX!r}")
                if version_prefix_guard.reject_code == REJECT_ISOLATED_PREFIX_CONFLICT:
                    raise ValueError("isolated markets cannot start with clearinghouse prefixes")
                raise ValueError("invalid perps version/prefix posture")

        action = _require_ascii_token(
            op_obj.get("action"),
            name="perps.action",
            max_len=64,
            allowed=_ASCII_TOKEN_CHARS_ACTION,
        )

        out.append(PerpOp(market_id=market_id, action=action, version=version, data=op_obj))
    return out


def _kernel_initial_global_state() -> Dict[str, Any]:
    st = perp_epoch_isolated_default_initial_state()
    return {k: (MARK_PRICE_SOURCE_EXTERNAL_MEDIAN if k == "mark_price_source_kind" else st[k]) for k in sorted(PERP_GLOBAL_KEYS)}


def _kernel_initial_account_state() -> PerpAccountState:
    st = perp_epoch_isolated_default_initial_state()
    return PerpAccountState(
        position_base=int(st.get("position_base", 0)),
        entry_price_e8=int(st.get("entry_price_e8", 0)),
        collateral_quote=int(st.get("collateral_quote", 0)),
        funding_paid_cumulative=int(st.get("funding_paid_cumulative", 0)),
        funding_last_applied_epoch=int(st.get("funding_last_applied_epoch", 0)),
        liquidated_this_step=bool(st.get("liquidated_this_step", False)),
    )


def _split_kernel_state(state: Mapping[str, Any]) -> tuple[Dict[str, Any], PerpAccountState]:
    global_state = {
        k: (MARK_PRICE_SOURCE_EXTERNAL_MEDIAN if k == "mark_price_source_kind" else state[k])
        for k in sorted(PERP_GLOBAL_KEYS)
    }
    acct = PerpAccountState(
        position_base=int(state.get("position_base", 0)),
        entry_price_e8=int(state.get("entry_price_e8", 0)),
        collateral_quote=int(state.get("collateral_quote", 0)),
        funding_paid_cumulative=int(state.get("funding_paid_cumulative", 0)),
        funding_last_applied_epoch=int(state.get("funding_last_applied_epoch", 0)),
        liquidated_this_step=bool(state.get("liquidated_this_step", False)),
    )
    return global_state, acct


def _preserve_isolated_shell_global_fields(*, pre_global: Mapping[str, Any], post_global: Dict[str, Any]) -> None:
    post_global["mark_price_source_kind"] = int(
        pre_global.get("mark_price_source_kind", MARK_PRICE_SOURCE_EXTERNAL_MEDIAN)
    )


def _require_operator(config: PerpEngineConfig, *, tx_sender_pubkey: str) -> Optional[str]:
    operator = (config.operator_pubkey or "").strip()
    if not operator:
        return "operator disabled (set TAU_DEX_OPERATOR_PUBKEY)"
    # Compare by decoded pubkey bytes to avoid representation mismatches (0x prefix/case).
    try:
        sender_b = _hex_to_bytes_allow_0x(tx_sender_pubkey, name="tx_sender_pubkey", expected_nbytes=48)
        operator_b = _hex_to_bytes_allow_0x(operator, name="operator_pubkey", expected_nbytes=48)
    except Exception as exc:
        return _safe_error_str(exc)
    if sender_b != operator_b:
        return "operator only"
    return None


def _is_operator(config: PerpEngineConfig, *, tx_sender_pubkey: str) -> bool:
    return _require_operator(config, tx_sender_pubkey=tx_sender_pubkey) is None


def _oracle_adapter_result_get(result: Any, key: str) -> Any:
    if isinstance(result, Mapping):
        return result.get(key)
    return getattr(result, key, None)


def _oracle_adapter_error_summary(result: Any) -> str:
    errors = _oracle_adapter_result_get(result, "errors")
    if isinstance(errors, list):
        parts = [str(x) for x in errors[:3]]
        if parts:
            return "; ".join(parts)
    if isinstance(errors, tuple):
        parts = [str(x) for x in errors[:3]]
        if parts:
            return "; ".join(parts)
    return "bridge verifier rejected"


def _verify_oracle_adapter_bridge(
    config: PerpEngineConfig,
    *,
    data: Mapping[str, Any],
    consumer_module: str,
    action_kind: str,
    expected_query_id: Optional[str] = None,
    expected_profile_id: Optional[str] = None,
    expected_action_id: Optional[str] = None,
    required: bool = False,
) -> tuple[Optional[str], Any]:
    if "oracle_adapter_bridge" not in data:
        if required:
            return f"{action_kind} requires oracle_adapter_bridge", None
        return None, None

    bridge = data.get("oracle_adapter_bridge")
    if not isinstance(bridge, Mapping):
        return "oracle_adapter_bridge must be an object", None
    verifier = config.oracle_adapter_bridge_verifier
    if verifier is None:
        return "oracle_adapter_bridge verifier not configured", None
    try:
        result = verifier(bridge)
    except Exception as exc:
        return f"oracle_adapter_bridge verifier error: {_safe_error_str(exc)}", None

    if _oracle_adapter_result_get(result, "status") != "accepted":
        return f"oracle_adapter_bridge rejected: {_oracle_adapter_error_summary(result)}", None
    result_consumer = _oracle_adapter_result_get(result, "consumer_module")
    result_action = _oracle_adapter_result_get(result, "action_kind")
    if result_consumer != consumer_module:
        return "oracle_adapter_bridge consumer mismatch", None
    if result_action != action_kind:
        return "oracle_adapter_bridge action mismatch", None
    result_query_id = _oracle_adapter_result_get(result, "query_id")
    if expected_query_id is not None and result_query_id != expected_query_id:
        return "oracle_adapter_bridge query mismatch", None
    result_profile_id = _oracle_adapter_result_get(result, "profile_id")
    if expected_profile_id is not None and result_profile_id != expected_profile_id:
        return "oracle_adapter_bridge profile mismatch", None
    result_action_id = _oracle_adapter_result_get(result, "action_id")
    if expected_action_id is not None and result_action_id != expected_action_id:
        return "oracle_adapter_bridge action_id mismatch", None
    return None, result


def _require_oracle_adapter_bridge(
    config: PerpEngineConfig,
    *,
    data: Mapping[str, Any],
    consumer_module: str,
    action_kind: str,
    expected_query_id: Optional[str] = None,
    expected_profile_id: Optional[str] = None,
    expected_action_id: Optional[str] = None,
    required: bool = False,
) -> Optional[str]:
    err, _result = _verify_oracle_adapter_bridge(
        config,
        data=data,
        consumer_module=consumer_module,
        action_kind=action_kind,
        expected_query_id=expected_query_id,
        expected_profile_id=expected_profile_id,
        expected_action_id=expected_action_id,
        required=required,
    )
    return err


def _perps_runtime_oracle_action_id(
    config: PerpEngineConfig,
    *,
    market_id: str,
    action_kind: str,
    market: PerpMarketState,
) -> str:
    global_state = market.global_state
    payload = {
        "schema": "zenodex.oracle.perps_runtime_action_id.v1",
        "chain_id": config.chain_id,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "market_id": market_id,
        "quote_asset": market.quote_asset,
        "now_epoch": int(global_state.get("now_epoch", 0)),
        "clearing_price_epoch": int(global_state.get("clearing_price_epoch", 0)),
        "clearing_price_e8": int(global_state.get("clearing_price_e8", 0)),
        "index_price_e8": int(global_state.get("index_price_e8", 0)),
        "oracle_last_update_epoch": int(global_state.get("oracle_last_update_epoch", 0)),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _perps_liquidate_account_runtime_oracle_action_id(
    config: PerpEngineConfig,
    *,
    market_id: str,
    market: PerpMarketState,
    account_pubkey: str,
    fraction_bps: int,
) -> str:
    global_state = market.global_state
    acct = market.accounts.get(account_pubkey) or _kernel_initial_account_state()
    payload = {
        "schema": "zenodex.oracle.perps_runtime_action_id.v1",
        "chain_id": config.chain_id,
        "consumer_module": "zenodex.perps",
        "action_kind": "liquidate_account",
        "market_id": market_id,
        "quote_asset": market.quote_asset,
        "account_pubkey": str(account_pubkey),
        "fraction_bps": int(fraction_bps),
        "now_epoch": int(global_state.get("now_epoch", 0)),
        "index_price_e8": int(global_state.get("index_price_e8", 0)),
        "oracle_last_update_epoch": int(global_state.get("oracle_last_update_epoch", 0)),
        "position_base": int(acct.position_base),
        "entry_price_e8": int(acct.entry_price_e8),
        "collateral_quote": int(acct.collateral_quote),
        "liquidated_this_step": bool(acct.liquidated_this_step),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _perps_clearinghouse_runtime_oracle_action_id(
    config: PerpEngineConfig,
    *,
    market_id: str,
    action_kind: str,
    market_kind: str,
    quote_asset: str,
    state: Mapping[str, Any],
    participant_pubkeys: tuple[str, ...],
) -> str:
    payload = {
        "schema": "zenodex.oracle.perps_clearinghouse_runtime_action_id.v1",
        "chain_id": config.chain_id,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "market_kind": market_kind,
        "market_id": market_id,
        "quote_asset": quote_asset,
        "participant_pubkeys": list(participant_pubkeys),
        "now_epoch": int(state.get("now_epoch", 0)),
        "clearing_price_epoch": int(state.get("clearing_price_epoch", 0)),
        "clearing_price_e8": int(state.get("clearing_price_e8", 0)),
        "index_price_e8": int(state.get("index_price_e8", 0)),
        "oracle_last_update_epoch": int(state.get("oracle_last_update_epoch", 0)),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _perps_clearinghouse_oracle_pre_state_hash(
    *,
    market_id: str,
    market_kind: str,
    quote_asset: str,
    state: Mapping[str, Any],
    participant_pubkeys: tuple[str, ...],
) -> str:
    payload = {
        "schema": "zenodex.oracle.perps_clearinghouse_pre_state.v1",
        "market_kind": market_kind,
        "market_id": market_id,
        "quote_asset": quote_asset,
        "participant_pubkeys": list(participant_pubkeys),
        "state": dict(state),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _perps_clearinghouse_settle_oracle_runtime_facts(
    config: PerpEngineConfig,
    *,
    market_id: str,
    market_kind: str,
    quote_asset: str,
    state: Mapping[str, Any],
    participant_pubkeys: tuple[str, ...],
) -> dict[str, object]:
    action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=market_id,
        action_kind="settle_epoch",
        market_kind=market_kind,
        quote_asset=quote_asset,
        state=state,
        participant_pubkeys=participant_pubkeys,
    )
    pre_state_hash = _perps_clearinghouse_oracle_pre_state_hash(
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=quote_asset,
        state=state,
        participant_pubkeys=participant_pubkeys,
    )
    facts_payload = {
        "schema": "zenodex.oracle.perps_clearinghouse_settle_epoch_facts.v1",
        "action_id": action_id,
        "market_kind": market_kind,
        "market_id": market_id,
        "participant_count": len(participant_pubkeys),
        "pre_state_hash": pre_state_hash,
        "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
    }
    return {
        "action_facts_hash": semantic_hash(
            "zenodex.perps.clearinghouse.settle_epoch.facts.v1",
            facts_payload,
        ),
        "action_id": action_id,
        "now_epoch": int(state.get("now_epoch", 0)),
        "pre_state_hash": pre_state_hash,
        "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
        # Clearinghouse settlement consumes the published clearing price.
        # `index_price_e8` is retained in the action id for bridge context, but
        # older clearinghouse kernels do not populate it on publish.
        "runtime_value_e8": int(state.get("clearing_price_e8", 0)),
    }


def _authorization_payload(authorization: Mapping[str, Any]) -> Mapping[str, Any]:
    nested = authorization.get("authorization")
    if isinstance(nested, Mapping):
        return nested
    return authorization


def _bind_clearinghouse_authorization_to_bridge(
    authorization: Mapping[str, Any],
    *,
    bridge_result: Any,
) -> Optional[str]:
    # DbC invariant: strict clearinghouse settlement accepts only the typed
    # authorization whose oracle value/receipt metadata came from the accepted
    # adapter bridge result. Missing bridge fields fail closed.
    auth = _authorization_payload(authorization)
    fields = (
        "value_hash",
        "observed_epoch",
        "expires_at_epoch",
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "receipt_graph_root",
    )
    for field in fields:
        if _oracle_adapter_result_get(bridge_result, field) != auth.get(field):
            return f"clearinghouse_settle_oracle_authorization_rejected: oracle_adapter_bridge {field} mismatch"
    return None


def _check_clearinghouse_settle_oracle_authorization(
    config: PerpEngineConfig,
    *,
    data: Mapping[str, Any],
    market_id: str,
    market_kind: str,
    quote_asset: str,
    state: Mapping[str, Any],
    participant_pubkeys: tuple[str, ...],
    bridge_result: Any = None,
) -> Optional[str]:
    authorization_required = bool(config.require_oracle_authorization_for_clearinghouse_settle_epoch)
    authorization = data.get("oracle_authorization")
    if authorization is None:
        if authorization_required:
            return "clearinghouse_settle_oracle_authorization_required"
        return None
    if not isinstance(authorization, Mapping):
        return "clearinghouse settle oracle_authorization must be an object"
    if authorization_required and "oracle_adapter_bridge" not in data:
        return "settle_epoch requires oracle_adapter_bridge"
    if int(state.get("clearing_price_e8", 0)) <= 0:
        return "clearinghouse_settle_oracle_authorization_rejected: clearing_price_e8 must be positive"

    runtime = _perps_clearinghouse_settle_oracle_runtime_facts(
        config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=quote_asset,
        state=state,
        participant_pubkeys=participant_pubkeys,
    )
    try:
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            action_id=str(runtime["action_id"]),
            action_facts_hash=str(runtime["action_facts_hash"]),
            pre_state_hash=str(runtime["pre_state_hash"]),
            query_id=str(runtime["query_id"]),
            runtime_value_e8=int(runtime["runtime_value_e8"]),
            now_epoch=int(runtime["now_epoch"]),
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            max_freshness_window_epochs=2,
        )
    except Exception as exc:
        return f"clearinghouse_settle_oracle_authorization_rejected: {exc}"
    if not bool(result.get("typed_ok", False)):
        errors = result.get("typed_errors") or result.get("opaque_errors") or ["typed authorization rejected"]
        return "clearinghouse_settle_oracle_authorization_rejected: " + "; ".join(str(err) for err in errors)
    if authorization_required:
        return _bind_clearinghouse_authorization_to_bridge(authorization, bridge_result=bridge_result)
    return None


def _oracle_reward_posture_error(config: PerpEngineConfig) -> Optional[str]:
    fields = {
        "oracle_spot_fee_bps": config.oracle_spot_fee_bps,
        "oracle_spot_reward_bps": config.oracle_spot_reward_bps,
        "oracle_spot_reward_safety_margin_bps": config.oracle_spot_reward_safety_margin_bps,
    }
    vals: dict[str, int] = {}
    for name, value in fields.items():
        if not isinstance(value, int) or isinstance(value, bool):
            return f"invalid config: {name} must be an int"
        if value < 0 or value > _BPS_SCALE:
            return f"invalid config: {name} must be in [0, 10000]"
        vals[name] = int(value)
    # Require non-zero fee friction and safety margin for publish-calls.
    # Zero values permit degenerate "no-cost" manipulation posture at the config edge.
    if vals["oracle_spot_fee_bps"] <= 0:
        return "oracle reward posture unsafe: require oracle_spot_fee_bps > 0"
    if vals["oracle_spot_reward_safety_margin_bps"] <= 0:
        return "oracle reward posture unsafe: require oracle_spot_reward_safety_margin_bps > 0"
    if vals["oracle_spot_reward_bps"] > 0 and not (config.oracle_pubkey or "").strip():
        return "oracle reward posture unsafe: require oracle_pubkey when oracle_spot_reward_bps > 0"
    if vals["oracle_spot_reward_bps"] + vals["oracle_spot_reward_safety_margin_bps"] > vals["oracle_spot_fee_bps"]:
        return (
            "oracle reward posture unsafe: require "
            "oracle_spot_reward_bps + oracle_spot_reward_safety_margin_bps <= oracle_spot_fee_bps"
        )
    return None


_SIGNED_FIELD_KEYS = PERP_OP_AUTH_SIGNED_FIELD_KEYS_V1


def _perp_op_signing_dict(op: Mapping[str, Any], *, signer_pubkey: str, nonce: int) -> Dict[str, Any]:
    """Build the canonical dict that is signed for per-op authorization.

    Security goals:
    - Bind the signature to **which action** is being authorized and for **which market**
      (`module`, `version`, `market_id`, `action`).
    - Bind the signature to the **signer identity** (`signer_pubkey`).
    - Provide **replay protection** via a per-signer monotone `nonce`.
    - Avoid ambiguous encodings by signing a canonical JSON byte representation
      (see `canonical_json_bytes` + `domain_sep_bytes`).

    The signed payload intentionally includes only a small, action-specific subset of
    fields (`_SIGNED_FIELD_KEYS[action]`). The API boundary rejects unknown fields,
    and the signing payload acts as a second line of defense against "hidden field"
    confusion.
    """
    return build_perp_op_auth_signing_dict_v1(op, signer_pubkey=signer_pubkey, nonce=nonce)


def _verify_perp_op_signature(
    *,
    config: PerpEngineConfig,
    signer_pubkey: str,
    nonce: int,
    signature: str,
    op: Mapping[str, Any],
    nonces: NonceTable,
    block_timestamp: int,
) -> Optional[str]:
    """Verify and consume a per-op signature (fail-closed).

    Verification steps (in order):
    1) Validate pubkey/signature encoding.
    2) Check deadline against `block_timestamp`.
    3) Enforce the expected next nonce (per signer).
    4) Reconstruct the canonical signing dict and verify the BLS signature over
       a domain-separated hash (bound to `config.chain_id`).
    5) Consume the nonce **only after** successful signature verification.

    Returns:
        None on success, else a human-readable error string.
    """
    if not _BLS_AVAILABLE:
        return "BLS verification not available (install py-ecc)"

    try:
        signer_nonce_key = canonical_hex_fixed_allow_0x(signer_pubkey, nbytes=48, name="signer_pubkey")
    except Exception as exc:
        return str(exc)

    # Deadline check first (cheap).
    try:
        deadline = _require_int(op.get("deadline"), name="deadline", non_negative=True)
    except Exception as exc:
        return _safe_error_str(exc)
    deadline_ok = int(block_timestamp) <= int(deadline)

    # Nonce policy (cheap). We only commit after signature verification, but we
    # validate expected value here to fail quickly.
    nonce_domain_ok = isinstance(nonce, int) and not isinstance(nonce, bool) and 0 < int(nonce) <= _U32_MAX
    expected = int(nonces.get_last(signer_nonce_key)) + 1
    nonce_expected_ok = bool(nonce_domain_ok and int(nonce) == expected)
    precheck = evaluate_perp_submission_auth_gate(
        mode_signed=True,
        mode_sender_bound=False,
        signed_surface_ok=True,
        signer_role_set_ok=True,
        deadline_ok=deadline_ok,
        nonce_domain_ok=nonce_domain_ok,
        nonce_expected_ok=nonce_expected_ok,
        signature_ok=True,
        tx_sender_binding_ok=True,
    )
    if not precheck.admission_ok:
        return perp_submission_auth_gate_error(precheck) or "signed auth rejected"

    try:
        pubkey_bytes = _hex_to_bytes_allow_0x(signer_pubkey, name="signer_pubkey", expected_nbytes=48)
        sig_bytes = _hex_to_bytes_allow_0x(signature, name="signature", expected_nbytes=96)
    except Exception as exc:
        return str(exc)

    try:
        msg_hash = hash_perp_op_auth_message_v1(
            op,
            chain_id=config.chain_id,
            signer_pubkey=signer_pubkey,
            nonce=int(nonce),
        )
        ok = bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))
    except Exception as exc:
        return f"signature verification error: {_safe_error_str(exc)}"
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=True,
        mode_sender_bound=False,
        signed_surface_ok=True,
        signer_role_set_ok=True,
        deadline_ok=deadline_ok,
        nonce_domain_ok=nonce_domain_ok,
        nonce_expected_ok=nonce_expected_ok,
        signature_ok=ok,
        tx_sender_binding_ok=True,
    )
    if not outcome.admission_ok:
        return perp_submission_auth_gate_error(outcome) or "signed auth rejected"

    # Commit nonce consumption after signature verification.
    nonces.set_last(signer_nonce_key, int(nonce))
    return None


def _require_sender_bound_account_pubkey(*, account_pubkey: str, tx_sender_pubkey: str) -> str | None:
    try:
        acct_b = _hex_to_bytes_allow_0x(account_pubkey, name="account_pubkey", expected_nbytes=48)
        sender_b = _hex_to_bytes_allow_0x(tx_sender_pubkey, name="tx_sender_pubkey", expected_nbytes=48)
    except Exception as exc:
        return str(exc)
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=False,
        mode_sender_bound=True,
        signed_surface_ok=True,
        signer_role_set_ok=True,
        deadline_ok=True,
        nonce_domain_ok=True,
        nonce_expected_ok=True,
        signature_ok=True,
        tx_sender_binding_ok=acct_b == sender_b,
    )
    if not outcome.admission_ok:
        return perp_submission_auth_gate_error(outcome) or "sender-bound auth rejected"
    return None


def _evaluate_signed_surface(
    *,
    action_kind: int,
    action: str,
    version_ok: bool,
    unknown_fields_ok: bool,
    distinct_accounts_ok: bool = True,
    market_accounts_match_ok: bool = True,
    net_zero_ok: bool = True,
    idle_leg_ok: bool = True,
    positive_price_ok: bool = True,
) -> str | None:
    outcome = evaluate_perp_signed_surface_guard(
        action_kind=action_kind,
        version_ok=version_ok,
        unknown_fields_ok=unknown_fields_ok,
        distinct_accounts_ok=distinct_accounts_ok,
        market_accounts_match_ok=market_accounts_match_ok,
        net_zero_ok=net_zero_ok,
        idle_leg_ok=idle_leg_ok,
        positive_price_ok=positive_price_ok,
    )
    if outcome.signed_surface_ok:
        return None
    return perp_signed_surface_guard_error(outcome, action=action) or "signed surface invalid"


@dataclass
class _PerpApplyCtx:
    config: PerpEngineConfig
    balances: BalanceTable
    nonces: NonceTable
    markets: Dict[str, PerpAnyMarketState]
    effects: List[Dict[str, Any]]
    tx_sender_pubkey: str
    block_timestamp: int


_CLEAR_BREAKER_OP_FIELDS: frozenset[str] = frozenset({"module", "version", "market_id", "action"})


def _reject_unknown_fields(data: Mapping[str, Any], allowed: set[str] | frozenset[str], *, error: str) -> Optional[str]:
    if set(data.keys()) - allowed:
        return error
    return None


def _operator_gate_error(
    *,
    action_kind: int,
    action: str,
    operator_err: str | None,
    unknown_fields_ok: bool,
    epoch_settled_ok: bool = True,
    positive_price_ok: bool = True,
    positions_flat_ok: bool = True,
    params_object_ok: bool = True,
) -> str | None:
    if operator_err is not None and operator_err != "operator only":
        return operator_err
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=action_kind,
        operator_ok=operator_err is None,
        unknown_fields_ok=unknown_fields_ok,
        sender_binding_ok=True,
        epoch_settled_ok=epoch_settled_ok,
        positive_price_ok=positive_price_ok,
        positions_flat_ok=positions_flat_ok,
        params_object_ok=params_object_ok,
    )
    return perp_runtime_risk_gate_error(outcome, action=action)


def _sender_gate_error(
    *,
    action_kind: int,
    action: str,
    sender_err: str | None,
    unknown_fields_ok: bool,
) -> str | None:
    if sender_err is not None and sender_err != "account_pubkey must match tx sender":
        return sender_err
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=action_kind,
        operator_ok=True,
        unknown_fields_ok=unknown_fields_ok,
        sender_binding_ok=sender_err is None,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )
    return perp_runtime_risk_gate_error(outcome, action=action)


def _ch2p_market_with_state(
    market: PerpClearinghouse2pMarketState, *, state: Dict[str, Any]
) -> PerpClearinghouse2pMarketState:
    return PerpClearinghouse2pMarketState(
        quote_asset=market.quote_asset,
        account_a_pubkey=market.account_a_pubkey,
        account_b_pubkey=market.account_b_pubkey,
        state=state,
    )


def _ch3p_market_with_state(
    market: PerpClearinghouse3pTransferMarketState, *, state: Dict[str, Any]
) -> PerpClearinghouse3pTransferMarketState:
    return PerpClearinghouse3pTransferMarketState(
        quote_asset=market.quote_asset,
        account_a_pubkey=market.account_a_pubkey,
        account_b_pubkey=market.account_b_pubkey,
        account_c_pubkey=market.account_c_pubkey,
        state=state,
    )


def _apply_ch2p_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    ch2p_market: PerpClearinghouse2pMarketState,
) -> str | None:
    config = ctx.config
    balances = ctx.balances
    nonces = ctx.nonces
    tx_sender_pubkey = ctx.tx_sender_pubkey
    block_timestamp = ctx.block_timestamp

    action = op.action
    market_id = op.market_id
    version = op.version
    data = op.data

    if action == "advance_epoch":
        allowed = {"module", "version", "market_id", "action", "delta"}
        unknown = _reject_unknown_fields(data, allowed, error="advance_epoch has unknown fields")
        if unknown is not None:
            return unknown
        # Scheduler rule: only advance when the current epoch is settled.
        if int(ch2p_market.state.get("oracle_last_update_epoch", 0)) != int(ch2p_market.state.get("now_epoch", 0)):
            return "cannot advance epoch before settling current epoch"
        delta = _require_int(data.get("delta"), name="delta", non_negative=True)
        # Hard cap: prevent relayers from jumping many epochs in a single call.
        # This keeps the price publication cadence predictable and avoids "stale by epoch" freezes.
        if delta != 1:
            return "advance_epoch delta must be 1 for clearinghouse markets"
        try:
            next_state, eff = _ch2p_step(ch2p_market.state, tag="advance_epoch", args={"delta": delta})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "publish_clearing_price":
        oracle_pubkey = (config.oracle_pubkey or "").strip()
        if not oracle_pubkey:
            return "oracle signer not configured (set PerpEngineConfig.oracle_pubkey)"

        version_ok = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        if not version_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_PUBLISH_CLEARING_PRICE,
                action=action,
                version_ok=False,
                unknown_fields_ok=True,
            )
            return surface_err or "publish_clearing_price requires a clearinghouse perps.version"

        oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
        oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)

        allowed = {"module", "version", "market_id", "action", "price_e8", "deadline", "oracle_nonce", "oracle_sig"}
        unknown_fields_ok = not (set(data.keys()) - allowed)
        if not unknown_fields_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_PUBLISH_CLEARING_PRICE,
                action=action,
                version_ok=version_ok,
                unknown_fields_ok=False,
            )
            return surface_err or "publish_clearing_price has unknown fields"

        # Cheap validation before signature verification (DoS resistance).
        price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_PUBLISH_CLEARING_PRICE,
            action=action,
            version_ok=version_ok,
            unknown_fields_ok=unknown_fields_ok,
            positive_price_ok=price_e8 > 0,
        )
        if surface_err is not None:
            return surface_err

        sig_err = _verify_perp_op_signature(
            config=config,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
            signature=oracle_sig,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err is not None:
            return f"oracle signature invalid: {sig_err}"

        try:
            next_state, eff = _ch2p_step(ch2p_market.state, tag="publish_clearing_price", args={"price_e8": price_e8})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "settle_epoch":
        allowed = {"module", "version", "market_id", "action", "oracle_adapter_bridge", "oracle_authorization"}
        unknown = _reject_unknown_fields(data, allowed, error="settle_epoch has unknown fields")
        if unknown is not None:
            return unknown
        participant_pubkeys = (ch2p_market.account_a_pubkey, ch2p_market.account_b_pubkey)
        err, bridge_result = _verify_oracle_adapter_bridge(
            config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_clearinghouse_runtime_oracle_action_id(
                config,
                market_id=market_id,
                action_kind="settle_epoch",
                market_kind="clearinghouse_2p_v1",
                quote_asset=ch2p_market.quote_asset,
                state=ch2p_market.state,
                participant_pubkeys=participant_pubkeys,
            ),
            required=config.require_oracle_adapter_for_clearinghouse_settle_epoch,
        )
        if err is not None:
            return err
        err = _check_clearinghouse_settle_oracle_authorization(
            config,
            data=data,
            market_id=market_id,
            market_kind="clearinghouse_2p_v1",
            quote_asset=ch2p_market.quote_asset,
            state=ch2p_market.state,
            participant_pubkeys=participant_pubkeys,
            bridge_result=bridge_result,
        )
        if err is not None:
            return err
        try:
            next_state, eff = _ch2p_step(ch2p_market.state, tag="settle_epoch", args={})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "clear_breaker":
        allowed = {"module", "version", "market_id", "action"}
        unknown = _reject_unknown_fields(data, allowed, error="clear_breaker has unknown fields")
        if unknown is not None:
            return unknown
        if int(ch2p_market.state.get("position_base_a", 0)) != 0 or int(ch2p_market.state.get("position_base_b", 0)) != 0:
            return "cannot clear breaker while positions are open"
        try:
            next_state, eff = _ch2p_step(ch2p_market.state, tag="clear_breaker", args={"auth_ok": True})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "set_market_params":
        operator_ok = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey) is None
        epoch_settled_ok = int(ch2p_market.state.get("oracle_last_update_epoch", 0)) == int(
            ch2p_market.state.get("now_epoch", 0)
        )
        pre_guard = evaluate_perp_clearinghouse_market_params_guard(
            market_kind=MARKET_KIND_CH2P,
            operator_ok=operator_ok,
            epoch_settled_ok=epoch_settled_ok,
            position_base_a=int(ch2p_market.state.get("position_base_a", 0)),
            position_base_b=int(ch2p_market.state.get("position_base_b", 0)),
            position_base_c=0,
            old_liquidation_penalty_bps=int(ch2p_market.state.get("liquidation_penalty_bps", 0)),
            new_liquidation_penalty_bps=int(ch2p_market.state.get("liquidation_penalty_bps", 0)),
            new_maintenance_margin_bps=int(ch2p_market.state.get("maintenance_margin_bps", 0)),
        )
        pre_guard_error = perp_clearinghouse_market_params_guard_error(pre_guard)
        if pre_guard_error is not None:
            return pre_guard_error
        allowed = {"module", "version", "market_id", "action", "params"}
        unknown = _reject_unknown_fields(data, allowed, error="set_market_params has unknown fields")
        if unknown is not None:
            return unknown

        params = data.get("params")
        if not isinstance(params, Mapping):
            return "params must be an object"
        try:
            next_state = _apply_clearinghouse_market_params(
                ch2p_market.state,
                params=params,
                kind="ch2p",
                operator_ok=operator_ok,
                epoch_settled_ok=epoch_settled_ok,
            )
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "params": dict(params)})
        return None

    if action in ("deposit_collateral", "withdraw_collateral"):
        allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
        allowed = allowed_common | {"amount"}
        unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
        if unknown is not None:
            return unknown

        account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
        sender_err = _require_sender_bound_account_pubkey(
            account_pubkey=account_pubkey,
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if sender_err is not None:
            return sender_err

        role = ch2p_market.role_for_pubkey(account_pubkey)
        if role is None:
            return "unknown account_pubkey for this clearinghouse_2p market"

        amount = _require_int(data.get("amount"), name="amount", non_negative=True)
        # Protocol balances are in quote units; the clearinghouse kernel tracks quote-e8 for exact PnL.
        amount_e8 = int(amount) * _E8_SCALE

        if action == "deposit_collateral":
            if balances.get(account_pubkey, ch2p_market.quote_asset) < amount:
                return "insufficient balance for deposit"
            tag = "deposit_collateral_a" if role == "a" else "deposit_collateral_b"
            try:
                next_state, eff = _ch2p_step(
                    ch2p_market.state,
                    tag=tag,
                    args={"amount_e8": amount_e8, "auth_ok": True},
                )
            except Exception as exc:
                return str(exc)
            balances.subtract(account_pubkey, ch2p_market.quote_asset, amount)
        else:
            tag = "withdraw_collateral_a" if role == "a" else "withdraw_collateral_b"
            try:
                next_state, eff = _ch2p_step(
                    ch2p_market.state,
                    tag=tag,
                    args={"amount_e8": amount_e8, "auth_ok": True},
                )
            except Exception as exc:
                return str(exc)
            balances.add(account_pubkey, ch2p_market.quote_asset, amount)

        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff})
        return None

    if action == "set_position_pair":
        version_ok = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        if not version_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_SET_POSITION_PAIR,
                action=action,
                version_ok=False,
                unknown_fields_ok=True,
            )
            return surface_err or "set_position_pair requires perps.version=0.2 or 1.0"

        nonce_a = _require_int_u32_pos(data.get("nonce_a"), name="nonce_a")
        sig_a = _require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096)
        nonce_b = _require_int_u32_pos(data.get("nonce_b"), name="nonce_b")
        sig_b = _require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096)

        allowed = {
            "module",
            "version",
            "market_id",
            "action",
            "account_a_pubkey",
            "account_b_pubkey",
            "new_position_base_a",
            "new_position_base_b",
            "deadline",
            "nonce_a",
            "sig_a",
            "nonce_b",
            "sig_b",
        }
        unknown_fields_ok = not (set(data.keys()) - allowed)
        if not unknown_fields_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_SET_POSITION_PAIR,
                action=action,
                version_ok=version_ok,
                unknown_fields_ok=False,
            )
            return surface_err or "set_position_pair has unknown fields"

        account_a_pubkey = _require_str(
            data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
        )
        account_b_pubkey = _require_str(
            data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
        )
        try:
            a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
            b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
            ma_b = _hex_to_bytes_allow_0x(ch2p_market.account_a_pubkey, name="market.account_a_pubkey", expected_nbytes=48)
            mb_b = _hex_to_bytes_allow_0x(ch2p_market.account_b_pubkey, name="market.account_b_pubkey", expected_nbytes=48)
        except Exception as exc:
            return str(exc)
        market_accounts_match_ok = bool(a_b == ma_b and b_b == mb_b)

        new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
        new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_SET_POSITION_PAIR,
            action=action,
            version_ok=version_ok,
            unknown_fields_ok=unknown_fields_ok,
            market_accounts_match_ok=market_accounts_match_ok,
            net_zero_ok=new_b == -new_a,
        )
        if surface_err is not None:
            return surface_err

        sig_err_a = _verify_perp_op_signature(
            config=config,
            signer_pubkey=account_a_pubkey,
            nonce=nonce_a,
            signature=sig_a,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err_a is not None:
            return f"account_a signature invalid: {sig_err_a}"

        sig_err_b = _verify_perp_op_signature(
            config=config,
            signer_pubkey=account_b_pubkey,
            nonce=nonce_b,
            signature=sig_b,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err_b is not None:
            return f"account_b signature invalid: {sig_err_b}"

        try:
            next_state, eff = _ch2p_step(
                ch2p_market.state,
                tag="set_position_pair",
                args={"new_position_base_a": new_a, "auth_ok": True},
            )
        except Exception as exc:
            return str(exc)

        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    return f"unknown perps action: {action}"


def _apply_ch3p_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    ch3p_market: PerpClearinghouse3pTransferMarketState,
) -> str | None:
    config = ctx.config
    balances = ctx.balances
    nonces = ctx.nonces
    tx_sender_pubkey = ctx.tx_sender_pubkey
    block_timestamp = ctx.block_timestamp

    action = op.action
    market_id = op.market_id
    version = op.version
    data = op.data

    if action == "advance_epoch":
        allowed = {"module", "version", "market_id", "action", "delta"}
        unknown = _reject_unknown_fields(data, allowed, error="advance_epoch has unknown fields")
        if unknown is not None:
            return unknown
        if int(ch3p_market.state.get("oracle_last_update_epoch", 0)) != int(ch3p_market.state.get("now_epoch", 0)):
            return "cannot advance epoch before settling current epoch"
        delta = _require_int(data.get("delta"), name="delta", non_negative=True)
        if delta != 1:
            return "advance_epoch delta must be 1 for clearinghouse markets"
        try:
            next_state, eff = _ch3p_step(ch3p_market.state, tag="advance_epoch", args={"delta": delta})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "publish_clearing_price":
        oracle_pubkey = (config.oracle_pubkey or "").strip()
        if not oracle_pubkey:
            return "oracle signer not configured (set PerpEngineConfig.oracle_pubkey)"

        version_ok = version == PERP_OP_VERSION_CH3P_V1_1
        if not version_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_PUBLISH_CLEARING_PRICE,
                action=action,
                version_ok=False,
                unknown_fields_ok=True,
            )
            return surface_err or "publish_clearing_price requires a clearinghouse perps.version"

        oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
        oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)

        allowed = {"module", "version", "market_id", "action", "price_e8", "deadline", "oracle_nonce", "oracle_sig"}
        unknown_fields_ok = not (set(data.keys()) - allowed)
        if not unknown_fields_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_PUBLISH_CLEARING_PRICE,
                action=action,
                version_ok=version_ok,
                unknown_fields_ok=False,
            )
            return surface_err or "publish_clearing_price has unknown fields"

        # Cheap validation before signature verification (DoS resistance).
        price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_PUBLISH_CLEARING_PRICE,
            action=action,
            version_ok=version_ok,
            unknown_fields_ok=unknown_fields_ok,
            positive_price_ok=price_e8 > 0,
        )
        if surface_err is not None:
            return surface_err

        sig_err = _verify_perp_op_signature(
            config=config,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
            signature=oracle_sig,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err is not None:
            return f"oracle signature invalid: {sig_err}"

        try:
            next_state, eff = _ch3p_step(ch3p_market.state, tag="publish_clearing_price", args={"price_e8": price_e8})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "settle_epoch":
        allowed = {"module", "version", "market_id", "action", "oracle_adapter_bridge", "oracle_authorization"}
        unknown = _reject_unknown_fields(data, allowed, error="settle_epoch has unknown fields")
        if unknown is not None:
            return unknown
        participant_pubkeys = (
            ch3p_market.account_a_pubkey,
            ch3p_market.account_b_pubkey,
            ch3p_market.account_c_pubkey,
        )
        err, bridge_result = _verify_oracle_adapter_bridge(
            config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_clearinghouse_runtime_oracle_action_id(
                config,
                market_id=market_id,
                action_kind="settle_epoch",
                market_kind="clearinghouse_3p_transfer_v1",
                quote_asset=ch3p_market.quote_asset,
                state=ch3p_market.state,
                participant_pubkeys=participant_pubkeys,
            ),
            required=config.require_oracle_adapter_for_clearinghouse_settle_epoch,
        )
        if err is not None:
            return err
        err = _check_clearinghouse_settle_oracle_authorization(
            config,
            data=data,
            market_id=market_id,
            market_kind="clearinghouse_3p_transfer_v1",
            quote_asset=ch3p_market.quote_asset,
            state=ch3p_market.state,
            participant_pubkeys=participant_pubkeys,
            bridge_result=bridge_result,
        )
        if err is not None:
            return err
        try:
            next_state, eff = _ch3p_step(ch3p_market.state, tag="settle_epoch", args={})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "clear_breaker":
        allowed = {"module", "version", "market_id", "action"}
        unknown = _reject_unknown_fields(data, allowed, error="clear_breaker has unknown fields")
        if unknown is not None:
            return unknown
        if (
            int(ch3p_market.state.get("position_base_a", 0)) != 0
            or int(ch3p_market.state.get("position_base_b", 0)) != 0
            or int(ch3p_market.state.get("position_base_c", 0)) != 0
        ):
            return "cannot clear breaker while positions are open"
        try:
            next_state, eff = _ch3p_step(ch3p_market.state, tag="clear_breaker", args={"auth_ok": True})
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    if action == "set_market_params":
        operator_ok = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey) is None
        epoch_settled_ok = int(ch3p_market.state.get("oracle_last_update_epoch", 0)) == int(
            ch3p_market.state.get("now_epoch", 0)
        )
        pre_guard = evaluate_perp_clearinghouse_market_params_guard(
            market_kind=MARKET_KIND_CH3P,
            operator_ok=operator_ok,
            epoch_settled_ok=epoch_settled_ok,
            position_base_a=int(ch3p_market.state.get("position_base_a", 0)),
            position_base_b=int(ch3p_market.state.get("position_base_b", 0)),
            position_base_c=int(ch3p_market.state.get("position_base_c", 0)),
            old_liquidation_penalty_bps=int(ch3p_market.state.get("liquidation_penalty_bps", 0)),
            new_liquidation_penalty_bps=int(ch3p_market.state.get("liquidation_penalty_bps", 0)),
            new_maintenance_margin_bps=int(ch3p_market.state.get("maintenance_margin_bps", 0)),
        )
        pre_guard_error = perp_clearinghouse_market_params_guard_error(pre_guard)
        if pre_guard_error is not None:
            return pre_guard_error
        allowed = {"module", "version", "market_id", "action", "params"}
        unknown = _reject_unknown_fields(data, allowed, error="set_market_params has unknown fields")
        if unknown is not None:
            return unknown

        params = data.get("params")
        if not isinstance(params, Mapping):
            return "params must be an object"
        try:
            next_state = _apply_clearinghouse_market_params(
                ch3p_market.state,
                params=params,
                kind="ch3p",
                operator_ok=operator_ok,
                epoch_settled_ok=epoch_settled_ok,
            )
        except Exception as exc:
            return str(exc)
        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "params": dict(params)})
        return None

    if action in ("deposit_collateral", "withdraw_collateral"):
        allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
        allowed = allowed_common | {"amount"}
        unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
        if unknown is not None:
            return unknown

        account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
        sender_err = _require_sender_bound_account_pubkey(
            account_pubkey=account_pubkey,
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if sender_err is not None:
            return sender_err

        role = ch3p_market.role_for_pubkey(account_pubkey)
        if role is None:
            return "unknown account_pubkey for this clearinghouse_3p market"

        amount = _require_int(data.get("amount"), name="amount", non_negative=True)
        amount_e8 = int(amount) * _E8_SCALE

        if action == "deposit_collateral":
            if balances.get(account_pubkey, ch3p_market.quote_asset) < amount:
                return "insufficient balance for deposit"
            tag = f"deposit_collateral_{role}"
            try:
                next_state, eff = _ch3p_step(
                    ch3p_market.state,
                    tag=tag,
                    args={"amount_e8": amount_e8, "auth_ok": True},
                )
            except Exception as exc:
                return str(exc)
            balances.subtract(account_pubkey, ch3p_market.quote_asset, amount)
        else:
            tag = f"withdraw_collateral_{role}"
            try:
                next_state, eff = _ch3p_step(
                    ch3p_market.state,
                    tag=tag,
                    args={"amount_e8": amount_e8, "auth_ok": True},
                )
            except Exception as exc:
                return str(exc)
            balances.add(account_pubkey, ch3p_market.quote_asset, amount)

        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff})
        return None

    if action == "set_position_triplet":
        version_ok = version == PERP_OP_VERSION_CH3P_V1_1
        if not version_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_SET_POSITION_TRIPLET,
                action=action,
                version_ok=False,
                unknown_fields_ok=True,
            )
            return surface_err or "set_position_triplet requires perps.version=1.1"

        nonce_a = _require_int_u32_pos(data.get("nonce_a"), name="nonce_a")
        sig_a = _require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096)
        nonce_b = _require_int_u32_pos(data.get("nonce_b"), name="nonce_b")
        sig_b = _require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096)
        nonce_c = _require_int_u32_pos(data.get("nonce_c"), name="nonce_c")
        sig_c = _require_str(data.get("sig_c"), name="sig_c", non_empty=True, max_len=4096)

        allowed = {
            "module",
            "version",
            "market_id",
            "action",
            "account_a_pubkey",
            "account_b_pubkey",
            "account_c_pubkey",
            "new_position_base_a",
            "new_position_base_b",
            "new_position_base_c",
            "deadline",
            "nonce_a",
            "sig_a",
            "nonce_b",
            "sig_b",
            "nonce_c",
            "sig_c",
        }
        unknown_fields_ok = not (set(data.keys()) - allowed)
        if not unknown_fields_ok:
            surface_err = _evaluate_signed_surface(
                action_kind=ACTION_SET_POSITION_TRIPLET,
                action=action,
                version_ok=version_ok,
                unknown_fields_ok=False,
            )
            return surface_err or "set_position_triplet has unknown fields"

        account_a_pubkey = _require_str(
            data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
        )
        account_b_pubkey = _require_str(
            data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
        )
        account_c_pubkey = _require_str(
            data.get("account_c_pubkey"), name="account_c_pubkey", non_empty=True, max_len=512
        )
        try:
            a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
            b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
            c_b = _hex_to_bytes_allow_0x(account_c_pubkey, name="account_c_pubkey", expected_nbytes=48)
            ma_b = _hex_to_bytes_allow_0x(ch3p_market.account_a_pubkey, name="market.account_a_pubkey", expected_nbytes=48)
            mb_b = _hex_to_bytes_allow_0x(ch3p_market.account_b_pubkey, name="market.account_b_pubkey", expected_nbytes=48)
            mc_b = _hex_to_bytes_allow_0x(ch3p_market.account_c_pubkey, name="market.account_c_pubkey", expected_nbytes=48)
        except Exception as exc:
            return str(exc)
        market_accounts_match_ok = bool(a_b == ma_b and b_b == mb_b and c_b == mc_b)

        new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
        new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
        new_c = _require_int(data.get("new_position_base_c"), name="new_position_base_c", non_negative=False)
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_SET_POSITION_TRIPLET,
            action=action,
            version_ok=version_ok,
            unknown_fields_ok=unknown_fields_ok,
            market_accounts_match_ok=market_accounts_match_ok,
            net_zero_ok=(new_a + new_b + new_c == 0),
            idle_leg_ok=(new_a == 0 or new_b == 0 or new_c == 0),
        )
        if surface_err is not None:
            return surface_err

        sig_err_a = _verify_perp_op_signature(
            config=config,
            signer_pubkey=account_a_pubkey,
            nonce=nonce_a,
            signature=sig_a,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err_a is not None:
            return f"account_a signature invalid: {sig_err_a}"

        sig_err_b = _verify_perp_op_signature(
            config=config,
            signer_pubkey=account_b_pubkey,
            nonce=nonce_b,
            signature=sig_b,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err_b is not None:
            return f"account_b signature invalid: {sig_err_b}"

        sig_err_c = _verify_perp_op_signature(
            config=config,
            signer_pubkey=account_c_pubkey,
            nonce=nonce_c,
            signature=sig_c,
            op=data,
            nonces=nonces,
            block_timestamp=block_timestamp,
        )
        if sig_err_c is not None:
            return f"account_c signature invalid: {sig_err_c}"

        # Determine which pair is active: the idle account must remain flat.
        if new_c == 0:
            if new_b != -new_a:
                return "clearinghouse_3p AB pair requires new_b == -new_a"
            tag = "set_position_pair_ab"
            args = {"new_position_base_a": new_a, "auth_ok": True}
        elif new_b == 0:
            if new_c != -new_a:
                return "clearinghouse_3p AC pair requires new_c == -new_a"
            tag = "set_position_pair_ac"
            args = {"new_position_base_a": new_a, "auth_ok": True}
        else:
            if new_c != -new_b:
                return "clearinghouse_3p BC pair requires new_c == -new_b"
            tag = "set_position_pair_bc"
            args = {"new_position_base_b": new_b, "auth_ok": True}

        try:
            next_state, eff = _ch3p_step(ch3p_market.state, tag=tag, args=args)
        except Exception as exc:
            return str(exc)

        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
        return None

    return f"unknown perps action: {action}"


def _apply_isolated_advance_epoch(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "delta"}
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_ADVANCE_EPOCH,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
        epoch_settled_ok=int(market.global_state.get("oracle_last_update_epoch", 0))
        == int(market.global_state.get("now_epoch", 0)),
    )
    if gate_error is not None:
        return gate_error
    delta = _require_int(data.get("delta"), name="delta", non_negative=True)

    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="advance_epoch",
        params={"delta": delta},
    )
    if not res.ok or res.state is None:
        return res.error or "advance_epoch rejected"
    new_global, new_dummy = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=new_global)
    if new_dummy != dummy:
        return "internal error: global op mutated account state"
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=new_global,
        accounts=dict(market.accounts),
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
    return None


def _apply_isolated_publish_clearing_price(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "price_e8", "mark_price_source_kind"}
    operator_err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    unknown_fields_ok = not (set(data.keys()) - allowed)
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_PUBLISH_CLEARING_PRICE,
        action=action,
        operator_err=operator_err,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error
    price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
    mark_price_source_kind = _require_int(
        data.get("mark_price_source_kind", MARK_PRICE_SOURCE_EXTERNAL_MEDIAN),
        name="mark_price_source_kind",
        non_negative=True,
    )
    if not is_derivatives_safe_mark_price_source(mark_price_source_kind):
        return "publish_clearing_price requires derivatives-safe mark_price_source_kind"
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_PUBLISH_CLEARING_PRICE,
        action=action,
        operator_err=operator_err,
        unknown_fields_ok=unknown_fields_ok,
        positive_price_ok=price_e8 > 0,
    )
    if gate_error is not None:
        return gate_error

    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="publish_clearing_price",
        params={"price_e8": price_e8},
    )
    if not res.ok or res.state is None:
        return res.error or "publish_clearing_price rejected"
    new_global, new_dummy = _split_kernel_state(res.state)
    new_global["mark_price_source_kind"] = mark_price_source_kind
    if new_dummy != dummy:
        return "internal error: global op mutated account state"
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=new_global,
        accounts=dict(market.accounts),
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
    return None


def _apply_isolated_apply_funding_auto(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action"}
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_APPLY_FUNDING_AUTO,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error

    now_epoch = int(market.global_state.get("now_epoch", 0))
    pre_fee_pool = int(market.global_state.get("fee_pool_quote", 0))
    pre_fee_income = int(market.global_state.get("fee_income", 0))
    pre_insurance_balance = int(market.global_state.get("insurance_balance", 0))
    max_fee_pool = int(perp_epoch_isolated_default_fee_pool_max_quote())
    sorted_accounts = tuple(sorted(market.accounts.items()))
    open_accounts = tuple((pk, acct) for pk, acct in sorted_accounts if int(acct.position_base) != 0)
    net_position_base = sum(int(acct.position_base) for _, acct in open_accounts)

    any_funding_applied_this_epoch = any(int(acct.funding_last_applied_epoch) >= now_epoch for _, acct in open_accounts)

    provisional_gate = evaluate_perp_apply_funding_auto_gate(
        now_epoch=now_epoch,
        mark_price_source_kind=int(market.global_state.get("mark_price_source_kind", 0)),
        clearing_price_seen=bool(market.global_state.get("clearing_price_seen", False)),
        clearing_price_epoch=int(market.global_state.get("clearing_price_epoch", 0)),
        oracle_last_update_epoch=int(market.global_state.get("oracle_last_update_epoch", 0)),
        oracle_seen=bool(market.global_state.get("oracle_seen", False)),
        index_price_e8=int(market.global_state.get("index_price_e8", 0)),
        max_oracle_staleness_epochs=int(market.global_state.get("max_oracle_staleness_epochs", 0)),
        clearing_price_e8=int(market.global_state.get("clearing_price_e8", 0)),
        max_oracle_move_bps=int(market.global_state.get("max_oracle_move_bps", 0)),
        funding_cap_bps=int(market.global_state.get("funding_cap_bps", 0)),
        projected_net_funding_quote=0,
        any_funding_applied_this_epoch=any_funding_applied_this_epoch,
        net_position_base=int(net_position_base),
    )
    new_rate_bps = int(provisional_gate.funding_rate_bps)

    projected_net_funding = 0
    for _, acct in open_accounts:
        funding_payment = _perp_v2_funding_payment(
            acct.position_base,
            int(market.global_state.get("index_price_e8", 0)),
            new_rate_bps,
        )
        projected_net_funding += int(funding_payment)

    funding_gate = evaluate_perp_apply_funding_auto_gate(
        now_epoch=now_epoch,
        mark_price_source_kind=int(market.global_state.get("mark_price_source_kind", 0)),
        clearing_price_seen=bool(market.global_state.get("clearing_price_seen", False)),
        clearing_price_epoch=int(market.global_state.get("clearing_price_epoch", 0)),
        oracle_last_update_epoch=int(market.global_state.get("oracle_last_update_epoch", 0)),
        oracle_seen=bool(market.global_state.get("oracle_seen", False)),
        index_price_e8=int(market.global_state.get("index_price_e8", 0)),
        max_oracle_staleness_epochs=int(market.global_state.get("max_oracle_staleness_epochs", 0)),
        clearing_price_e8=int(market.global_state.get("clearing_price_e8", 0)),
        max_oracle_move_bps=int(market.global_state.get("max_oracle_move_bps", 0)),
        funding_cap_bps=int(market.global_state.get("funding_cap_bps", 0)),
        projected_net_funding_quote=int(projected_net_funding),
        any_funding_applied_this_epoch=any_funding_applied_this_epoch,
        net_position_base=int(net_position_base),
        fee_pool_quote=int(market.global_state.get("fee_pool_quote", 0)),
        fee_income=int(market.global_state.get("fee_income", 0)),
        insurance_balance=int(market.global_state.get("insurance_balance", 0)),
    )
    gate_error = perp_apply_funding_auto_gate_error(funding_gate)
    if gate_error is not None:
        return gate_error

    pre_global = dict(market.global_state)
    expected_account_global = dict(pre_global)
    expected_account_global["funding_rate_bps"] = int(new_rate_bps)
    expected_global = dict(expected_account_global)

    new_accounts: Dict[str, PerpAccountState] = dict(market.accounts)
    applied_accounts = 0
    for pk, acct in open_accounts:
        res = perp_epoch_isolated_default_apply(
            state={**pre_global, **acct.to_kernel_state()},
            action="apply_funding",
            params={"new_rate_bps": int(new_rate_bps), "auth_ok": True},
        )
        if not res.ok or res.state is None:
            return f"apply_funding rejected for account {pk}: {res.error or ''}".strip()
        post_global, post_acct = _split_kernel_state(res.state)
        _preserve_isolated_shell_global_fields(pre_global=pre_global, post_global=post_global)
        if post_global != expected_account_global:
            return "internal error: apply_funding mutated unexpected global fields"
        new_accounts[str(pk)] = post_acct
        applied_accounts += 1

    # Zero-sum funding settlement via a bounded sink. Each open account already
    # received its exact floor-divided funding_payment above, so
    #   Δ(Σ collateral) = -projected_net_funding.
    # Route the net (structural OI imbalance + floor-rounding residual, either
    # sign) into the protocol sink so total value is conserved:
    #   Δ(Σ collateral + fee_pool_quote) = -projected_net + projected_net = 0.
    # Bumping fee_income and insurance_balance by the same delta keeps the
    # persistent identities intact (fee_pool_quote == fee_income;
    # insurance_balance == initial_insurance + fee_income - claims_paid). The
    # gate already rejected (before any mutation) any net that would drive a
    # sink below 0 or above the finite-domain max, so no user account ever
    # absorbs a global accounting residual.
    funding_sink_delta = int(projected_net_funding)
    if funding_sink_delta != 0:
        expected_global["fee_pool_quote"] = int(expected_global["fee_pool_quote"]) + funding_sink_delta
        expected_global["fee_income"] = int(expected_global["fee_income"]) + funding_sink_delta
        expected_global["insurance_balance"] = int(expected_global["insurance_balance"]) + funding_sink_delta

    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=expected_global,
        accounts=new_accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "funding_rate_bps": int(new_rate_bps),
            "mark_price_e8": int(funding_gate.mark_price_e8),
            "accounts_applied": int(applied_accounts),
            "raw_projected_net_funding_quote": int(projected_net_funding),
            "net_position_base": int(net_position_base),
            "funding_sink_delta_quote": funding_sink_delta,
        }
    )
    return None


def _apply_isolated_settle_epoch(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "oracle_authorization", "oracle_adapter_bridge"}
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_SETTLE_EPOCH,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error
    err = _require_oracle_adapter_bridge(
        ctx.config,
        data=data,
        consumer_module="zenodex.perps",
        action_kind="settle_epoch",
        expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
        expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        expected_action_id=_perps_runtime_oracle_action_id(
            ctx.config,
            market_id=market_id,
            action_kind="settle_epoch",
            market=market,
        ),
        required=ctx.config.require_oracle_adapter_for_isolated_settle_epoch,
    )
    if err is not None:
        return err
    oracle_auth_error = _check_isolated_settle_oracle_authorization(ctx=ctx, op=op, market=market)
    if oracle_auth_error is not None:
        return oracle_auth_error

    pre_market = market
    pre_fee_pool = int(pre_market.global_state.get("fee_pool_quote", 0))
    pre_fee_income = int(pre_market.global_state.get("fee_income", 0))
    pre_initial_insurance = int(pre_market.global_state.get("initial_insurance", 0))
    pre_claims_paid = int(pre_market.global_state.get("claims_paid", 0))
    pre_insurance_balance = int(pre_market.global_state.get("insurance_balance", 0))

    # Phase 1: compute the post-epoch *global* update that must be identical across all accounts
    # (oracle/index, breaker flags, clearing-price bookkeeping). This is computed against a dummy
    # account so it cannot depend on account-specific liquidation events.
    dummy = _kernel_initial_account_state()
    res0 = perp_epoch_isolated_default_apply(
        state=pre_market.kernel_state_for_account(dummy),
        action="settle_epoch",
        params={},
    )
    if not res0.ok or res0.state is None:
        return res0.error or "settle_epoch rejected"
    base_global, new_dummy = _split_kernel_state(res0.state)
    _preserve_isolated_shell_global_fields(pre_global=pre_market.global_state, post_global=base_global)
    if new_dummy != dummy:
        return "internal error: settle_epoch mutated dummy account state"

    # Phase 2: settle each account against the *same* pre-global state, but accumulate the
    # liquidation penalty deltas into the global fee/insurance state deterministically
    # (sorted account keys).
    expected_global_no_accum = dict(base_global)
    expected_global_no_accum["fee_pool_quote"] = pre_fee_pool
    expected_global_no_accum["fee_income"] = pre_fee_income
    expected_global_no_accum["insurance_balance"] = pre_insurance_balance

    total_penalty_delta = 0
    new_accounts: Dict[str, PerpAccountState] = {}
    sorted_accounts = tuple(sorted(pre_market.accounts.items()))
    for pk, acct in sorted_accounts:
        # Optimization: when an account is strictly flat and already in a stable
        # post-step shape, settle_epoch cannot change account-local fields.
        # Keep a strict guard and fall back to kernel execution otherwise.
        if (
            int(acct.position_base) == 0
            and int(acct.entry_price_e8) == 0
            and not bool(acct.liquidated_this_step)
            and 0 <= int(acct.collateral_quote) <= MAX_COLLATERAL
        ):
            new_accounts[str(pk)] = acct
            continue

        res = perp_epoch_isolated_default_apply(
            state=pre_market.kernel_state_for_account(acct),
            action="settle_epoch",
            params={},
        )
        if not res.ok or res.state is None:
            return f"settle_epoch rejected for account {pk}: {res.error or ''}".strip()
        post_global, post_acct = _split_kernel_state(res.state)
        _preserve_isolated_shell_global_fields(pre_global=pre_market.global_state, post_global=post_global)

        # All global fields except fee/insurance accumulators must match the dummy-derived post-global.
        post_global_no_accum = dict(post_global)
        post_global_no_accum["fee_pool_quote"] = pre_fee_pool
        post_global_no_accum["fee_income"] = pre_fee_income
        post_global_no_accum["insurance_balance"] = pre_insurance_balance
        if post_global_no_accum != expected_global_no_accum:
            return "internal error: global settle depended on account state"

        post_fee_pool = int(post_global.get("fee_pool_quote", 0))
        post_fee_income = int(post_global.get("fee_income", 0))
        post_insurance = int(post_global.get("insurance_balance", 0))

        fee_pool_delta = post_fee_pool - pre_fee_pool
        fee_income_delta = post_fee_income - pre_fee_income
        insurance_delta = post_insurance - pre_insurance_balance

        if fee_pool_delta < 0 or fee_income_delta < 0 or insurance_delta < 0:
            return "internal error: fee pool decreased during settle_epoch"
        if fee_pool_delta != fee_income_delta or fee_pool_delta != insurance_delta:
            return "internal error: fee/insurance deltas inconsistent"

        total_penalty_delta += fee_pool_delta
        new_accounts[str(pk)] = post_acct

    # Fail-closed on fee-pool overflow beyond the kernel's finite-domain bound.
    max_fee_pool = perp_epoch_isolated_default_fee_pool_max_quote()
    next_fee_pool = pre_fee_pool + total_penalty_delta
    next_fee_income = pre_fee_income + total_penalty_delta
    next_insurance = pre_initial_insurance + next_fee_income - pre_claims_paid
    if next_fee_pool > max_fee_pool or next_fee_income > max_fee_pool or next_insurance > max_fee_pool:
        return "fee/insurance overflow (post-settle)"
    if next_insurance < 0:
        return "insurance negative (post-settle)"

    expected_global_no_accum["fee_pool_quote"] = int(next_fee_pool)
    expected_global_no_accum["fee_income"] = int(next_fee_income)
    expected_global_no_accum["insurance_balance"] = int(next_insurance)
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=expected_global_no_accum,
        accounts=new_accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "fee_pool_delta": int(total_penalty_delta),
            "effects": dict(res0.effects or {}),
        }
    )
    return None


def _apply_isolated_clear_breaker(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_CLEAR_BREAKER,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - _CLEAR_BREAKER_OP_FIELDS),
        positions_flat_ok=not any(int(acct.position_base) != 0 for acct in market.accounts.values()),
    )
    if gate_error is not None:
        return gate_error

    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="clear_breaker",
        params={"auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "clear_breaker rejected"
    new_global, new_dummy = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=new_global)
    if new_dummy != dummy:
        return "internal error: clear_breaker mutated dummy account state"

    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=new_global,
        accounts=dict(market.accounts),
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
    return None


def _apply_isolated_set_market_params(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "params"}
    params = data.get("params")
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_SET_MARKET_PARAMS,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
        epoch_settled_ok=int(market.global_state.get("oracle_last_update_epoch", 0))
        == int(market.global_state.get("now_epoch", 0)),
        params_object_ok=isinstance(params, Mapping),
    )
    if gate_error is not None:
        return gate_error
    if not isinstance(params, Mapping):
        return "params must be an object"
    min_collectible_penalty = _min_collectible_liquidation_penalty_quote(ctx.config)
    next_market = _apply_isolated_market_params(
        market,
        params=params,
        min_collectible_liquidation_penalty_quote=min_collectible_penalty,
    )
    ctx.markets[market_id] = next_market
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "params": dict(params)})
    return None


def _apply_isolated_deposit_collateral(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
    allowed = allowed_common | {"amount"}
    unknown_fields_ok = not (set(data.keys()) - allowed)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_DEPOSIT_COLLATERAL,
        action=action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_DEPOSIT_COLLATERAL,
        action=action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

    amount = _require_int(data.get("amount"), name="amount", non_negative=True)
    if ctx.balances.get(account_pubkey, market.quote_asset) < amount:
        return "insufficient balance for deposit"

    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(acct),
        action="deposit_collateral",
        params={"amount": amount, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "deposit_collateral rejected"
    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    if post_global != market.global_state:
        return "internal error: deposit mutated global state"
    ctx.balances.subtract(account_pubkey, market.quote_asset, amount)
    accounts[account_pubkey] = post_acct
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "effects": dict(res.effects or {}),
        }
    )
    return None


def _apply_isolated_withdraw_collateral(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
    allowed = allowed_common | {"amount"}
    unknown_fields_ok = not (set(data.keys()) - allowed)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_WITHDRAW_COLLATERAL,
        action=action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_WITHDRAW_COLLATERAL,
        action=action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

    amount = _require_int(data.get("amount"), name="amount", non_negative=True)
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(acct),
        action="withdraw_collateral",
        params={"amount": amount, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "withdraw_collateral rejected"
    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    if post_global != market.global_state:
        return "internal error: withdraw mutated global state"
    ctx.balances.add(account_pubkey, market.quote_asset, amount)
    accounts[account_pubkey] = post_acct
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "effects": dict(res.effects or {}),
        }
    )
    return None


def _apply_isolated_deposit_insurance(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "account_pubkey", "amount"}
    if set(data.keys()) - allowed:
        return "deposit_insurance has unknown fields"

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    if sender_err is not None:
        return sender_err

    amount = _require_int(data.get("amount"), name="amount", non_negative=True)
    if amount <= 0:
        return "amount must be positive"
    if ctx.balances.get(account_pubkey, market.quote_asset) < amount:
        return "insufficient balance for insurance deposit"

    # `deposit_insurance` is a global reserve top-up. It must not be blocked by
    # an unrelated distressed account's margin state, so evaluate the isolated
    # kernel against a flat account shell and preserve the account table.
    anchor_account = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(anchor_account),
        action="deposit_insurance",
        params={"amount": amount, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "deposit_insurance rejected"
    post_global, _post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    ctx.balances.subtract(account_pubkey, market.quote_asset, amount)
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=post_global,
        accounts=dict(market.accounts),
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "effects": dict(res.effects or {}),
        }
    )
    return None


def _apply_isolated_set_position(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "account_pubkey", "new_position_base"}
    unknown_fields_ok = not (set(data.keys()) - allowed)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_SET_POSITION,
        action=action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_SET_POSITION,
        action=action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

    new_pos = _require_int(data.get("new_position_base"), name="new_position_base", non_negative=False)
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(acct),
        action="set_position",
        params={"new_position_base": new_pos, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "set_position rejected"
    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    if post_global != market.global_state:
        return "internal error: set_position mutated global state"
    accounts[account_pubkey] = post_acct
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "effects": dict(res.effects or {}),
        }
    )
    return None


def _apply_isolated_partial_liquidate(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    unknown_fields_ok = not (set(data.keys()) - _PARTIAL_LIQUIDATE_ALLOWED_FIELDS)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_PARTIAL_LIQUIDATE,
        action=action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_PARTIAL_LIQUIDATE,
        action=action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

    fraction_bps = _require_int(data.get("fraction_bps", 0), name="fraction_bps", non_negative=True)
    err = _require_oracle_adapter_bridge(
        ctx.config,
        data=data,
        consumer_module="zenodex.perps",
        action_kind="liquidate_account",
        expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
        expected_profile_id=_ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
        expected_action_id=_perps_liquidate_account_runtime_oracle_action_id(
            ctx.config,
            market_id=market_id,
            market=market,
            account_pubkey=account_pubkey,
            fraction_bps=fraction_bps,
        ),
        required=ctx.config.require_oracle_adapter_for_isolated_partial_liquidate,
    )
    if err is not None:
        return err
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(acct),
        action="partial_liquidate",
        params={"fraction_bps": fraction_bps, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "partial_liquidate rejected"
    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    accounts[account_pubkey] = post_acct
    ctx.markets[market_id] = PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=post_global,
        accounts=accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "account_pubkey": account_pubkey,
            "effects": dict(res.effects or {}),
        }
    )
    return None


_PERP_STATEFUL_CONTROL_PARAMS = (
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "funding_cap_bps",
    "min_notional_for_bounty",
)


_MISSING_FIELD = object()


def _int_field(mapping: Mapping[str, Any], key: str, default: object = _MISSING_FIELD) -> int:
    value = mapping.get(key, default)
    if value is _MISSING_FIELD:
        raise ValueError(f"{key} missing")
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be an int")
    return int(value)


def _bool_field(mapping: Mapping[str, Any], key: str, default: object = _MISSING_FIELD) -> bool:
    value = mapping.get(key, default)
    if value is _MISSING_FIELD:
        raise ValueError(f"{key} missing")
    if not isinstance(value, bool):
        raise ValueError(f"{key} must be a bool")
    return bool(value)


def _account_for_shadow(market: PerpMarketState, account_pubkey: object) -> PerpAccountState:
    if isinstance(account_pubkey, str):
        return market.accounts.get(account_pubkey) or _kernel_initial_account_state()
    return _kernel_initial_account_state()


def _funding_auto_shadow_case(pre_market: PerpMarketState, post_market: PerpMarketState) -> dict[str, Any]:
    gs = pre_market.global_state
    return {
        "now_epoch": _int_field(gs, "now_epoch"),
        "rate_bps": _int_field(post_market.global_state, "funding_rate_bps"),
        "index_price_e8": _int_field(gs, "index_price_e8"),
        "maintenance_margin_bps": _int_field(gs, "maintenance_margin_bps"),
        "depeg_buffer_bps": _int_field(gs, "depeg_buffer_bps"),
        "fee_pool_quote": _int_field(gs, "fee_pool_quote"),
        "fee_income": _int_field(gs, "fee_income"),
        "insurance_balance": _int_field(gs, "insurance_balance"),
        "accounts": [
            {
                "key": pk,
                "position_base": int(acct.position_base),
                "collateral_quote": int(acct.collateral_quote),
                "funding_paid_cumulative": int(acct.funding_paid_cumulative),
                "funding_last_applied_epoch": int(acct.funding_last_applied_epoch),
            }
            for pk, acct in sorted(pre_market.accounts.items())
        ],
    }


def _settle_epoch_shadow_case(pre_market: PerpMarketState) -> dict[str, Any]:
    gs = pre_market.global_state
    return {
        "now_epoch": _int_field(gs, "now_epoch"),
        "epoch_phase": _int_field(gs, "epoch_phase"),
        "clearing_price_seen": _bool_field(gs, "clearing_price_seen"),
        "clearing_price_epoch": _int_field(gs, "clearing_price_epoch"),
        "clearing_price_e8": _int_field(gs, "clearing_price_e8"),
        "oracle_last_update_epoch": _int_field(gs, "oracle_last_update_epoch"),
        "oracle_seen": _bool_field(gs, "oracle_seen"),
        "index_price_e8": _int_field(gs, "index_price_e8"),
        "max_oracle_move_bps": _int_field(gs, "max_oracle_move_bps"),
        "maintenance_margin_bps": _int_field(gs, "maintenance_margin_bps"),
        "depeg_buffer_bps": _int_field(gs, "depeg_buffer_bps"),
        "liquidation_penalty_bps": _int_field(gs, "liquidation_penalty_bps"),
        "min_notional_for_bounty": _int_field(gs, "min_notional_for_bounty"),
        "fee_pool_quote": _int_field(gs, "fee_pool_quote"),
        "fee_income": _int_field(gs, "fee_income"),
        "initial_insurance": _int_field(gs, "initial_insurance"),
        "claims_paid": _int_field(gs, "claims_paid"),
        "breaker_active": _bool_field(gs, "breaker_active"),
        "breaker_last_trigger_epoch": _int_field(gs, "breaker_last_trigger_epoch"),
        "accounts": [
            {
                "key": pk,
                "position_base": int(acct.position_base),
                "collateral_quote": int(acct.collateral_quote),
                "entry_price_e8": int(acct.entry_price_e8),
                "liquidated_this_step": bool(acct.liquidated_this_step),
            }
            for pk, acct in sorted(pre_market.accounts.items())
        ],
    }


def _partial_liquidate_shadow_case(pre_market: PerpMarketState, op: PerpOp) -> dict[str, Any]:
    gs = pre_market.global_state
    account_pubkey = op.data.get("account_pubkey")
    acct = _account_for_shadow(pre_market, account_pubkey)
    return {
        "now_epoch": _int_field(gs, "now_epoch"),
        "epoch_phase": _int_field(gs, "epoch_phase"),
        "oracle_last_update_epoch": _int_field(gs, "oracle_last_update_epoch"),
        "max_oracle_staleness_epochs": _int_field(gs, "max_oracle_staleness_epochs"),
        "oracle_seen": _bool_field(gs, "oracle_seen"),
        "index_price_e8": _int_field(gs, "index_price_e8"),
        "position_base": int(acct.position_base),
        "collateral_quote": int(acct.collateral_quote),
        "entry_price_e8": int(acct.entry_price_e8),
        "maintenance_margin_bps": _int_field(gs, "maintenance_margin_bps"),
        "depeg_buffer_bps": _int_field(gs, "depeg_buffer_bps"),
        "liquidation_penalty_bps": _int_field(gs, "liquidation_penalty_bps"),
        "min_notional_for_bounty": _int_field(gs, "min_notional_for_bounty"),
        "fee_pool_quote": _int_field(gs, "fee_pool_quote"),
        "fee_income": _int_field(gs, "fee_income"),
        "initial_insurance": _int_field(gs, "initial_insurance"),
        "claims_paid": _int_field(gs, "claims_paid"),
        "fraction_bps": int(op.data.get("fraction_bps", 0)),
    }


def _account_op_shadow_case(pre_market: PerpMarketState, op: PerpOp) -> dict[str, Any]:
    gs = pre_market.global_state
    account_pubkey = op.data.get("account_pubkey")
    acct = _account_for_shadow(pre_market, account_pubkey)
    return {
        "op": op.action,
        "now_epoch": _int_field(gs, "now_epoch"),
        "epoch_phase": _int_field(gs, "epoch_phase"),
        "oracle_last_update_epoch": _int_field(gs, "oracle_last_update_epoch"),
        "max_oracle_staleness_epochs": _int_field(gs, "max_oracle_staleness_epochs"),
        "oracle_seen": _bool_field(gs, "oracle_seen"),
        "index_price_e8": _int_field(gs, "index_price_e8"),
        "position_base": int(acct.position_base),
        "collateral_quote": int(acct.collateral_quote),
        "entry_price_e8": int(acct.entry_price_e8),
        "maintenance_margin_bps": _int_field(gs, "maintenance_margin_bps"),
        "depeg_buffer_bps": _int_field(gs, "depeg_buffer_bps"),
        "initial_margin_bps": _int_field(gs, "initial_margin_bps"),
        "max_position_abs": _int_field(gs, "max_position_abs"),
        "breaker_active": _bool_field(gs, "breaker_active"),
        "breaker_last_trigger_epoch": _int_field(gs, "breaker_last_trigger_epoch"),
        "amount": int(op.data.get("amount", 0)),
        "new_position_base": int(op.data.get("new_position_base", 0)),
        "all_positions_flat": not any(int(acct.position_base) != 0 for acct in pre_market.accounts.values()),
    }


def _set_market_params_shadow_case(
    ctx: _PerpApplyCtx, pre_market: PerpMarketState, op: PerpOp
) -> dict[str, Any]:
    gs = pre_market.global_state
    params = op.data.get("params")
    if not isinstance(params, Mapping):
        params = {}
    case: dict[str, Any] = {f"cur_{key}": _int_field(gs, key) for key in _PERP_STATEFUL_CONTROL_PARAMS}
    case["cur_funding_rate_bps"] = _int_field(gs, "funding_rate_bps")
    case["index_price_e8"] = _int_field(gs, "index_price_e8")
    case["min_collectible_liquidation_penalty_quote"] = _min_collectible_liquidation_penalty_quote(ctx.config)
    for key, value in params.items():
        if key in _PERP_STATEFUL_CONTROL_PARAMS:
            case[f"upd_{key}"] = int(value)
    case["accounts"] = [
        {
            "position_base": int(acct.position_base),
            "collateral_quote": int(acct.collateral_quote),
        }
        for _, acct in sorted(pre_market.accounts.items())
    ]
    return case


def _perp_stateful_shadow_case(
    *, ctx: _PerpApplyCtx, pre_market: PerpMarketState, post_market: PerpMarketState, op: PerpOp
) -> tuple[str, dict[str, Any]]:
    gs = pre_market.global_state
    if op.action == "advance_epoch":
        return (
            "advance-epoch",
            {
                "now_epoch": _int_field(gs, "now_epoch"),
                "epoch_phase": _int_field(gs, "epoch_phase"),
                "oracle_last_update_epoch": _int_field(gs, "oracle_last_update_epoch"),
                "delta": int(op.data.get("delta", 0)),
            },
        )
    if op.action == "publish_clearing_price":
        return (
            "publish-clearing-price",
            {
                "now_epoch": _int_field(gs, "now_epoch"),
                "epoch_phase": _int_field(gs, "epoch_phase"),
                "clearing_price_seen": _bool_field(gs, "clearing_price_seen"),
                "clearing_price_epoch": _int_field(gs, "clearing_price_epoch"),
                "clearing_price_e8": _int_field(gs, "clearing_price_e8"),
                "oracle_last_update_epoch": _int_field(gs, "oracle_last_update_epoch"),
                "price_e8": int(op.data.get("price_e8", 0)),
            },
        )
    if op.action == "apply_funding_auto":
        return ("funding-auto", _funding_auto_shadow_case(pre_market, post_market))
    if op.action == "settle_epoch":
        return ("settle-epoch", _settle_epoch_shadow_case(pre_market))
    if op.action == "partial_liquidate":
        return ("partial-liquidate", _partial_liquidate_shadow_case(pre_market, op))
    if op.action in {"deposit_collateral", "withdraw_collateral", "set_position", "clear_breaker"}:
        return ("account-op", _account_op_shadow_case(pre_market, op))
    if op.action == "set_market_params":
        return ("set-market-params", _set_market_params_shadow_case(ctx, pre_market, op))
    raise ValueError(f"unsupported perps stateful shadow action: {op.action}")


def _post_account_for_shadow(pre_market: PerpMarketState, post_market: PerpMarketState, op: PerpOp) -> PerpAccountState:
    account_pubkey = op.data.get("account_pubkey")
    if isinstance(account_pubkey, str):
        return post_market.accounts.get(account_pubkey) or _kernel_initial_account_state()
    return _kernel_initial_account_state()


def _perp_stateful_python_doc(
    *, pre_market: PerpMarketState, post_market: PerpMarketState, op: PerpOp
) -> dict[str, Any]:
    pg = post_market.global_state
    if op.action == "advance_epoch":
        return {
            "ok": True,
            "now_epoch": _int_field(pg, "now_epoch"),
            "epoch_phase": _int_field(pg, "epoch_phase"),
            "oracle_last_update_epoch": _int_field(pg, "oracle_last_update_epoch"),
        }
    if op.action == "publish_clearing_price":
        return {
            "ok": True,
            "now_epoch": _int_field(pg, "now_epoch"),
            "epoch_phase": _int_field(pg, "epoch_phase"),
            "clearing_price_seen": _bool_field(pg, "clearing_price_seen"),
            "clearing_price_epoch": _int_field(pg, "clearing_price_epoch"),
            "clearing_price_e8": _int_field(pg, "clearing_price_e8"),
        }
    if op.action == "apply_funding_auto":
        return {
            "ok": True,
            "funding_rate_bps": _int_field(pg, "funding_rate_bps"),
            "fee_pool_quote": _int_field(pg, "fee_pool_quote"),
            "fee_income": _int_field(pg, "fee_income"),
            "insurance_balance": _int_field(pg, "insurance_balance"),
            "accounts": [
                {
                    "key": pk,
                    "position_base": int(acct.position_base),
                    "collateral_quote": int(acct.collateral_quote),
                    "funding_paid_cumulative": int(acct.funding_paid_cumulative),
                    "funding_last_applied_epoch": int(acct.funding_last_applied_epoch),
                }
                for pk, acct in sorted(post_market.accounts.items())
            ],
        }
    if op.action == "settle_epoch":
        return {
            "ok": True,
            "epoch_phase": _int_field(pg, "epoch_phase"),
            "oracle_last_update_epoch": _int_field(pg, "oracle_last_update_epoch"),
            "oracle_seen": _bool_field(pg, "oracle_seen"),
            "index_price_e8": _int_field(pg, "index_price_e8"),
            "breaker_active": _bool_field(pg, "breaker_active"),
            "breaker_last_trigger_epoch": _int_field(pg, "breaker_last_trigger_epoch"),
            "fee_pool_quote": _int_field(pg, "fee_pool_quote"),
            "fee_income": _int_field(pg, "fee_income"),
            "insurance_balance": _int_field(pg, "insurance_balance"),
            "accounts": [
                {
                    "key": pk,
                    "position_base": int(acct.position_base),
                    "collateral_quote": int(acct.collateral_quote),
                    "entry_price_e8": int(acct.entry_price_e8),
                    "liquidated_this_step": bool(acct.liquidated_this_step),
                }
                for pk, acct in sorted(post_market.accounts.items())
            ],
        }
    if op.action == "partial_liquidate":
        acct = _post_account_for_shadow(pre_market, post_market, op)
        return {
            "ok": True,
            "position_base": int(acct.position_base),
            "entry_price_e8": int(acct.entry_price_e8),
            "collateral_quote": int(acct.collateral_quote),
            "fee_pool_quote": _int_field(pg, "fee_pool_quote"),
            "fee_income": _int_field(pg, "fee_income"),
            "insurance_balance": _int_field(pg, "insurance_balance"),
            "liquidated_this_step": bool(acct.liquidated_this_step),
        }
    if op.action in {"deposit_collateral", "withdraw_collateral", "set_position", "clear_breaker"}:
        acct = _post_account_for_shadow(pre_market, post_market, op)
        return {
            "ok": True,
            "position_base": int(acct.position_base),
            "entry_price_e8": int(acct.entry_price_e8),
            "collateral_quote": int(acct.collateral_quote),
            "breaker_active": _bool_field(pg, "breaker_active"),
            "breaker_last_trigger_epoch": _int_field(pg, "breaker_last_trigger_epoch"),
        }
    if op.action == "set_market_params":
        doc: dict[str, Any] = {key: _int_field(pg, key) for key in _PERP_STATEFUL_CONTROL_PARAMS}
        doc["funding_rate_bps"] = _int_field(pg, "funding_rate_bps")
        doc["ok"] = True
        return doc
    raise ValueError(f"unsupported perps stateful shadow action: {op.action}")


def _perp_stateful_docs_agree(python_doc: Any, rust_doc: Any) -> bool:
    if not isinstance(python_doc, Mapping) or not isinstance(rust_doc, Mapping):
        return False
    py_ok = python_doc.get("ok")
    rust_ok = rust_doc.get("ok")
    if not isinstance(py_ok, bool) or not isinstance(rust_ok, bool):
        return False
    if py_ok != rust_ok:
        return False
    if not py_ok:
        return str(python_doc.get("code")) == str(rust_doc.get("code"))

    def same_int(field: str) -> bool:
        return str(int(python_doc[field])) == str(rust_doc.get(field))

    def same_bool(field: str) -> bool:
        return isinstance(rust_doc.get(field), bool) and bool(python_doc[field]) == bool(rust_doc[field])

    for field, value in python_doc.items():
        if field == "ok":
            continue
        if isinstance(value, bool):
            if not same_bool(field):
                return False
        elif isinstance(value, int):
            if not same_int(field):
                return False
        elif isinstance(value, list):
            rust_accounts = rust_doc.get(field)
            if not isinstance(rust_accounts, list) or len(value) != len(rust_accounts):
                return False
            for py_account, rust_account in zip(value, rust_accounts):
                if not isinstance(py_account, Mapping) or not isinstance(rust_account, Mapping):
                    return False
                if str(py_account.get("key")) != str(rust_account.get("key")):
                    return False
                for account_field, account_value in py_account.items():
                    if account_field == "key":
                        continue
                    if isinstance(account_value, bool):
                        if not isinstance(rust_account.get(account_field), bool) or bool(account_value) != bool(
                            rust_account[account_field]
                        ):
                            return False
                    elif str(int(account_value)) != str(rust_account.get(account_field)):
                        return False
        else:
            if value != rust_doc.get(field):
                return False
    return True


# Ops with a full materialized Rust transition (emits the complete post-market
# state + the exact kernel effect payload). For these, the `rust_shadow` check
# compares the full post-state + effects. The Rust-authority dispatcher below
# also uses this set as the eligibility list for isolated-op authority.
_PERP_STATEFUL_MATERIALIZED_ACTIONS: frozenset[str] = frozenset(
    {
        "advance_epoch",
        "publish_clearing_price",
        "settle_epoch",
        "apply_funding_auto",
        "deposit_collateral",
        "withdraw_collateral",
        "set_position",
        "clear_breaker",
        "partial_liquidate",
        "set_market_params",
    }
)

_PERP_STATEFUL_RUST_AUTHORITY_ACTIONS: frozenset[str] = frozenset(
    {
        "advance_epoch",
        "publish_clearing_price",
        "settle_epoch",
        "clear_breaker",
        "set_position",
        "deposit_collateral",
        "withdraw_collateral",
        "set_market_params",
        "apply_funding_auto",
        "partial_liquidate",
    }
)

_PERP_STATEFUL_ACCOUNT_EFFECT_ACTIONS: frozenset[str] = frozenset(
    {"deposit_collateral", "withdraw_collateral", "set_position", "partial_liquidate"}
)

_PERP_STATEFUL_TOP_LEVEL_EFFECT_ACTIONS: frozenset[str] = frozenset(
    {"apply_funding_auto", "set_market_params"}
)

_PARTIAL_LIQUIDATE_ALLOWED_FIELDS: frozenset[str] = frozenset(
    {
        "module",
        "version",
        "market_id",
        "action",
        "account_pubkey",
        "fraction_bps",
        "oracle_adapter_bridge",
    }
)

_PERP_STATEFUL_AUTHORITY_BLOCK_MSG = (
    "perp_stateful action is not eligible for Rust authority; configure rust_shadow "
    "or promote the action"
)

# Design by Contract:
# - Precondition: materialized Rust shadow checks receive a bounded account table.
# - Invariant: oversized shadow inputs never spawn the Rust subprocess.
# - Postcondition: Python remains authoritative in rust_shadow, matching RustUnavailable semantics.
_PERP_STATEFUL_MATERIALIZED_ACCOUNT_LIMIT = 50_000
_PERP_STATEFUL_MATERIALIZED_REQUEST_BYTES_LIMIT = 8 * 1024 * 1024
_PERP_STATEFUL_MATERIALIZED_RESPONSE_BYTES_LIMIT = 8 * 1024 * 1024

_ISOLATED_GLOBAL_BOOL_KEYS: frozenset[str] = frozenset(
    {"breaker_active", "clearing_price_seen", "oracle_seen"}
)

_ISOLATED_ACCOUNT_DOC_KEYS: frozenset[str] = frozenset(
    {
        "key",
        "position_base",
        "collateral_quote",
        "entry_price_e8",
        "funding_paid_cumulative",
        "funding_last_applied_epoch",
        "liquidated_this_step",
    }
)


def _require_decimal_string_int(value: Any, *, name: str) -> int:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a decimal string")
    digits = value[1:] if value.startswith("-") else value
    if not digits or not digits.isdigit():
        raise ValueError(f"{name} must be a decimal string")
    return int(value)


def _isolated_global_doc(global_state: Mapping[str, Any]) -> dict[str, Any]:
    """Full isolated global-state doc: int keys as decimal strings, bools as bools."""
    out: dict[str, Any] = {}
    for key in sorted(PERP_GLOBAL_KEYS):
        if key in _ISOLATED_GLOBAL_BOOL_KEYS:
            out[key] = _bool_field(global_state, key)
        else:
            out[key] = str(_int_field(global_state, key))
    return out


def _isolated_accounts_doc(accounts: Mapping[str, PerpAccountState]) -> list[dict[str, Any]]:
    return [
        {
            "key": pk,
            "position_base": str(int(acct.position_base)),
            "collateral_quote": str(int(acct.collateral_quote)),
            "entry_price_e8": str(int(acct.entry_price_e8)),
            "funding_paid_cumulative": str(int(acct.funding_paid_cumulative)),
            "funding_last_applied_epoch": str(int(acct.funding_last_applied_epoch)),
            "liquidated_this_step": bool(acct.liquidated_this_step),
        }
        for pk, acct in sorted(accounts.items())
    ]


def _market_from_materialized_post(post: Mapping[str, Any]) -> PerpMarketState:
    """Convert Rust `perp-isolated-op` accepted post-state into a Python market.

    This is intentionally strict because it is the future Rust-authority commit
    boundary: missing, duplicate, or mis-typed fields must fail closed.
    """
    if not isinstance(post, Mapping):
        raise ValueError("materialized post must be an object")
    quote_asset = _require_str(post.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
    global_doc = post.get("global_state")
    if not isinstance(global_doc, Mapping):
        raise ValueError("materialized post.global_state must be an object")
    if set(global_doc.keys()) != set(PERP_GLOBAL_KEYS):
        raise ValueError("materialized post.global_state keys mismatch")

    global_state: dict[str, Any] = {}
    for key in sorted(PERP_GLOBAL_KEYS):
        value = global_doc[key]
        if key in _ISOLATED_GLOBAL_BOOL_KEYS:
            if not isinstance(value, bool):
                raise ValueError(f"materialized post.global_state[{key}] must be bool")
            global_state[key] = value
        else:
            global_state[key] = _require_decimal_string_int(
                value,
                name=f"materialized post.global_state[{key}]",
            )

    accounts_doc = post.get("accounts")
    if not isinstance(accounts_doc, list):
        raise ValueError("materialized post.accounts must be a list")
    accounts: dict[str, PerpAccountState] = {}
    for raw_account in accounts_doc:
        if not isinstance(raw_account, Mapping):
            raise ValueError("materialized post account must be an object")
        if set(raw_account.keys()) != _ISOLATED_ACCOUNT_DOC_KEYS:
            raise ValueError("materialized post account keys mismatch")
        key = _require_str(raw_account.get("key"), name="account.key", non_empty=True, max_len=512)
        if key in accounts:
            raise ValueError("materialized post has duplicate account key")
        liquidated = raw_account.get("liquidated_this_step")
        if not isinstance(liquidated, bool):
            raise ValueError("materialized post account liquidated_this_step must be bool")
        accounts[key] = PerpAccountState(
            position_base=_require_decimal_string_int(raw_account["position_base"], name="account.position_base"),
            collateral_quote=_require_decimal_string_int(
                raw_account["collateral_quote"],
                name="account.collateral_quote",
            ),
            entry_price_e8=_require_decimal_string_int(raw_account["entry_price_e8"], name="account.entry_price_e8"),
            funding_paid_cumulative=_require_decimal_string_int(
                raw_account["funding_paid_cumulative"],
                name="account.funding_paid_cumulative",
            ),
            funding_last_applied_epoch=_require_decimal_string_int(
                raw_account["funding_last_applied_epoch"],
                name="account.funding_last_applied_epoch",
            ),
            liquidated_this_step=liquidated,
        )

    return PerpMarketState(quote_asset=quote_asset, global_state=global_state, accounts=accounts)


def _materialized_shadow_account_count_bounded(pre_market: PerpMarketState) -> bool:
    """Return whether full-state Rust shadow materialization is resource-bounded."""
    return len(pre_market.accounts) <= _PERP_STATEFUL_MATERIALIZED_ACCOUNT_LIMIT


def _materialized_shadow_request_bounded(request: Mapping[str, Any]) -> bool:
    """Return whether the request can fit through the Rust bridge stdin cap."""
    return len(json.dumps(request).encode()) <= _PERP_STATEFUL_MATERIALIZED_REQUEST_BYTES_LIMIT


def _materialized_shadow_response_bounded(python_doc: Mapping[str, Any]) -> bool:
    """Return whether the accepted Rust materializer response should fit stdout."""
    response_shape = {
        "accept": True,
        "post": {
            "quote_asset": python_doc.get("quote_asset"),
            "global_state": python_doc.get("global_state"),
            "accounts": python_doc.get("accounts"),
        },
        "effects": python_doc.get("effects"),
    }
    try:
        bounded_json_utf8_size(
            response_shape,
            max_bytes=_PERP_STATEFUL_MATERIALIZED_RESPONSE_BYTES_LIMIT,
        )
    except (TypeError, ValueError):
        return False
    return True


def _isolated_op_integration_facts(
    *,
    ctx: _PerpApplyCtx,
    pre_market: PerpMarketState,
    op: PerpOp,
    trust_authoritative_acceptance: bool = False,
) -> dict[str, Any]:
    """Compute the explicit non-kernel facts consumed by the Rust materializer.

    These facts are evaluated from the pre-state integration shell. Rust may
    consume them, but it must not reimplement operator keys, sender binding,
    wallet balances, or oracle bridge verification.

    DbC precondition: ``trust_authoritative_acceptance`` may only be true
    after the authoritative Python handler has accepted this operation. In
    that mode, oracle facts are derived from the accepted handler result rather
    than re-running side-effectful bridge verification.
    """
    account_pubkey = op.data.get("account_pubkey")
    account_key = account_pubkey if isinstance(account_pubkey, str) else ""
    all_flat = all(int(acct.position_base) == 0 for acct in pre_market.accounts.values())

    oracle_adapter_ok = True
    oracle_authorization_ok = True
    if trust_authoritative_acceptance:
        oracle_adapter_ok = True
        oracle_authorization_ok = True
    elif op.action == "settle_epoch":
        adapter_err = _require_oracle_adapter_bridge(
            ctx.config,
            data=op.data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_runtime_oracle_action_id(
                ctx.config,
                market_id=op.market_id,
                action_kind="settle_epoch",
                market=pre_market,
            ),
            required=ctx.config.require_oracle_adapter_for_isolated_settle_epoch,
        )
        oracle_adapter_ok = adapter_err is None
        oracle_authorization_ok = (
            _check_isolated_settle_oracle_authorization(ctx=ctx, op=op, market=pre_market) is None
        )
    elif op.action == "partial_liquidate":
        try:
            fraction_bps = _require_int(
                op.data.get("fraction_bps", 0),
                name="fraction_bps",
                non_negative=True,
            )
        except Exception:
            fraction_bps = 0
        adapter_err = _require_oracle_adapter_bridge(
            ctx.config,
            data=op.data,
            consumer_module="zenodex.perps",
            action_kind="liquidate_account",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            expected_action_id=_perps_liquidate_account_runtime_oracle_action_id(
                ctx.config,
                market_id=op.market_id,
                market=pre_market,
                account_pubkey=account_key,
                fraction_bps=int(fraction_bps),
            ),
            required=ctx.config.require_oracle_adapter_for_isolated_partial_liquidate,
        )
        oracle_adapter_ok = adapter_err is None

    sender_bound_ok = False
    if account_key:
        sender_bound_ok = (
            _require_sender_bound_account_pubkey(
                account_pubkey=account_key,
                tx_sender_pubkey=ctx.tx_sender_pubkey,
            )
            is None
        )

    return {
        "operator_ok": _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey) is None,
        "sender_bound_ok": bool(sender_bound_ok),
        "all_positions_flat": bool(all_flat),
        "balance_available": str(int(ctx.balances.get(account_key, pre_market.quote_asset))) if account_key else "0",
        "oracle_adapter_ok": bool(oracle_adapter_ok),
        "oracle_authorization_ok": bool(oracle_authorization_ok),
        "min_collectible_liquidation_penalty_quote": str(
            _min_collectible_liquidation_penalty_quote(ctx.config)
        ),
    }


def _reject_unknown_materialized_op_fields(op: PerpOp) -> Optional[str]:
    """Reject raw fields that would be stripped before Rust validation.

    Design by Contract:
    - Precondition: ``op.data`` is the original operation payload.
    - Invariant: promoted Rust-authority ops fail closed on Python-equivalent
      unknown-field boundaries before sanitized Rust request shaping.
    - Postcondition: a partial liquidation with any non-allowlisted raw field is
      never committed by pure Rust authority.
    """
    if op.action != "partial_liquidate":
        return None
    return _reject_unknown_fields(
        op.data,
        set(_PARTIAL_LIQUIDATE_ALLOWED_FIELDS),
        error="partial_liquidate has unknown fields",
    )


def _build_isolated_op_request(
    *, pre_market: PerpMarketState, op: PerpOp, integration_facts: Mapping[str, Any]
) -> dict[str, Any]:
    """Build the full `perp-isolated-op` request from the pre-market, op, and the
    explicit integration facts. In the current live path this is used after
    Python has accepted an op, but the facts are still computed from the pre-state
    shell instead of being hardcoded. That keeps the request boundary ready for a
    later Rust-authority inversion."""
    unknown_fields_error = _reject_unknown_materialized_op_fields(op)
    if unknown_fields_error is not None:
        raise ValueError(unknown_fields_error)

    op_obj: dict[str, Any] = {"action": op.action}
    if op.action == "advance_epoch":
        op_obj["delta"] = str(_require_int(op.data.get("delta", 0), name="delta", non_negative=True))
    elif op.action == "publish_clearing_price":
        op_obj["price_e8"] = str(
            _require_int(op.data.get("price_e8", 0), name="price_e8", non_negative=True)
        )
        # Forward mark_price_source_kind so the Rust materializer sees what the
        # Python authority (_apply_isolated_publish_clearing_price) used. Without
        # this the bridge silently dropped the field, the Rust shadow fell back to
        # its external-median default, and a forwarded non-default source could
        # diverge under a future rust-authority inversion (Gemini F1). Forwarded
        # only when present, matching the op's actual payload; Rust defaults to
        # external median when absent, exactly as Python does.
        if "mark_price_source_kind" in op.data:
            op_obj["mark_price_source_kind"] = str(
                _require_int(
                    op.data.get("mark_price_source_kind"),
                    name="mark_price_source_kind",
                    non_negative=True,
                )
            )
    elif op.action in ("deposit_collateral", "withdraw_collateral"):
        op_obj["account_pubkey"] = _require_str(
            op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512
        )
        op_obj["amount"] = str(
            _require_int(op.data.get("amount", 0), name="amount", non_negative=True)
        )
    elif op.action == "set_position":
        op_obj["account_pubkey"] = _require_str(
            op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512
        )
        # new_position_base is signed (a short is negative): non_negative=False.
        op_obj["new_position_base"] = str(
            _require_int(op.data.get("new_position_base", 0), name="new_position_base", non_negative=False)
        )
    elif op.action == "partial_liquidate":
        op_obj["account_pubkey"] = _require_str(
            op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512
        )
        # fraction_bps in [0, 10000]; 0 => auto-compute the minimum viable close.
        op_obj["fraction_bps"] = str(
            _require_int(op.data.get("fraction_bps", 0), name="fraction_bps", non_negative=True)
        )
    elif op.action == "apply_funding_auto":
        pass
    elif op.action == "clear_breaker":
        # DbC precondition: do not let the bridge sanitize privileged no-param ops.
        unknown = _reject_unknown_fields(
            op.data, _CLEAR_BREAKER_OP_FIELDS, error="clear_breaker has unknown fields"
        )
        if unknown is not None:
            raise ValueError(unknown)
    elif op.action == "set_market_params":
        params = op.data.get("params")
        if not isinstance(params, Mapping):
            raise ValueError("params must be an object")
        op_obj["params"] = _isolated_set_market_params_wire_doc(params)
    # clear_breaker (and the global ops settle_epoch) carry no op params; the
    # materializer reads everything it needs from global_state + the all_positions_flat
    # fact, so the bare {"action": ...} op object above is complete.
    return {
        "schema": "zenodex/perp_isolated_op/v1",
        "version": 1,
        "quote_asset": pre_market.quote_asset,
        "global_state": _isolated_global_doc(pre_market.global_state),
        "accounts": _isolated_accounts_doc(pre_market.accounts),
        "op": op_obj,
        "facts": dict(integration_facts),
    }


def _isolated_set_market_params_wire_doc(params: Mapping[str, Any]) -> dict[str, Any]:
    """Serialize the set-market overlay into the Rust materializer wire shape.

    Known control params keep Python's semantic input contract: callers must
    provide ints, and the bridge converts them to decimal strings for Rust.
    Unknown keys are left untouched so the materializer rejects them as unknown
    before value parsing, matching the semantic handler's reject order.
    """
    out: dict[str, Any] = {}
    for key, value in params.items():
        if not isinstance(key, str):
            raise ValueError("params keys must be strings")
        if key not in _ISOLATED_CONTROL_PARAM_BOUNDS:
            out[key] = value
            continue
        out[key] = str(_require_int(value, name=f"params.{key}", non_negative=True))
    return out


def _perp_stateful_full_doc(
    post_market: PerpMarketState, python_effect: Mapping[str, Any]
) -> dict[str, Any]:
    """The Python full post-market doc, in the Rust `post` shape, plus the exact
    kernel effect payload, for full state + effect parity comparison."""
    return {
        "accept": True,
        "quote_asset": post_market.quote_asset,
        "global_state": _isolated_global_doc(post_market.global_state),
        "accounts": _isolated_accounts_doc(post_market.accounts),
        "effects": dict(python_effect),
    }


def _materialized_effect_payload(effect: Mapping[str, Any]) -> dict[str, Any]:
    """Return the semantic effect payload Rust materialization must reproduce."""
    nested = effect.get("effects")
    if isinstance(nested, Mapping):
        return dict(nested)
    return {
        key: value
        for key, value in effect.items()
        if key not in {"i", "market_id", "action"}
    }


def _effects_agree(python_effect: Any, rust_effect: Any) -> bool:
    """Exact effect parity: identical key set; bool fields strict, int fields
    coerced (Python emits JSON numbers, Rust emits decimal strings), event string
    equal. A receipt/effect drift fails closed even when post-state still matches."""

    def values_agree(py_val: Any, rust_val: Any) -> bool:
        if isinstance(py_val, bool):
            return isinstance(rust_val, bool) and py_val == rust_val
        if isinstance(py_val, int):
            try:
                return int(str(rust_val)) == py_val
            except (TypeError, ValueError):
                return False
        if isinstance(py_val, Mapping):
            if not isinstance(rust_val, Mapping) or set(py_val.keys()) != set(rust_val.keys()):
                return False
            return all(values_agree(py_val[key], rust_val.get(key)) for key in py_val)
        if isinstance(py_val, list):
            if not isinstance(rust_val, list) or len(py_val) != len(rust_val):
                return False
            return all(values_agree(a, b) for a, b in zip(py_val, rust_val))
        return str(py_val) == str(rust_val)

    if not isinstance(python_effect, Mapping) or not isinstance(rust_effect, Mapping):
        return False
    if set(python_effect.keys()) != set(rust_effect.keys()):
        return False
    for key, py_val in python_effect.items():
        if not values_agree(py_val, rust_effect.get(key)):
            return False
    return True


def _full_post_markets_agree(python_doc: Any, rust_response: Any) -> bool:
    """Full post-market parity: accept, quote_asset, every global key, every account,
    and the exact kernel effect payload."""
    if not isinstance(python_doc, Mapping) or not isinstance(rust_response, Mapping):
        return False
    if set(rust_response.keys()) != {"accept", "post", "effects"}:
        return False
    if rust_response.get("accept") is not True:
        return False
    post = rust_response.get("post")
    if not isinstance(post, Mapping):
        return False
    if set(post.keys()) != {"quote_asset", "global_state", "accounts"}:
        return False
    if str(python_doc.get("quote_asset")) != str(post.get("quote_asset")):
        return False
    rust_gs = post.get("global_state")
    if not isinstance(rust_gs, Mapping):
        return False
    python_gs = python_doc.get("global_state")
    if not isinstance(python_gs, Mapping):
        return False
    if set(rust_gs.keys()) != set(python_gs.keys()):
        return False
    for key, value in python_gs.items():
        rust_value = rust_gs.get(key)
        if isinstance(value, bool):
            if not isinstance(rust_value, bool) or value != rust_value:
                return False
        elif str(value) != str(rust_value):
            return False
    rust_accounts = post.get("accounts")
    python_accounts = python_doc.get("accounts")
    if not isinstance(python_accounts, list) or not isinstance(rust_accounts, list):
        return False
    if len(rust_accounts) != len(python_accounts):
        return False
    rust_by_key = {a.get("key"): a for a in rust_accounts if isinstance(a, Mapping)}
    if len(rust_by_key) != len(rust_accounts):
        return False
    for py_acct in python_accounts:
        rust_acct = rust_by_key.get(py_acct["key"])
        if not isinstance(rust_acct, Mapping):
            return False
        if set(rust_acct.keys()) != set(py_acct.keys()):
            return False
        for field, value in py_acct.items():
            if field == "key":
                continue
            rust_value = rust_acct.get(field)
            if isinstance(value, bool):
                if not isinstance(rust_value, bool) or value != rust_value:
                    return False
            elif str(value) != str(rust_value):
                return False
    if not _effects_agree(python_doc.get("effects"), rust_response.get("effects")):
        return False
    return True


def _materialized_responses_agree(python_response: Any, rust_response: Any) -> bool:
    if not isinstance(python_response, Mapping) or not isinstance(rust_response, Mapping):
        return False
    py_accept = python_response.get("accept")
    rust_accept = rust_response.get("accept")
    if not isinstance(py_accept, bool) or not isinstance(rust_accept, bool):
        return False
    if py_accept != rust_accept:
        return False
    if not py_accept:
        return str(python_response.get("reject_reason")) == str(rust_response.get("reject_reason"))
    return _full_post_markets_agree(python_response, rust_response)


def _python_shadow_materialized_isolated_op(
    *, ctx: _PerpApplyCtx, i: int, op: PerpOp, pre_market: PerpMarketState
) -> dict[str, Any]:
    handler = _ISOLATED_ACTION_HANDLERS.get(op.action)
    if handler is None:
        return {"accept": False, "reject_reason": f"unknown perps action: {op.action}"}
    shadow_ctx = _PerpApplyCtx(
        config=ctx.config,
        balances=_copy_balance_table(ctx.balances),
        nonces=_copy_nonce_table(ctx.nonces),
        markets=dict(ctx.markets),
        effects=[],
        tx_sender_pubkey=ctx.tx_sender_pubkey,
        block_timestamp=ctx.block_timestamp,
    )
    err = handler(shadow_ctx, i=i, op=op, market=pre_market)
    if err is not None:
        return {"accept": False, "reject_reason": err}
    python_effect = _materialized_effect_payload(shadow_ctx.effects[-1]) if shadow_ctx.effects else {}
    return _perp_stateful_full_doc(
        shadow_ctx.markets[op.market_id],
        python_effect,
    )


def _materialized_settle_epoch_effect_doc(
    *, pre_market: PerpMarketState, post_market: PerpMarketState, effects: Mapping[str, Any]
) -> tuple[dict[str, Any] | None, str | None]:
    pre_fee_pool = int(pre_market.global_state.get("fee_pool_quote", 0))
    pre_fee_income = int(pre_market.global_state.get("fee_income", 0))
    pre_insurance_balance = int(pre_market.global_state.get("insurance_balance", 0))
    post_fee_pool = int(post_market.global_state.get("fee_pool_quote", 0))
    post_fee_income = int(post_market.global_state.get("fee_income", 0))
    post_insurance = int(post_market.global_state.get("insurance_balance", 0))

    fee_pool_delta = post_fee_pool - pre_fee_pool
    fee_income_delta = post_fee_income - pre_fee_income
    insurance_delta = post_insurance - pre_insurance_balance
    if fee_pool_delta < 0 or fee_income_delta < 0 or insurance_delta < 0:
        return None, "internal error: fee pool decreased during settle_epoch"
    if fee_pool_delta != fee_income_delta or fee_pool_delta != insurance_delta:
        return None, "internal error: fee/insurance deltas inconsistent"
    return {"fee_pool_delta": int(fee_pool_delta), "effects": dict(effects)}, None


def _commit_materialized_rust_accept(
    *,
    ctx: _PerpApplyCtx,
    i: int,
    op: PerpOp,
    pre_market: PerpMarketState,
    rust_response: Mapping[str, Any],
) -> Optional[str]:
    if not bool(rust_response.get("accept")):
        return str(rust_response.get("reject_reason") or "perp_stateful rust authority rejected")
    post = rust_response.get("post")
    if not isinstance(post, Mapping):
        return "perp_stateful rust authority malformed accepted post"
    effects = rust_response.get("effects")
    if not isinstance(effects, Mapping):
        return "perp_stateful rust authority malformed accepted effects"
    try:
        post_market = _market_from_materialized_post(post)
    except Exception as exc:
        return f"perp_stateful rust authority malformed post: {_safe_error_str(exc)}"
    ctx.markets[op.market_id] = post_market
    effect_doc: dict[str, Any] = {"i": i, "market_id": op.market_id, "action": op.action}
    if op.action in _PERP_STATEFUL_ACCOUNT_EFFECT_ACTIONS:
        try:
            effect_doc["account_pubkey"] = _require_str(
                op.data.get("account_pubkey"),
                name="account_pubkey",
                non_empty=True,
                max_len=512,
            )
        except Exception as exc:
            return _safe_error_str(exc)
    if op.action == "settle_epoch":
        settle_effect, err = _materialized_settle_epoch_effect_doc(
            pre_market=pre_market,
            post_market=post_market,
            effects=effects,
        )
        if err is not None:
            return err
        effect_doc.update(settle_effect or {})
    elif op.action in _PERP_STATEFUL_TOP_LEVEL_EFFECT_ACTIONS:
        effect_doc.update(dict(effects))
    else:
        effect_doc["effects"] = dict(effects)
    if op.action == "deposit_collateral":
        try:
            amount = _require_int(op.data.get("amount"), name="amount", non_negative=True)
            ctx.balances.subtract(str(effect_doc["account_pubkey"]), post_market.quote_asset, amount)
        except Exception as exc:
            return _safe_error_str(exc)
    elif op.action == "withdraw_collateral":
        try:
            amount = _require_int(op.data.get("amount"), name="amount", non_negative=True)
            ctx.balances.add(str(effect_doc["account_pubkey"]), post_market.quote_asset, amount)
        except Exception as exc:
            return _safe_error_str(exc)
    ctx.effects.append(effect_doc)
    return None


def _apply_materialized_isolated_op_rust_authority(
    *, ctx: _PerpApplyCtx, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    from src.runtime.authority import AuthorityError, AuthorityMode, active_mode, decide
    from src.runtime.rust_invoker import perp_isolated_op

    if op.action not in _PERP_STATEFUL_RUST_AUTHORITY_ACTIONS:
        return _PERP_STATEFUL_AUTHORITY_BLOCK_MSG
    if not _materialized_shadow_account_count_bounded(market):
        return "perp_stateful rust authority account table too large"

    mode = active_mode(PERP_STATEFUL_SURFACE)
    integration_facts = _isolated_op_integration_facts(ctx=ctx, pre_market=market, op=op)
    try:
        request = _build_isolated_op_request(
            pre_market=market,
            op=op,
            integration_facts=integration_facts,
        )
    except Exception as exc:
        return _safe_error_str(exc)
    if not _materialized_shadow_request_bounded(request):
        return "perp_stateful rust authority request too large"

    try:
        decision = decide(
            PERP_STATEFUL_SURFACE,
            mode,
            python_fn=lambda: _python_shadow_materialized_isolated_op(
                ctx=ctx,
                i=i,
                op=op,
                pre_market=market,
            ),
            rust_fn=lambda: perp_isolated_op(request),
            compare=_materialized_responses_agree,
        )
    except AuthorityError as exc:
        return f"perp_stateful rust authority disagreement: {exc}"
    except Exception as exc:
        return f"perp_stateful rust authority error: {_safe_error_str(exc)}"

    if decision.authority != "rust":
        return "perp_stateful rust authority internal error: Rust did not decide"
    if isinstance(decision.result, Mapping) and bool(decision.result.get("accept")):
        post = decision.result.get("post")
        python_doc = {
            "accept": True,
            "quote_asset": post.get("quote_asset") if isinstance(post, Mapping) else None,
            "global_state": post.get("global_state") if isinstance(post, Mapping) else None,
            "accounts": post.get("accounts") if isinstance(post, Mapping) else None,
            "effects": decision.result.get("effects"),
        }
        if not _materialized_shadow_response_bounded(python_doc):
            return "perp_stateful rust authority response too large"
    return _commit_materialized_rust_accept(
        ctx=ctx,
        i=i,
        op=op,
        pre_market=market,
        rust_response=decision.result,
    )


def _shadow_accepted_isolated_op(
    *,
    ctx: _PerpApplyCtx,
    op: PerpOp,
    pre_market: PerpMarketState,
    post_market: PerpMarketState,
    python_effect: Mapping[str, Any],
    integration_facts: Mapping[str, Any] | None,
) -> Optional[str]:
    from src.runtime.authority import AuthorityError, AuthorityMode, active_mode, decide
    from src.runtime.rust_invoker import perp_isolated_op, perp_stateful_case

    mode = active_mode(PERP_STATEFUL_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return None
    if mode in (AuthorityMode.RUST_AUTHORITY, AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW):
        # Defensive guard only. `_apply_isolated_op` routes authority modes to the
        # pre-state Rust materializer before the Python handler can run.
        return _PERP_STATEFUL_AUTHORITY_BLOCK_MSG
    materialized = op.action in _PERP_STATEFUL_MATERIALIZED_ACTIONS
    if materialized and not _materialized_shadow_account_count_bounded(pre_market):
        return None

    try:
        if materialized:
            python_doc = _perp_stateful_full_doc(post_market, python_effect)
            if not _materialized_shadow_response_bounded(python_doc):
                return None
            if integration_facts is None:
                return "perp_stateful rust shadow error: missing pre-state integration facts"
            request = _build_isolated_op_request(
                pre_market=pre_market,
                op=op,
                integration_facts=integration_facts,
            )
            if not _materialized_shadow_request_bounded(request):
                return None
            decide(
                PERP_STATEFUL_SURFACE,
                mode,
                python_fn=lambda: python_doc,
                rust_fn=lambda: perp_isolated_op(request),
                compare=_full_post_markets_agree,
            )
        else:
            subcommand, case = _perp_stateful_shadow_case(
                ctx=ctx,
                pre_market=pre_market,
                post_market=post_market,
                op=op,
            )
            decide(
                PERP_STATEFUL_SURFACE,
                mode,
                python_fn=lambda: _perp_stateful_python_doc(
                    pre_market=pre_market,
                    post_market=post_market,
                    op=op,
                ),
                rust_fn=lambda: perp_stateful_case(subcommand, case),
                compare=_perp_stateful_docs_agree,
            )
        return None
    except AuthorityError as exc:
        return f"perp_stateful rust shadow disagreement: {exc}"
    except Exception as exc:
        return f"perp_stateful rust shadow error: {_safe_error_str(exc)}"


_ISOLATED_ACTION_HANDLERS = {
    "advance_epoch": _apply_isolated_advance_epoch,
    "publish_clearing_price": _apply_isolated_publish_clearing_price,
    "apply_funding_auto": _apply_isolated_apply_funding_auto,
    "settle_epoch": _apply_isolated_settle_epoch,
    "clear_breaker": _apply_isolated_clear_breaker,
    "set_market_params": _apply_isolated_set_market_params,
    "deposit_collateral": _apply_isolated_deposit_collateral,
    "withdraw_collateral": _apply_isolated_withdraw_collateral,
    "deposit_insurance": _apply_isolated_deposit_insurance,
    "set_position": _apply_isolated_set_position,
    "partial_liquidate": _apply_isolated_partial_liquidate,
}


def _apply_isolated_op(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    from src.runtime.authority import AuthorityMode, active_mode

    mode = active_mode(PERP_STATEFUL_SURFACE)
    if mode in (AuthorityMode.RUST_AUTHORITY, AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW):
        return _apply_materialized_isolated_op_rust_authority(ctx=ctx, i=i, op=op, market=market)

    handler = _ISOLATED_ACTION_HANDLERS.get(op.action)
    if handler is None:
        return f"unknown perps action: {op.action}"
    pre_fact_ctx = None
    if mode is not AuthorityMode.PYTHON_AUTHORITY:
        pre_fact_ctx = _PerpApplyCtx(
            config=ctx.config,
            balances=_copy_balance_table(ctx.balances),
            nonces=_copy_nonce_table(ctx.nonces),
            markets=dict(ctx.markets),
            effects=[],
            tx_sender_pubkey=ctx.tx_sender_pubkey,
            block_timestamp=ctx.block_timestamp,
        )

    err = handler(ctx, i=i, op=op, market=market)
    if err is not None:
        return err

    integration_facts = None
    if pre_fact_ctx is not None:
        integration_facts = _isolated_op_integration_facts(
            ctx=pre_fact_ctx,
            pre_market=market,
            op=op,
            trust_authoritative_acceptance=True,
        )
    # The accepted op appended exactly one effect; capture its semantic payload
    # for effect parity.
    python_effect = _materialized_effect_payload(ctx.effects[-1]) if ctx.effects else {}
    return _shadow_accepted_isolated_op(
        ctx=ctx,
        op=op,
        pre_market=market,
        post_market=ctx.markets[op.market_id],
        python_effect=python_effect,
        integration_facts=integration_facts,
    )


# ---------------------------------------------------------------------------
# N-party net-zero clearinghouse (clearinghouse_np_v1) engine path.
# ---------------------------------------------------------------------------

_CHNP_PARAM_KEYS = (
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
)


def _chnp_market_to_core(market: _NpMarketState) -> Any:
    gs = market.global_state
    params = _np_core.MarketParams(**{k: int(gs[k]) for k in _CHNP_PARAM_KEYS})
    accounts = tuple(
        _np_core.Account(
            pubkey=a.pubkey,
            position_base=a.position_base,
            entry_price_e8=a.entry_price_e8,
            collateral_e8=a.collateral_e8,
            funding_paid_cum_e8=a.funding_paid_cum_e8,
            nonce=a.nonce,
        )
        for a in market.accounts
    )
    return _np_core.MarketState(
        index_price_e8=int(gs["index_price_e8"]),
        params=params,
        accounts=accounts,
        now_epoch=int(gs["now_epoch"]),
        fee_pool_e8=int(gs["fee_pool_e8"]),
        insurance_e8=int(gs["insurance_e8"]),
        insurance_ext_e8=int(gs["insurance_ext_e8"]),
        claims_paid_e8=int(gs["claims_paid_e8"]),
        net_deposited_e8=int(gs["net_deposited_e8"]),
    )


def _chnp_core_to_market(
    quote_asset: str,
    ms: Any,
    *,
    pending_intents: tuple[_NpPendingIntent, ...] = (),
    pending_price_fields: Mapping[str, Any] | None = None,
) -> _NpMarketState:
    gs = {
        "now_epoch": int(ms.now_epoch),
        "index_price_e8": int(ms.index_price_e8),
        "clearing_price_seen": 0,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "fee_pool_e8": int(ms.fee_pool_e8),
        "insurance_e8": int(ms.insurance_e8),
        "insurance_ext_e8": int(ms.insurance_ext_e8),
        "claims_paid_e8": int(ms.claims_paid_e8),
        "net_deposited_e8": int(ms.net_deposited_e8),
    }
    if pending_price_fields is not None:
        for key in ("clearing_price_seen", "clearing_price_epoch", "clearing_price_e8"):
            gs[key] = int(pending_price_fields.get(key, 0))
    for key in _CHNP_PARAM_KEYS:
        gs[key] = int(getattr(ms.params, key))
    accounts = tuple(
        _NpAccount(
            pubkey=a.pubkey,
            position_base=a.position_base,
            entry_price_e8=a.entry_price_e8,
            collateral_e8=a.collateral_e8,
            funding_paid_cum_e8=a.funding_paid_cum_e8,
            nonce=a.nonce,
        )
        for a in ms.accounts
    )
    return _NpMarketState(
        quote_asset=quote_asset,
        global_state=gs,
        accounts=accounts,
        pending_intents=tuple(pending_intents),
    )


def _chnp_pending_price_fields(market: _NpMarketState) -> dict[str, int]:
    return {
        "clearing_price_seen": int(market.global_state.get("clearing_price_seen", 0)),
        "clearing_price_epoch": int(market.global_state.get("clearing_price_epoch", 0)),
        "clearing_price_e8": int(market.global_state.get("clearing_price_e8", 0)),
    }


def _chnp_participant_pubkeys(market: _NpMarketState) -> tuple[str, ...]:
    return tuple(
        account.pubkey
        for account in sorted(
            market.accounts,
            key=lambda a: _hex_to_bytes_allow_0x(a.pubkey, name="pubkey", expected_nbytes=48),
        )
    )


def _chnp_pending_intents_to_core(market: _NpMarketState) -> list[_NpIntent]:
    return [
        _NpIntent(
            pubkey=intent.pubkey,
            target_base=intent.target_base,
            limit_price_e8=intent.limit_price_e8,
            min_fill_base=intent.min_fill_base,
            expiry_epoch=intent.expiry_epoch,
            nonce=intent.nonce,
        )
        for intent in market.pending_intents
    ]


def _chnp_settle_oracle_bridge_error(
    config: PerpEngineConfig,
    *,
    data: Mapping[str, Any],
    market_id: str,
    market: _NpMarketState,
    state_for_oracle: Mapping[str, Any],
) -> str | None:
    participant_pubkeys = _chnp_participant_pubkeys(market)
    expected_action_id = _perps_clearinghouse_runtime_oracle_action_id(
        config,
        market_id=market_id,
        action_kind="settle_epoch",
        market_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
        quote_asset=market.quote_asset,
        state=state_for_oracle,
        participant_pubkeys=participant_pubkeys,
    )
    err = _require_oracle_adapter_bridge(
        config,
        data=data,
        consumer_module="zenodex.perps",
        action_kind="settle_epoch",
        expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
        expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        expected_action_id=expected_action_id,
        required=config.require_oracle_adapter_for_clearinghouse_settle_epoch,
    )
    if err is not None:
        return err
    return _check_clearinghouse_settle_oracle_authorization(
        config,
        data=data,
        market_id=market_id,
        market_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
        quote_asset=market.quote_asset,
        state=state_for_oracle,
        participant_pubkeys=participant_pubkeys,
    )


def _chnp_run_epoch(
    market: _NpMarketState,
    *,
    clearing_price_e8: int,
    funding_rate_bps: int,
) -> tuple[_NpMarketState, Any]:
    ms = _chnp_market_to_core(market)
    intents = _chnp_pending_intents_to_core(market)
    ms2, result = _np_core.run_epoch(ms, clearing_price_e8, funding_rate_bps, intents)
    return _chnp_core_to_market(market.quote_asset, ms2, pending_intents=()), result


def _apply_chnp_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    chnp_market: _NpMarketState,
) -> str | None:
    config = ctx.config
    balances = ctx.balances
    tx_sender_pubkey = ctx.tx_sender_pubkey
    action = op.action
    market_id = op.market_id
    data = op.data

    if action == "join_market":
        allowed = {"module", "version", "market_id", "action", "account_pubkey"}
        unknown = _reject_unknown_fields(data, allowed, error="join_market has unknown fields")
        if unknown is not None:
            return unknown
        account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
        sender_err = _require_sender_bound_account_pubkey(
            account_pubkey=account_pubkey,
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if sender_err is not None:
            return sender_err
        ms = _chnp_market_to_core(chnp_market)
        try:
            ms2 = _np_core.deposit(ms, account_pubkey, 0)
        except Exception as exc:
            return _safe_error_str(exc)
        ctx.markets[market_id] = _chnp_core_to_market(
            chnp_market.quote_asset,
            ms2,
            pending_intents=chnp_market.pending_intents,
            pending_price_fields=_chnp_pending_price_fields(chnp_market),
        )
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey})
        return None

    if action in ("deposit_collateral", "withdraw_collateral"):
        allowed = {"module", "version", "market_id", "action", "account_pubkey", "amount"}
        unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
        if unknown is not None:
            return unknown
        account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
        sender_err = _require_sender_bound_account_pubkey(
            account_pubkey=account_pubkey,
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if sender_err is not None:
            return sender_err
        amount = _require_int(data.get("amount"), name="amount", non_negative=True)
        amount_e8 = int(amount) * _E8_SCALE
        if amount_e8 > _np_core.I128_MAX:
            return f"{action} amount exceeds clearinghouse_np ledger bound"
        ms = _chnp_market_to_core(chnp_market)
        if action == "deposit_collateral":
            if balances.get(account_pubkey, chnp_market.quote_asset) < amount:
                return "insufficient balance for deposit"
            try:
                ms2 = _np_core.deposit(ms, account_pubkey, amount_e8)
            except Exception as exc:
                return _safe_error_str(exc)
            balances.subtract(account_pubkey, chnp_market.quote_asset, amount)
        else:
            if chnp_market.role_for_pubkey(account_pubkey) is None:
                return "unknown account_pubkey for this clearinghouse_np market"
            try:
                ms2 = _np_core.withdraw(ms, account_pubkey, amount_e8)
            except Exception as exc:
                return _safe_error_str(exc)
            balances.add(account_pubkey, chnp_market.quote_asset, amount)
        ctx.markets[market_id] = _chnp_core_to_market(
            chnp_market.quote_asset,
            ms2,
            pending_intents=chnp_market.pending_intents,
            pending_price_fields=_chnp_pending_price_fields(chnp_market),
        )
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey})
        return None

    if action == "submit_intent":
        allowed = {
            "module",
            "version",
            "market_id",
            "action",
            "account_pubkey",
            "target_base",
            "limit_price_e8",
            "min_fill_base",
            "expiry_epoch",
        }
        unknown = _reject_unknown_fields(data, allowed, error="submit_intent has unknown fields")
        if unknown is not None:
            return unknown
        account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
        sender_err = _require_sender_bound_account_pubkey(
            account_pubkey=account_pubkey,
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if sender_err is not None:
            return sender_err
        if chnp_market.role_for_pubkey(account_pubkey) is None:
            return "unknown account_pubkey for this clearinghouse_np market"
        target_base = _require_int(data.get("target_base"), name="target_base", non_negative=False)
        limit_price_e8 = _require_int(data.get("limit_price_e8", 0), name="limit_price_e8", non_negative=True)
        min_fill_base = _require_int(data.get("min_fill_base", 0), name="min_fill_base", non_negative=True)
        expiry_epoch = _require_int(data.get("expiry_epoch", 1 << 62), name="expiry_epoch", non_negative=True)
        if abs(target_base) > int(chnp_market.global_state["max_position_abs"]):
            return "submit_intent target exceeds max_position_abs"
        ms = _chnp_market_to_core(chnp_market)
        acct = ms.by_pubkey().get(account_pubkey)
        intent_nonce = (int(acct.nonce) if acct is not None else 0) + 1
        intent = _NpPendingIntent(
            pubkey=account_pubkey,
            target_base=target_base,
            nonce=intent_nonce,
            limit_price_e8=limit_price_e8,
            min_fill_base=min_fill_base,
            expiry_epoch=expiry_epoch,
        )
        target_bytes = _hex_to_bytes_allow_0x(account_pubkey, name="account_pubkey", expected_nbytes=48)
        kept = tuple(
            pending
            for pending in chnp_market.pending_intents
            if _hex_to_bytes_allow_0x(pending.pubkey, name="pubkey", expected_nbytes=48) != target_bytes
        )
        ctx.markets[market_id] = _chnp_core_to_market(
            chnp_market.quote_asset,
            ms,
            pending_intents=kept + (intent,),
            pending_price_fields=_chnp_pending_price_fields(chnp_market),
        )
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey})
        return None

    if action == "match_intents":
        return "match_intents disabled for clearinghouse_np_v1; use run_epoch"

    if action == "publish_clearing_price":
        oracle_pubkey = (config.oracle_pubkey or "").strip()
        if not oracle_pubkey:
            return "oracle signer not configured (set PerpEngineConfig.oracle_pubkey)"
        allowed = {
            "module",
            "version",
            "market_id",
            "action",
            "price_e8",
            "deadline",
            "oracle_nonce",
            "oracle_sig",
        }
        unknown = _reject_unknown_fields(data, allowed, error="publish_clearing_price has unknown fields")
        if unknown is not None:
            return unknown
        if int(chnp_market.global_state.get("clearing_price_seen", 0)) != 0:
            return "clearinghouse_np clearing price already published"
        oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
        oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)
        price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
        if price_e8 <= 0:
            return "publish_clearing_price requires price_e8 > 0"
        sig_err = _verify_perp_op_signature(
            config=config,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
            signature=oracle_sig,
            op=data,
            nonces=ctx.nonces,
            block_timestamp=ctx.block_timestamp,
        )
        if sig_err is not None:
            return f"oracle signature invalid: {sig_err}"
        ms = _chnp_market_to_core(chnp_market)
        pending_price = {
            "clearing_price_seen": 1,
            "clearing_price_epoch": int(ms.now_epoch),
            "clearing_price_e8": int(price_e8),
        }
        ctx.markets[market_id] = _chnp_core_to_market(
            chnp_market.quote_asset,
            ms,
            pending_intents=chnp_market.pending_intents,
            pending_price_fields=pending_price,
        )
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "price_e8": int(price_e8)})
        return None

    if action in ("run_epoch", "settle_epoch"):
        allowed = {
            "module",
            "version",
            "market_id",
            "action",
            "funding_rate_bps",
            "oracle_adapter_bridge",
            "oracle_authorization",
        }
        unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
        if unknown is not None:
            return unknown
        op_err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
        if op_err is not None:
            return op_err
        funding_rate_bps = _require_int(data.get("funding_rate_bps", 0), name="funding_rate_bps", non_negative=False)
        if funding_rate_bps != 0:
            return f"{action} funding_rate_bps must be 0 (oracle-bound funding not yet implemented)"
        pending_price = _chnp_pending_price_fields(chnp_market)
        if int(pending_price["clearing_price_seen"]) != 1:
            return f"{action} requires a published (oracle-signed) clearing price"
        clearing_price_e8 = int(pending_price["clearing_price_e8"])
        err = _chnp_settle_oracle_bridge_error(
            config,
            data=data,
            market_id=market_id,
            market=chnp_market,
            state_for_oracle=dict(chnp_market.global_state),
        )
        if err is not None:
            return err
        try:
            next_market, result = _chnp_run_epoch(
                chnp_market,
                clearing_price_e8=clearing_price_e8,
                funding_rate_bps=int(funding_rate_bps),
            )
        except _np_core.SettleInsolvent as exc:
            return f"clearinghouse_np_settle_insolvent: {_safe_error_str(exc)}"
        except Exception as exc:
            return _safe_error_str(exc)
        ctx.markets[market_id] = next_market
        ctx.effects.append(
            {
                "i": i,
                "market_id": market_id,
                "action": action,
                "now_epoch": int(next_market.global_state["now_epoch"]),
                "matched_net": int(result.net),
                "fills": {pk: int(delta) for pk, delta in result.deltas.items()},
                "receipt_count": len(result.receipts),
            }
        )
        return None

    if action == "advance_epoch":
        allowed = {"module", "version", "market_id", "action"}
        unknown = _reject_unknown_fields(data, allowed, error="advance_epoch has unknown fields")
        if unknown is not None:
            return unknown
        op_err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
        if op_err is not None:
            return op_err
        ms = _chnp_market_to_core(chnp_market)
        if any(int(account.position_base) != 0 for account in ms.accounts):
            return "advance_epoch requires flat clearinghouse_np positions"
        if chnp_market.pending_intents:
            return "advance_epoch requires empty clearinghouse_np intent buffer"
        if int(chnp_market.global_state.get("clearing_price_seen", 0)) != 0:
            return "advance_epoch requires no published clearing price"
        ms2 = _np_core.MarketState(
            index_price_e8=ms.index_price_e8,
            params=ms.params,
            accounts=ms.accounts,
            now_epoch=ms.now_epoch + 1,
            fee_pool_e8=ms.fee_pool_e8,
            insurance_e8=ms.insurance_e8,
            insurance_ext_e8=ms.insurance_ext_e8,
            claims_paid_e8=ms.claims_paid_e8,
            net_deposited_e8=ms.net_deposited_e8,
        )
        ctx.markets[market_id] = _chnp_core_to_market(chnp_market.quote_asset, ms2)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "now_epoch": int(ms2.now_epoch)})
        return None

    return f"unknown perps action: {action}"


def apply_perp_ops(
    *,
    config: PerpEngineConfig,
    state: DexState,
    operations: Mapping[str, Any],
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> PerpTxResult:
    try:
        ops = parse_perp_ops(
            operations,
            max_ops=config.max_ops,
            max_op_bytes=config.max_op_bytes,
            max_total_ops_bytes=config.max_total_ops_bytes,
            max_int_bits=config.max_int_bits,
        )

        if not ops:
            return PerpTxResult(ok=True, state=state, effects=[])

        if any(op.action == "publish_clearing_price" for op in ops):
            posture_err = _oracle_reward_posture_error(config)
            if posture_err is not None:
                return PerpTxResult(ok=False, error=posture_err)

        has_isolated = any(op.version == PERP_OP_VERSION_V0_1 for op in ops)
        has_clearinghouse = any(
            op.version in (
                PERP_OP_VERSION_CH2P_V0_2,
                PERP_OP_VERSION_CH2P_V1_0,
                PERP_OP_VERSION_CH3P_V1_1,
                PERP_OP_VERSION_CHNP_V1_2,
            )
            for op in ops
        )
        if has_isolated and has_clearinghouse:
            return PerpTxResult(ok=False, error="cannot mix isolated and clearinghouse perps ops in one tx")
        if has_isolated and not config.allow_isolated_markets:
            return PerpTxResult(ok=False, error="isolated perps disabled by config (enable allow_isolated_markets)")

        # Work on copies; only commit to `DexState` if everything succeeds.
        balances = _copy_balance_table(state.balances)
        nonces = _copy_nonce_table(state.nonces)

        perps = state.perps
        perps_version = PERPS_STATE_VERSION
        if perps is None:
            perps = PerpsState(version=PERPS_STATE_VERSION, markets={})
        else:
            perps_version = int(perps.version)

        markets = dict(perps.markets)
        # Perps state v5 is a strict superset of v4 (adds per-market kind tags). If
        # any op uses the clearinghouse posture, upgrade in-memory to v5.
        if any(
            op.version in (
                PERP_OP_VERSION_CH2P_V0_2,
                PERP_OP_VERSION_CH2P_V1_0,
                PERP_OP_VERSION_CH3P_V1_1,
                PERP_OP_VERSION_CHNP_V1_2,
            )
            for op in ops
        ):
            perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
        effects: List[Dict[str, Any]] = []
        ctx = _PerpApplyCtx(
            config=config,
            balances=balances,
            nonces=nonces,
            markets=markets,
            effects=effects,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=block_timestamp,
        )

        for i, op in enumerate(ops):
            action = op.action
            market_id = op.market_id
            version = op.version
            data = op.data

            if action == "init_market":
                if version != PERP_OP_VERSION_V0_1:
                    return PerpTxResult(ok=False, error="init_market requires perps.version=0.1")
                err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
                if err is not None:
                    return PerpTxResult(ok=False, error=err)
                if market_id in markets:
                    return PerpTxResult(ok=False, error="market already exists")

                quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
                allowed = {"module", "version", "market_id", "action", "quote_asset"}
                extra = set(data.keys()) - allowed
                if extra:
                    return PerpTxResult(ok=False, error="init_market has unknown fields")

                markets[market_id] = PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=_kernel_initial_global_state(),
                    accounts={},
                )
                effects.append({"i": i, "market_id": market_id, "action": action})
                continue

            if action == "init_market_2p":
                version_ok = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
                if not version_ok:
                    surface_err = _evaluate_signed_surface(
                        action_kind=ACTION_INIT_MARKET_2P,
                        action=action,
                        version_ok=False,
                        unknown_fields_ok=True,
                    )
                    return PerpTxResult(ok=False, error=surface_err or "init_market_2p requires perps.version=0.2 or 1.0")
                if market_id in markets:
                    return PerpTxResult(ok=False, error="market already exists")

                quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
                account_a_pubkey = _require_str(
                    data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
                )
                account_b_pubkey = _require_str(
                    data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
                )
                distinct_accounts_ok = account_a_pubkey != account_b_pubkey

                # Distinctness must be enforced by pubkey bytes (not string representation).
                try:
                    a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
                    b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
                    distinct_accounts_ok = bool(distinct_accounts_ok and a_b != b_b)
                except Exception:
                    # Fail later via signature verification (keeps errors attributed to the signer).
                    pass

                nonce_a = _require_int_u32_pos(data.get("nonce_a"), name="nonce_a")
                sig_a = _require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096)
                nonce_b = _require_int_u32_pos(data.get("nonce_b"), name="nonce_b")
                sig_b = _require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096)

                allowed = {
                    "module",
                    "version",
                    "market_id",
                    "action",
                    "quote_asset",
                    "account_a_pubkey",
                    "account_b_pubkey",
                    "deadline",
                    "nonce_a",
                    "sig_a",
                    "nonce_b",
                    "sig_b",
                }
                surface_err = _evaluate_signed_surface(
                    action_kind=ACTION_INIT_MARKET_2P,
                    action=action,
                    version_ok=version_ok,
                    unknown_fields_ok=not (set(data.keys()) - allowed),
                    distinct_accounts_ok=distinct_accounts_ok,
                )
                if surface_err is not None:
                    return PerpTxResult(ok=False, error=surface_err)

                sig_err_a = _verify_perp_op_signature(
                    config=config,
                    signer_pubkey=account_a_pubkey,
                    nonce=nonce_a,
                    signature=sig_a,
                    op=data,
                    nonces=nonces,
                    block_timestamp=block_timestamp,
                )
                if sig_err_a is not None:
                    return PerpTxResult(ok=False, error=f"account_a signature invalid: {sig_err_a}")

                sig_err_b = _verify_perp_op_signature(
                    config=config,
                    signer_pubkey=account_b_pubkey,
                    nonce=nonce_b,
                    signature=sig_b,
                    op=data,
                    nonces=nonces,
                    block_timestamp=block_timestamp,
                )
                if sig_err_b is not None:
                    return PerpTxResult(ok=False, error=f"account_b signature invalid: {sig_err_b}")

                # Clearinghouse markets require perps state v5+ (market kind tags).
                perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
                try:
                    init_state = _ch2p_init_state_dict()
                except Exception as exc:
                    return PerpTxResult(ok=False, error=str(exc))
                markets[market_id] = PerpClearinghouse2pMarketState(
                    quote_asset=quote_asset,
                    account_a_pubkey=account_a_pubkey,
                    account_b_pubkey=account_b_pubkey,
                    state=init_state,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "account_a_pubkey": account_a_pubkey,
                        "account_b_pubkey": account_b_pubkey,
                    }
                )
                continue

            if action == "init_market_3p":
                version_ok = version == PERP_OP_VERSION_CH3P_V1_1
                if not version_ok:
                    surface_err = _evaluate_signed_surface(
                        action_kind=ACTION_INIT_MARKET_3P,
                        action=action,
                        version_ok=False,
                        unknown_fields_ok=True,
                    )
                    return PerpTxResult(ok=False, error=surface_err or "init_market_3p requires perps.version=1.1")
                if market_id in markets:
                    return PerpTxResult(ok=False, error="market already exists")

                quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
                account_a_pubkey = _require_str(
                    data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
                )
                account_b_pubkey = _require_str(
                    data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
                )
                account_c_pubkey = _require_str(
                    data.get("account_c_pubkey"), name="account_c_pubkey", non_empty=True, max_len=512
                )
                distinct_accounts_ok = len({account_a_pubkey, account_b_pubkey, account_c_pubkey}) == 3

                # Distinctness must be enforced by pubkey bytes (not string representation).
                try:
                    a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
                    b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
                    c_b = _hex_to_bytes_allow_0x(account_c_pubkey, name="account_c_pubkey", expected_nbytes=48)
                    distinct_accounts_ok = bool(distinct_accounts_ok and len({a_b, b_b, c_b}) == 3)
                except Exception:
                    pass

                nonce_a = _require_int_u32_pos(data.get("nonce_a"), name="nonce_a")
                sig_a = _require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096)
                nonce_b = _require_int_u32_pos(data.get("nonce_b"), name="nonce_b")
                sig_b = _require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096)
                nonce_c = _require_int_u32_pos(data.get("nonce_c"), name="nonce_c")
                sig_c = _require_str(data.get("sig_c"), name="sig_c", non_empty=True, max_len=4096)

                allowed = {
                    "module",
                    "version",
                    "market_id",
                    "action",
                    "quote_asset",
                    "account_a_pubkey",
                    "account_b_pubkey",
                    "account_c_pubkey",
                    "deadline",
                    "nonce_a",
                    "sig_a",
                    "nonce_b",
                    "sig_b",
                    "nonce_c",
                    "sig_c",
                }
                surface_err = _evaluate_signed_surface(
                    action_kind=ACTION_INIT_MARKET_3P,
                    action=action,
                    version_ok=version_ok,
                    unknown_fields_ok=not (set(data.keys()) - allowed),
                    distinct_accounts_ok=distinct_accounts_ok,
                )
                if surface_err is not None:
                    return PerpTxResult(ok=False, error=surface_err)

                sig_err_a = _verify_perp_op_signature(
                    config=config,
                    signer_pubkey=account_a_pubkey,
                    nonce=nonce_a,
                    signature=sig_a,
                    op=data,
                    nonces=nonces,
                    block_timestamp=block_timestamp,
                )
                if sig_err_a is not None:
                    return PerpTxResult(ok=False, error=f"account_a signature invalid: {sig_err_a}")

                sig_err_b = _verify_perp_op_signature(
                    config=config,
                    signer_pubkey=account_b_pubkey,
                    nonce=nonce_b,
                    signature=sig_b,
                    op=data,
                    nonces=nonces,
                    block_timestamp=block_timestamp,
                )
                if sig_err_b is not None:
                    return PerpTxResult(ok=False, error=f"account_b signature invalid: {sig_err_b}")

                sig_err_c = _verify_perp_op_signature(
                    config=config,
                    signer_pubkey=account_c_pubkey,
                    nonce=nonce_c,
                    signature=sig_c,
                    op=data,
                    nonces=nonces,
                    block_timestamp=block_timestamp,
                )
                if sig_err_c is not None:
                    return PerpTxResult(ok=False, error=f"account_c signature invalid: {sig_err_c}")

                perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
                try:
                    init_state = _ch3p_init_state_dict()
                except Exception as exc:
                    return PerpTxResult(ok=False, error=str(exc))
                markets[market_id] = PerpClearinghouse3pTransferMarketState(
                    quote_asset=quote_asset,
                    account_a_pubkey=account_a_pubkey,
                    account_b_pubkey=account_b_pubkey,
                    account_c_pubkey=account_c_pubkey,
                    state=init_state,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "account_a_pubkey": account_a_pubkey,
                        "account_b_pubkey": account_b_pubkey,
                        "account_c_pubkey": account_c_pubkey,
                    }
                )
                continue

            if action == "init_market_np":
                if version != PERP_OP_VERSION_CHNP_V1_2:
                    return PerpTxResult(ok=False, error="init_market_np requires perps.version=1.2")
                err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
                if err is not None:
                    return PerpTxResult(ok=False, error=err)
                if market_id in markets:
                    return PerpTxResult(ok=False, error="market already exists")
                if not market_id.startswith(PERP_CHNP_MARKET_PREFIX):
                    return PerpTxResult(ok=False, error="clearinghouse_np market_id must start with perp:chnp:")
                quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
                index_price_e8 = _require_int(data.get("index_price_e8"), name="index_price_e8", non_negative=True)
                if index_price_e8 <= 0:
                    return PerpTxResult(ok=False, error="index_price_e8 must be positive")
                allowed = {
                    "module",
                    "version",
                    "market_id",
                    "action",
                    "quote_asset",
                    "index_price_e8",
                    "insurance_seed_e8",
                    "params",
                }
                if set(data.keys()) - allowed:
                    return PerpTxResult(ok=False, error="init_market_np has unknown fields")
                insurance_seed_e8 = _require_int(
                    data.get("insurance_seed_e8", 0),
                    name="insurance_seed_e8",
                    non_negative=True,
                )
                insurance_seed_quote = 0
                if insurance_seed_e8:
                    if insurance_seed_e8 % _E8_SCALE != 0:
                        return PerpTxResult(ok=False, error="insurance_seed_e8 must be quote-unit aligned")
                    insurance_seed_quote = insurance_seed_e8 // _E8_SCALE
                    if balances.get(tx_sender_pubkey, quote_asset) < insurance_seed_quote:
                        return PerpTxResult(ok=False, error="insufficient balance for insurance seed")
                params_obj = data.get("params", {})
                if not isinstance(params_obj, Mapping):
                    return PerpTxResult(ok=False, error="params must be an object")
                perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
                try:
                    param_overrides = _validated_control_params(
                        params_obj,
                        bounds=_CLEARINGHOUSE_NP_CONTROL_PARAM_BOUNDS,
                        name="params",
                    )
                    if not _funded_liquidation_params_ok(
                        maintenance_margin_bps=int(param_overrides.get("maintenance_margin_bps", 0)),
                        depeg_buffer_bps=int(param_overrides.get("depeg_buffer_bps", 0)),
                        max_oracle_move_bps=int(param_overrides.get("max_oracle_move_bps", 0)),
                        liquidation_penalty_bps=int(param_overrides.get("liquidation_penalty_bps", 0)),
                    ):
                        return PerpTxResult(
                            ok=False,
                            error="invalid params: require funded liquidation after max_oracle_move_bps",
                        )
                    init_ms = _np_core.init_market(
                        index_price_e8,
                        params=_np_core.MarketParams(**param_overrides),
                        insurance_seed_e8=insurance_seed_e8,
                    )
                    next_market = _chnp_core_to_market(quote_asset, init_ms, pending_intents=())
                except Exception as exc:
                    return PerpTxResult(ok=False, error=_safe_error_str(exc))
                if insurance_seed_quote:
                    balances.subtract(tx_sender_pubkey, quote_asset, insurance_seed_quote)
                markets[market_id] = next_market
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "quote_asset": quote_asset,
                        "insurance_seed_e8": int(insurance_seed_e8),
                    }
                )
                continue

            market_any = markets.get(market_id)
            if market_any is None:
                return PerpTxResult(ok=False, error="unknown market_id")

            is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
            is_ch3p = version == PERP_OP_VERSION_CH3P_V1_1
            is_chnp = version == PERP_OP_VERSION_CHNP_V1_2
            if is_ch2p:
                if not isinstance(market_any, PerpClearinghouse2pMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse_2p operation")
                ch2p_market = market_any
            elif is_ch3p:
                if not isinstance(market_any, PerpClearinghouse3pTransferMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse_3p operation")
                ch3p_market = market_any
            elif is_chnp:
                if not isinstance(market_any, _NpMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse_np operation")
                chnp_market = market_any
            else:
                if not isinstance(market_any, PerpMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for isolated operation")
                market = market_any

            if is_ch2p:
                err = _apply_ch2p_op(ctx, i=i, op=op, ch2p_market=ch2p_market)
                if err is not None:
                    return PerpTxResult(ok=False, error=err)
                continue

            if is_ch3p:
                err = _apply_ch3p_op(ctx, i=i, op=op, ch3p_market=ch3p_market)
                if err is not None:
                    return PerpTxResult(ok=False, error=err)
                continue

            if is_chnp:
                err = _apply_chnp_op(ctx, i=i, op=op, chnp_market=chnp_market)
                if err is not None:
                    return PerpTxResult(ok=False, error=err)
                continue

            err = _apply_isolated_op(ctx, i=i, op=op, market=market)
            if err is not None:
                return PerpTxResult(ok=False, error=err)
            continue

        next_perps = PerpsState(version=perps_version, markets=markets) if markets else None
        next_state = replace(state, balances=balances, nonces=nonces, perps=next_perps)
        return PerpTxResult(ok=True, state=next_state, effects=effects)

    except Exception as exc:
        return PerpTxResult(ok=False, error=_safe_error_str(exc))
