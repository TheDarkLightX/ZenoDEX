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

import hashlib
import re
import sys
from dataclasses import asdict, dataclass, fields, replace
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import Any, Callable, Dict, List, Mapping, Optional

from ..core import perp_np_clearinghouse as _np_core
from ..core.dex import DexState
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
from ..core.perp_clearinghouse_phase import clearinghouse_position_update_allowed
from ..core.perp_depth_source_quorum_economics import (
    verify_depth_source_quorum_economics_payload,
)
from ..core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perp_funding_closeout_liability_certificate import (
    RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    ClosedFundingSourceRow,
    PositionAccount,
    carried_funding_closeout_liability_hash,
    funding_closeout_allocation_receipt_from_payload,
    funding_closeout_carry_forward_receipt_from_payload,
    funding_closeout_carry_forward_receipt_to_payload,
    funding_closeout_rationed_allocation_receipt_from_payload,
    funding_closeout_source_availability_hash,
    funding_closeout_source_bound_rationed_allocation_receipt_from_payload,
    funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload,
    post_open_receiver_claim_rows,
    pre_close_position_snapshot_hash,
    verify_funding_closeout_allocation_receipt_payload,
    verify_funding_closeout_carry_forward_receipt_payload,
    verify_funding_closeout_liability_certificate_payload,
    verify_funding_closeout_liability_receipt_payload,
    verify_funding_closeout_rationed_allocation_receipt_payload,
    verify_funding_closeout_source_bound_rationed_allocation_receipt_payload,
    verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload,
)
from ..core.perp_funding_closeout_mixed_open_netting import (
    MIXED_OPEN_NETTING_SCHEMA,
    mixed_open_funding_netting_certificate_from_payload,
    verify_mixed_open_funding_netting_certificate_payload,
)
from ..core.perp_funding_closeout_policy_ledger import (
    HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    funding_closeout_policy_ledger_from_payload,
    funding_closeout_policy_ledger_hash,
    funding_closeout_policy_ledger_to_payload,
    verify_funding_closeout_policy_ledger_payload,
)
from ..core.perp_funding_closeout_priority import (
    funding_closeout_receiver_recovery_distribution_certificate_from_payload,
    funding_closeout_receiver_recovery_distribution_certificate_hash,
    funding_closeout_recovery_collection_receipt_from_payload,
    funding_closeout_recovery_collection_receipt_hash,
    funding_closeout_recovery_priority_certificate_from_payload,
    funding_closeout_recovery_priority_certificate_hash,
    funding_closeout_recovery_source_authority_binding_hash,
    funding_closeout_recovery_source_authority_hash,
    funding_closeout_sink_recovery_distribution_certificate_from_payload,
    funding_closeout_sink_recovery_distribution_certificate_hash,
    validate_receiver_recovery_distribution_against_sources,
    validate_recovery_collection_receipt_against_sources,
    validate_recovery_priority_certificate_against_policy_ledger,
    validate_sink_recovery_distribution_against_sources,
    verify_funding_closeout_recovery_source_authority_binding_payload,
    verify_funding_closeout_recovery_source_authority_payload,
)
from ..core.perp_liquidation_envelope import require_perp_liquidation_envelope_bps
from ..core.perp_liquidation_tau_source_binding import (
    PARTIAL_LIQUIDATE_ACTION as TAU_PARTIAL_LIQUIDATE_ACTION,
)
from ..core.perp_liquidation_tau_source_binding import (
    PerpLiquidationTauSourceBinding,
    PerpLiquidationTauSourceFacts,
    derive_perp_liquidation_flags_from_source_binding,
    expected_perp_liquidation_o4,
    perp_liquidation_tau_source_binding_from_payload,
    perp_liquidation_tau_source_facts_hash,
    source_admission_envelope_reject_reason,
    source_binding_reject_reasons,
    source_membership_proof_reject_reason,
    source_root_authority_reject_reason,
    source_state_root_binding_reject_reason,
)
from ..core.perp_market_version_prefix_guard import (
    REJECT_CH2P_PREFIX_MISMATCH,
    REJECT_CH3P_PREFIX_MISMATCH,
    REJECT_INVALID_VERSION,
    REJECT_ISOLATED_PREFIX_CONFLICT,
    evaluate_perp_market_version_prefix_guard,
)
from ..core.perp_np_matching import Intent as _NpIntent
from ..core.perp_oi_depth_certificate import (
    verify_oi_depth_certificate_payload,
    verify_oi_depth_source_authority_binding_payload,
    verify_oi_depth_source_authority_payload,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_ADVANCE_EPOCH as RUNTIME_ACTION_ADVANCE_EPOCH,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_APPLY_FUNDING_AUTO as RUNTIME_ACTION_APPLY_FUNDING_AUTO,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_CARRY_FUNDING_CLOSEOUT_LIABILITY as RUNTIME_ACTION_CARRY_FUNDING_CLOSEOUT_LIABILITY,
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
    ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY as RUNTIME_ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY,
)
from ..core.perp_runtime_risk_gate import (
    ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY as RUNTIME_ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY,
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
from ..core.perp_v2.math import MAX_COLLATERAL, MAX_FUNDING_CUMULATIVE
from ..core.perp_v2.math import funding_payment as _perp_v2_funding_payment
from ..core.perp_v2.math import liq_penalty as _perp_v2_liq_penalty
from ..core.perp_v2.math import maint_margin_req as _perp_v2_maint_margin_req
from ..core.perp_v2.oi_liquidity_bound import evaluate_oi_liquidity_bound
from ..core.perps import (
    FUNDING_CLOSEOUT_RECEIVER_CLAIM_NO_EXPIRY_EPOCH,
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_GLOBAL_KEYS,
    PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
    PERPS_STATE_VERSION,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpAnyMarketState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
    PerpsState,
    funding_closeout_receiver_claim_balances_from_lots,
)
from ..core.perps import (
    PerpClearinghouseNpAccount as _NpAccount,
)
from ..core.perps import (
    PerpClearinghouseNpMarketState as _NpMarketState,
)
from ..core.perps import (
    PerpClearinghouseNpPendingIntent as _NpPendingIntent,
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
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")
_U32_MAX = 0xFFFFFFFF
_BPS_SCALE = 10_000
OracleAdapterBridgeVerifier = Callable[[Mapping[str, Any]], Any]
TauSourceAuthorityPolicyReceiptVerifier = Callable[[Mapping[str, Any]], Any]


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


def _isolated_global_with_param_updates(market: PerpMarketState, updates: Mapping[str, int]) -> Mapping[str, Any]:
    new_global = dict(market.global_state)
    for k, v in updates.items():
        new_global[k] = int(v)
    return new_global


def _validate_isolated_open_position_param_softening(market: PerpMarketState, new_global: Mapping[str, Any]) -> None:
    old_liquidation_penalty_bps = int(market.global_state["liquidation_penalty_bps"])
    old_min_notional_for_bounty = int(market.global_state["min_notional_for_bounty"])
    old_max_oracle_staleness_epochs = int(market.global_state["max_oracle_staleness_epochs"])
    new_liquidation_penalty_bps = int(new_global["liquidation_penalty_bps"])
    new_min_notional_for_bounty = int(new_global["min_notional_for_bounty"])
    new_max_oracle_staleness_epochs = int(new_global["max_oracle_staleness_epochs"])
    has_open_positions = any(int(acct.position_base) != 0 for acct in market.accounts.values())

    # Scientist hardening (bounty-farming lane):
    # while positions are open, reject parameter shocks that increase liquidation keeper payoff
    # by raising penalty bps, lowering the bounty-eligible notional threshold,
    # or widening the stale-oracle action window.
    if has_open_positions:
        if new_liquidation_penalty_bps > old_liquidation_penalty_bps:
            raise ValueError("invalid params: cannot increase liquidation_penalty_bps while positions are open")
        if new_min_notional_for_bounty < old_min_notional_for_bounty:
            raise ValueError("invalid params: cannot decrease min_notional_for_bounty while positions are open")
        if new_max_oracle_staleness_epochs > old_max_oracle_staleness_epochs:
            raise ValueError("invalid params: cannot increase max_oracle_staleness_epochs while positions are open")


def _clamp_isolated_funding_rate_to_cap(new_global: Dict[str, Any]) -> None:
    # Funding cap changes can make the stored last rate out of bounds. The rate
    # is informational for margin math, so clamp it to preserve state invariants.
    funding_cap_bps = int(new_global["funding_cap_bps"])
    funding_rate_bps = int(new_global["funding_rate_bps"])
    if abs(funding_rate_bps) > funding_cap_bps:
        new_global["funding_rate_bps"] = funding_cap_bps if funding_rate_bps >= 0 else -funding_cap_bps


def _validate_isolated_margin_and_liquidation_params(new_global: Mapping[str, Any]) -> None:
    max_oracle_move_bps = int(new_global["max_oracle_move_bps"])
    initial_margin_bps = int(new_global["initial_margin_bps"])
    maintenance_margin_bps = int(new_global["maintenance_margin_bps"])
    depeg_buffer_bps = int(new_global["depeg_buffer_bps"])
    liquidation_penalty_bps = int(new_global["liquidation_penalty_bps"])

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
    try:
        require_perp_liquidation_envelope_bps(
            initial_margin_bps=initial_margin_bps,
            maintenance_margin_bps=maintenance_margin_bps,
            depeg_buffer_bps=depeg_buffer_bps,
            max_oracle_move_bps=max_oracle_move_bps,
            liquidation_penalty_bps=liquidation_penalty_bps,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError(
            "invalid params: require funded liquidation "
            "liquidation_penalty_bps * (10000 + max_oracle_move_bps) <= "
            "10000 * (maintenance_margin_bps + depeg_buffer_bps - max_oracle_move_bps)"
        ) from exc


def _validate_isolated_liquidation_bounty_floor(
    new_global: Mapping[str, Any],
    *,
    min_collectible_liquidation_penalty_quote: int,
) -> None:
    liquidation_penalty_bps = int(new_global["liquidation_penalty_bps"])

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


def _validate_isolated_open_account_safety(market: PerpMarketState, new_global: Mapping[str, Any]) -> None:
    max_position_abs = int(new_global["max_position_abs"])
    index_price_e8 = int(new_global["index_price_e8"])
    maintenance_margin_bps = int(new_global["maintenance_margin_bps"])
    depeg_buffer_bps = int(new_global["depeg_buffer_bps"])

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


def _isolated_oi_policy_configured(config: "PerpEngineConfig") -> bool:
    spot_depth = config.isolated_oi_spot_depth_quote
    absorb = config.isolated_oi_arbitrage_absorb_bps
    return (
        spot_depth is not None
        or absorb is not None
        or config.isolated_oi_depth_certificate is not None
        or bool(config.require_isolated_oi_depth_certificate)
        or config.isolated_oi_depth_source_authority is not None
        or bool(config.require_isolated_oi_depth_source_authority)
        or config.isolated_oi_depth_source_authority_binding is not None
        or bool(config.require_isolated_oi_depth_source_authority_binding)
        or config.isolated_oi_depth_source_quorum_economics is not None
        or bool(config.require_isolated_oi_depth_source_quorum_economics)
    )


def _isolated_position_notional_quote_ceil(*, position_base: int, index_price_e8: int) -> int:
    if index_price_e8 <= 0:
        raise ValueError("index_price_e8 must be positive")
    return _ceil_div_nonnegative(abs(int(position_base)) * int(index_price_e8), _E8_SCALE)


def _isolated_open_interest_quote_ceil(
    accounts: Mapping[str, PerpAccountState],
    *,
    index_price_e8: int,
) -> int:
    total = 0
    for pk in sorted(accounts.keys()):
        total += _isolated_position_notional_quote_ceil(
            position_base=int(accounts[pk].position_base),
            index_price_e8=index_price_e8,
        )
    return total


def _isolated_oi_liquidity_policy_error(
    config: "PerpEngineConfig",
    *,
    market_id: str,
    market: PerpMarketState,
    accounts_after: Mapping[str, PerpAccountState],
) -> Optional[str]:
    if not _isolated_oi_policy_configured(config):
        return None
    spot_depth_quote = config.isolated_oi_spot_depth_quote
    arbitrage_absorb_bps = config.isolated_oi_arbitrage_absorb_bps
    economics_requested = (
        config.require_isolated_oi_depth_source_quorum_economics
        or config.isolated_oi_depth_source_quorum_economics is not None
    )
    if config.require_isolated_oi_depth_certificate and config.isolated_oi_depth_certificate is None:
        return "isolated OI depth certificate required"
    if economics_requested and config.isolated_oi_depth_certificate is None:
        return "isolated OI depth certificate required for source quorum economics"
    if (
        config.require_isolated_oi_depth_source_quorum_economics
        and config.isolated_oi_depth_source_quorum_economics is None
    ):
        return "isolated OI depth source quorum economics envelope required"
    if (
        (
            config.require_isolated_oi_depth_source_authority
            or config.isolated_oi_depth_source_authority is not None
            or config.require_isolated_oi_depth_source_authority_binding
            or config.isolated_oi_depth_source_authority_binding is not None
        )
        and config.isolated_oi_depth_certificate is None
    ):
        return "isolated OI depth certificate required for source authority"
    if config.isolated_oi_depth_certificate is not None:
        verdict = verify_oi_depth_certificate_payload(
            config.isolated_oi_depth_certificate,
            expected_market_id=market_id,
            now_epoch=int(market.global_state["now_epoch"]),
            expected_spot_depth_quote=spot_depth_quote,
            expected_arbitrage_absorb_bps=arbitrage_absorb_bps,
        )
        if not verdict.ok or verdict.certificate is None:
            return f"invalid isolated OI depth certificate: {verdict.error or 'rejected'}"
        if economics_requested and config.isolated_oi_depth_source_authority is None:
            return "isolated OI depth source authority required for source quorum economics"
        if config.require_isolated_oi_depth_source_authority and config.isolated_oi_depth_source_authority is None:
            return "isolated OI depth source authority required"
        authority = None
        if config.isolated_oi_depth_source_authority is not None:
            authority_verdict = verify_oi_depth_source_authority_payload(
                config.isolated_oi_depth_source_authority,
                expected_market_id=market_id,
                now_epoch=int(market.global_state["now_epoch"]),
                required_source_ids=verdict.certificate.source_ids,
            )
            if not authority_verdict.ok or authority_verdict.authority is None:
                return f"invalid isolated OI depth source authority: {authority_verdict.error or 'rejected'}"
            authority = authority_verdict.authority
        if economics_requested and config.isolated_oi_depth_source_authority_binding is None:
            return "isolated OI depth source authority binding required for source quorum economics"
        if (
            config.require_isolated_oi_depth_source_authority_binding
            or config.isolated_oi_depth_source_authority_binding is not None
        ):
            if authority is None:
                return "isolated OI depth source authority required for binding"
            if config.require_isolated_oi_depth_source_authority_binding and (
                config.isolated_oi_depth_source_authority_binding is None
            ):
                return "isolated OI depth source authority binding required"
            if config.isolated_oi_depth_source_authority_binding is not None:
                binding_verdict = verify_oi_depth_source_authority_binding_payload(
                    config.isolated_oi_depth_source_authority_binding,
                    authority=authority,
                    expected_market_id=market_id,
                    now_epoch=int(market.global_state["now_epoch"]),
                    expected_authority_state_root_hash=config.isolated_oi_depth_source_authority_state_root_hash,
                    expected_policy_hash=config.isolated_oi_depth_source_authority_policy_hash,
                    allowed_signer_pubkeys=config.isolated_oi_depth_source_authority_signer_pubkeys,
                )
                if not binding_verdict.ok or binding_verdict.binding is None:
                    return f"invalid isolated OI depth source authority binding: {binding_verdict.error or 'rejected'}"
        if economics_requested:
            economics_policy_hash = (
                config.isolated_oi_depth_source_quorum_economics_policy_hash
                or config.isolated_oi_depth_source_authority_policy_hash
            )
            if economics_policy_hash is None:
                return "isolated OI depth source quorum economics policy hash required"
            economics_verdict = verify_depth_source_quorum_economics_payload(
                config.isolated_oi_depth_source_quorum_economics,
                expected_market_id=market_id,
                now_epoch=int(market.global_state["now_epoch"]),
                expected_policy_hash=economics_policy_hash,
                expected_reported_depth_quote=int(verdict.certificate.spot_depth_quote),
                expected_arbitrage_absorb_bps=int(verdict.certificate.arbitrage_absorb_bps),
                expected_source_ids=verdict.certificate.source_ids,
            )
            if not economics_verdict.ok:
                return (
                    "invalid isolated OI depth source quorum economics: "
                    f"{economics_verdict.error or 'rejected'}"
                )
        spot_depth_quote = int(verdict.certificate.spot_depth_quote)
        arbitrage_absorb_bps = int(verdict.certificate.arbitrage_absorb_bps)
    if spot_depth_quote is None or arbitrage_absorb_bps is None:
        return "invalid isolated OI liquidity policy: spot depth and absorb bps are both required"

    try:
        open_interest_quote = _isolated_open_interest_quote_ceil(
            accounts_after,
            index_price_e8=int(market.global_state["index_price_e8"]),
        )
        outcome = evaluate_oi_liquidity_bound(
            open_interest_quote=open_interest_quote,
            spot_depth_quote=int(spot_depth_quote),
            arbitrage_absorb_bps=int(arbitrage_absorb_bps),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return f"invalid isolated OI liquidity policy: {_safe_error_str(exc)}"

    if not outcome.bound_ok:
        return (
            "set_position open interest exceeds liquidity-depth bound: "
            f"open_interest_quote={outcome.open_interest_quote} "
            f"max_open_interest_quote={outcome.max_open_interest_quote}"
        )
    return None


def _apply_isolated_market_params(
    market: PerpMarketState,
    *,
    params: Mapping[str, Any],
    min_collectible_liquidation_penalty_quote: int,
) -> PerpMarketState:
    updates = _validated_control_params(params, bounds=_ISOLATED_CONTROL_PARAM_BOUNDS, name="params")
    if not updates:
        return market

    new_global = dict(_isolated_global_with_param_updates(market, updates))
    _validate_isolated_open_position_param_softening(market, new_global)
    _clamp_isolated_funding_rate_to_cap(new_global)
    _validate_isolated_margin_and_liquidation_params(new_global)
    _validate_isolated_liquidation_bounty_floor(
        new_global,
        min_collectible_liquidation_penalty_quote=min_collectible_liquidation_penalty_quote,
    )
    _validate_isolated_open_account_safety(market, new_global)

    return _isolated_market_with(
        market,
        global_state=new_global,
        accounts=market.accounts,
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
        new_initial_margin_bps=int(new_state.get("initial_margin_bps", 0)),
        new_maintenance_margin_bps=int(new_state.get("maintenance_margin_bps", 0)),
        new_max_oracle_move_bps=int(new_state.get("max_oracle_move_bps", 0)),
    )
    if not guard.admission_ok:
        raise ValueError(perp_clearinghouse_market_params_guard_error(guard) or "invalid clearinghouse market params")

    try:
        if kind == "ch2p":
            _ch2p_state_from_dict(new_state)
        elif kind == "ch3p":
            _ch3p_state_from_dict(new_state)
        else:  # pragma: no cover
            raise ValueError(f"unknown clearinghouse kind: {kind}")
    except (TypeError, ValueError) as exc:
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
    require_tau_source_binding_for_isolated_partial_liquidate: bool = False
    require_tau_source_state_root_binding_for_isolated_partial_liquidate: bool = False
    require_tau_source_membership_proof_for_isolated_partial_liquidate: bool = False
    require_tau_source_root_authority_for_isolated_partial_liquidate: bool = False
    require_tau_source_admission_envelope_for_isolated_partial_liquidate: bool = False
    require_tau_source_authority_policy_receipt_for_isolated_partial_liquidate: bool = False
    tau_source_authority_policy_receipt_verifier: Optional[
        TauSourceAuthorityPolicyReceiptVerifier
    ] = None
    isolated_partial_liquidate_tau_source_state_root_hash: Optional[str] = None
    isolated_partial_liquidate_tau_source_state_root_kind: Optional[str] = None
    isolated_partial_liquidate_tau_source_root_authority_state_root_hash: Optional[str] = None
    isolated_partial_liquidate_tau_source_root_authority_policy_hash: Optional[str] = None
    isolated_partial_liquidate_tau_source_root_authority_signer_pubkeys: tuple[str, ...] = ()
    require_oracle_adapter_for_clearinghouse_settle_epoch: bool = False
    # Scientist-derived anti-bounty-farming posture guard:
    # require a non-trivial minimum collectible liquidation penalty for bounty-eligible notional.
    min_collectible_liquidation_penalty_quote: int = 1_000
    # Optional production bridge: require a typed ZenoOracle authorization before
    # isolated perps settlement can consume the current oracle/index snapshot.
    require_oracle_authorization_for_isolated_settle: bool = False
    require_oracle_authorization_for_clearinghouse_settle_epoch: bool = False
    oracle_authorization_receipt_graph_root: Optional[str] = None
    # Optional isolated-perps scaling policy. When both fields are set, each
    # set_position must keep aggregate open interest within the depth-supported
    # TWAP-funding manipulation budget.
    isolated_oi_spot_depth_quote: Optional[int] = None
    isolated_oi_arbitrage_absorb_bps: Optional[int] = None
    isolated_oi_depth_certificate: Optional[Mapping[str, Any]] = None
    require_isolated_oi_depth_certificate: bool = False
    isolated_oi_depth_source_authority: Optional[Mapping[str, Any]] = None
    require_isolated_oi_depth_source_authority: bool = False
    isolated_oi_depth_source_authority_binding: Optional[Mapping[str, Any]] = None
    require_isolated_oi_depth_source_authority_binding: bool = False
    isolated_oi_depth_source_authority_state_root_hash: Optional[str] = None
    isolated_oi_depth_source_authority_policy_hash: Optional[str] = None
    isolated_oi_depth_source_authority_signer_pubkeys: tuple[str, ...] = ()
    isolated_oi_depth_source_quorum_economics: Optional[Mapping[str, Any]] = None
    require_isolated_oi_depth_source_quorum_economics: bool = False
    isolated_oi_depth_source_quorum_economics_policy_hash: Optional[str] = None
    require_isolated_funding_closeout_liability_certificate_on_negative_net_funding: bool = False
    isolated_funding_closeout_pre_due_vector_hash: Optional[str] = None
    require_isolated_funding_closeout_liability_receipt_on_negative_net_funding: bool = False
    require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding: bool = False
    isolated_funding_closeout_pre_state_root_hash: Optional[str] = None
    isolated_funding_closeout_source_availability_hash: Optional[str] = None
    isolated_funding_closeout_recovery_source_authority: Optional[Mapping[str, Any]] = None
    isolated_funding_closeout_recovery_source_authority_binding: Optional[Mapping[str, Any]] = None
    isolated_funding_closeout_recovery_source_authority_state_root_hash: Optional[str] = None
    isolated_funding_closeout_recovery_source_authority_policy_hash: Optional[str] = None
    isolated_funding_closeout_recovery_source_authority_signer_pubkeys: tuple[str, ...] = ()


@dataclass(frozen=True)
class PerpOp:
    market_id: str
    action: str
    version: str
    data: Dict[str, Any]


_KEEP_PENDING_FUNDING_CLOSEOUT_ROOTS = object()
_KEEP_PENDING_FUNDING_CLOSEOUT_SOURCE_ROOTS = object()
_KEEP_PENDING_FUNDING_CLOSEOUT_CARRIED_ROOTS = object()
_KEEP_FUNDING_CLOSEOUT_POLICY_LEDGER_ROOTS = object()
_KEEP_FUNDING_CLOSEOUT_SINK_CLAIMANT_BALANCES = object()
_KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES = object()
_KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_LOTS = object()


def _isolated_market_with(
    market: PerpMarketState,
    *,
    global_state: Mapping[str, Any],
    accounts: Mapping[str, PerpAccountState],
    pending_funding_closeout_root_hashes: object = _KEEP_PENDING_FUNDING_CLOSEOUT_ROOTS,
    pending_funding_closeout_source_availability_hashes: object = (
        _KEEP_PENDING_FUNDING_CLOSEOUT_SOURCE_ROOTS
    ),
    pending_funding_closeout_carried_liability_hashes: object = (
        _KEEP_PENDING_FUNDING_CLOSEOUT_CARRIED_ROOTS
    ),
    funding_closeout_policy_ledger_hashes: object = (
        _KEEP_FUNDING_CLOSEOUT_POLICY_LEDGER_ROOTS
    ),
    funding_closeout_sink_claimant_balances_quote: object = (
        _KEEP_FUNDING_CLOSEOUT_SINK_CLAIMANT_BALANCES
    ),
    funding_closeout_receiver_claim_balances_quote: object = (
        _KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES
    ),
    funding_closeout_receiver_claim_lots_quote: object = (
        _KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_LOTS
    ),
) -> PerpMarketState:
    if pending_funding_closeout_root_hashes is _KEEP_PENDING_FUNDING_CLOSEOUT_ROOTS:
        pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    else:
        pending_roots = tuple(pending_funding_closeout_root_hashes)  # type: ignore[arg-type]
    if (
        pending_funding_closeout_source_availability_hashes
        is _KEEP_PENDING_FUNDING_CLOSEOUT_SOURCE_ROOTS
    ):
        pending_source_roots = tuple(
            getattr(market, "pending_funding_closeout_source_availability_hashes", ())
        )
    else:
        pending_source_roots = tuple(
            pending_funding_closeout_source_availability_hashes
        )  # type: ignore[arg-type]
    if (
        pending_funding_closeout_carried_liability_hashes
        is _KEEP_PENDING_FUNDING_CLOSEOUT_CARRIED_ROOTS
    ):
        pending_carried_roots = tuple(
            getattr(market, "pending_funding_closeout_carried_liability_hashes", ())
        )
    else:
        pending_carried_roots = tuple(
            pending_funding_closeout_carried_liability_hashes
        )  # type: ignore[arg-type]
    if (
        funding_closeout_policy_ledger_hashes
        is _KEEP_FUNDING_CLOSEOUT_POLICY_LEDGER_ROOTS
    ):
        policy_ledger_roots = tuple(
            getattr(market, "funding_closeout_policy_ledger_hashes", ())
        )
    else:
        policy_ledger_roots = tuple(
            funding_closeout_policy_ledger_hashes
        )  # type: ignore[arg-type]
    if (
        funding_closeout_sink_claimant_balances_quote
        is _KEEP_FUNDING_CLOSEOUT_SINK_CLAIMANT_BALANCES
    ):
        sink_claimant_balances = tuple(
            getattr(market, "funding_closeout_sink_claimant_balances_quote", ())
        )
    else:
        sink_claimant_balances = tuple(
            funding_closeout_sink_claimant_balances_quote
        )  # type: ignore[arg-type]
    if (
        funding_closeout_receiver_claim_balances_quote
        is _KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_BALANCES
    ):
        receiver_claim_balances = tuple(
            getattr(market, "funding_closeout_receiver_claim_balances_quote", ())
        )
    else:
        receiver_claim_balances = tuple(
            funding_closeout_receiver_claim_balances_quote
        )  # type: ignore[arg-type]
    if (
        funding_closeout_receiver_claim_lots_quote
        is _KEEP_FUNDING_CLOSEOUT_RECEIVER_CLAIM_LOTS
    ):
        receiver_claim_lots = tuple(
            getattr(market, "funding_closeout_receiver_claim_lots_quote", ())
        )
    else:
        receiver_claim_lots = tuple(
            funding_closeout_receiver_claim_lots_quote
        )  # type: ignore[arg-type]
    return PerpMarketState(
        quote_asset=market.quote_asset,
        global_state=dict(global_state),
        accounts=dict(accounts),
        pending_funding_closeout_root_hashes=pending_roots,
        pending_funding_closeout_source_availability_hashes=pending_source_roots,
        pending_funding_closeout_carried_liability_hashes=pending_carried_roots,
        funding_closeout_policy_ledger_hashes=policy_ledger_roots,
        funding_closeout_sink_claimant_balances_quote=sink_claimant_balances,
        funding_closeout_receiver_claim_balances_quote=receiver_claim_balances,
        funding_closeout_receiver_claim_lots_quote=receiver_claim_lots,
    )


def _funding_closeout_receiver_claim_lot_id(
    *,
    policy_hash: str | None,
    account_pubkey: str,
) -> str:
    payload = {
        "schema": "zenodex.perps.funding_closeout.receiver_claim_lot.v1",
        "policy_hash": policy_hash or "unbound-policy",
        "account_pubkey": str(account_pubkey),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _legacy_funding_closeout_receiver_claim_lot_id(account_pubkey: str) -> str:
    payload = {
        "schema": "zenodex.perps.funding_closeout.receiver_claim_legacy_lot.v1",
        "account_pubkey": str(account_pubkey),
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _receiver_claim_lots_for_mutation(
    market: PerpMarketState,
    *,
    materialize_legacy_balances: bool,
) -> tuple[tuple[str, str, int, int], ...]:
    lots = tuple(getattr(market, "funding_closeout_receiver_claim_lots_quote", ()))
    if lots or not materialize_legacy_balances:
        return lots
    balances = tuple(
        getattr(market, "funding_closeout_receiver_claim_balances_quote", ())
    )
    return tuple(
        (
            str(account_pubkey),
            _legacy_funding_closeout_receiver_claim_lot_id(str(account_pubkey)),
            int(balance_quote),
            FUNDING_CLOSEOUT_RECEIVER_CLAIM_NO_EXPIRY_EPOCH,
        )
        for account_pubkey, balance_quote in balances
    )


def _add_funding_closeout_receiver_claim_lots(
    market: PerpMarketState,
    *,
    receiver_claims_by_account: Mapping[str, int],
    policy_hash: str | None,
) -> tuple[tuple[str, str, int, int], ...]:
    claims = {
        str(account_pubkey): int(claim_quote)
        for account_pubkey, claim_quote in dict(receiver_claims_by_account).items()
        if int(claim_quote) != 0
    }
    lots = list(
        _receiver_claim_lots_for_mutation(
            market,
            materialize_legacy_balances=bool(claims),
        )
    )
    by_key = {
        (str(account_pubkey), str(lot_id)): (
            str(account_pubkey),
            str(lot_id),
            int(balance_quote),
            int(expires_at_epoch),
        )
        for account_pubkey, lot_id, balance_quote, expires_at_epoch in lots
    }
    for account_pubkey, claim_quote in claims.items():
        claim = int(claim_quote)
        if claim == 0:
            continue
        lot_id = _funding_closeout_receiver_claim_lot_id(
            policy_hash=policy_hash,
            account_pubkey=str(account_pubkey),
        )
        key = (str(account_pubkey), lot_id)
        existing = by_key.get(key)
        if existing is None:
            by_key[key] = (
                str(account_pubkey),
                lot_id,
                int(claim),
                FUNDING_CLOSEOUT_RECEIVER_CLAIM_NO_EXPIRY_EPOCH,
            )
            continue
        by_key[key] = (
            existing[0],
            existing[1],
            int(existing[2]) + int(claim),
            existing[3],
        )
    return tuple(sorted(by_key.values(), key=lambda row: (row[0], row[3], row[1])))


def _debit_funding_closeout_receiver_claim_lots(
    market: PerpMarketState,
    receiver_recoveries: Mapping[str, int],
) -> tuple[Optional[str], tuple[tuple[str, str, int, int], ...], list[dict[str, Any]]]:
    rows = list(
        _receiver_claim_lots_for_mutation(
            market,
            materialize_legacy_balances=True,
        )
    )
    debits: list[dict[str, Any]] = []
    for account_pubkey, recovery_quote in sorted(receiver_recoveries.items()):
        remaining = int(recovery_quote)
        if remaining == 0:
            continue
        for index, row in enumerate(list(rows)):
            lot_account, lot_id, balance_quote, expires_at_epoch = row
            if lot_account != account_pubkey or remaining == 0:
                continue
            debit = min(int(balance_quote), remaining)
            next_balance = int(balance_quote) - debit
            remaining -= debit
            debits.append(
                {
                    "account_pubkey": lot_account,
                    "lot_id": lot_id,
                    "debited_quote": int(debit),
                    "remaining_lot_balance_quote": int(next_balance),
                    "expires_at_epoch": int(expires_at_epoch),
                }
            )
            if next_balance == 0:
                rows[index] = ("", "", 0, 0)
            else:
                rows[index] = (lot_account, lot_id, next_balance, expires_at_epoch)
        rows = [row for row in rows if row[2] > 0]
        if remaining != 0:
            return "funding closeout recovery exceeds receiver claim lot balance", (), []
    next_lots = tuple(sorted(rows, key=lambda row: (row[0], row[3], row[1])))
    return None, next_lots, debits


def _isolated_open_position_accounts(accounts: Mapping[str, PerpAccountState]) -> tuple[PositionAccount, ...]:
    return tuple(
        PositionAccount(str(account_pubkey), int(account.position_base))
        for account_pubkey, account in sorted(accounts.items())
        if int(account.position_base) != 0
    )


def _append_pending_funding_closeout_root(
    market: PerpMarketState,
    root_hash: str,
) -> tuple[str, ...]:
    return tuple(sorted(set(tuple(getattr(market, "pending_funding_closeout_root_hashes", ())) + (root_hash,))))


def _append_pending_funding_closeout_source_availability_hash(
    market: PerpMarketState,
    root_hash: str,
) -> tuple[str, ...]:
    existing = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    return tuple(sorted(set(existing + (root_hash,))))


def _append_pending_funding_closeout_carried_liability_hash(
    market: PerpMarketState,
    root_hash: str,
) -> tuple[str, ...]:
    existing = tuple(
        getattr(market, "pending_funding_closeout_carried_liability_hashes", ())
    )
    return tuple(sorted(set(existing + (root_hash,))))


def _append_funding_closeout_policy_ledger_hash(
    market: PerpMarketState,
    root_hash: str,
) -> tuple[str, ...]:
    existing = tuple(getattr(market, "funding_closeout_policy_ledger_hashes", ()))
    return tuple(sorted(set(existing + (root_hash,))))


def _remove_funding_closeout_policy_ledger_hash(
    market: PerpMarketState,
    root_hash: str,
) -> tuple[str, ...]:
    existing = tuple(getattr(market, "funding_closeout_policy_ledger_hashes", ()))
    return tuple(root for root in existing if root != root_hash)


def _isolated_pending_funding_closeout_boundary_error(
    action: str,
    market: PerpMarketState,
) -> Optional[str]:
    pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    pending_source_roots = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    if pending_roots or pending_source_roots:
        return (
            f"{action} requires pending funding closeout liabilities "
            "to be consumed before epoch boundary"
        )
    return None


def _funding_closeout_source_availability_row_for_closeout(
    *,
    account_pubkey: str,
    epoch: int,
    result: _IsolatedPartialLiquidateResult,
) -> ClosedFundingSourceRow:
    return ClosedFundingSourceRow(
        account_pubkey=str(account_pubkey),
        epoch=int(epoch),
        payer_available_quote=max(0, int(result.account.collateral_quote)),
        sink_capacity_quote=max(0, int(result.global_state.get("fee_pool_quote", 0))),
    )


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


def _ceil_div_nonnegative(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    if numerator < 0:
        raise ValueError("numerator must be non-negative")
    return (numerator + denominator - 1) // denominator


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


def _check_isolated_settle_oracle_authorization(
    *,
    ctx: "_PerpApplyCtx",
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    authorization = op.data.get("oracle_authorization")
    if authorization is None:
        if ctx.config.require_oracle_authorization_for_isolated_settle:
            return "oracle_authorization_required"
        return None
    if not isinstance(authorization, Mapping):
        return "oracle_authorization must be an object"
    if not bool(market.global_state.get("oracle_seen", False)):
        return "oracle_authorization_rejected: oracle snapshot not seen"
    if int(market.global_state.get("index_price_e8", 0)) <= 0:
        return "oracle_authorization_rejected: index_price_e8 must be positive"

    runtime = _isolated_settle_oracle_runtime_facts(market_id=op.market_id, market=market)
    runtime_value_e8 = runtime.get("runtime_value_e8")
    now_epoch = runtime.get("now_epoch")
    if (
        not isinstance(runtime_value_e8, int)
        or isinstance(runtime_value_e8, bool)
        or not isinstance(now_epoch, int)
        or isinstance(now_epoch, bool)
    ):
        return "oracle_authorization_rejected: malformed runtime facts"
    try:
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            action_id=str(runtime["action_id"]),
            action_facts_hash=str(runtime["action_facts_hash"]),
            pre_state_hash=str(runtime["pre_state_hash"]),
            query_id=str(runtime["query_id"]),
            runtime_value_e8=runtime_value_e8,
            now_epoch=now_epoch,
            expected_receipt_graph_root=ctx.config.oracle_authorization_receipt_graph_root,
        )
    except Exception as exc:
        return f"oracle_authorization_rejected: {_safe_error_str(exc)}"
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


_PERP_SUPPORTED_VERSIONS = frozenset(
    {
        PERP_OP_VERSION_V0_1,
        PERP_OP_VERSION_CH2P_V0_2,
        PERP_OP_VERSION_CH2P_V1_0,
        PERP_OP_VERSION_CH3P_V1_1,
        PERP_OP_VERSION_CHNP_V1_2,
    }
)


def _select_perp_ops_stream(operations: Mapping[str, Any]) -> tuple[str, Any]:
    if PERP_OPS_KEY in operations and LEGACY_PERP_OPS_KEY in operations:
        raise ValueError("ambiguous perps streams: use either upstream stream 8 or legacy stream 5")
    selected_key = PERP_OPS_KEY if PERP_OPS_KEY in operations else LEGACY_PERP_OPS_KEY
    return selected_key, operations.get(selected_key)


def _validated_perp_op_obj(
    entry: Any,
    *,
    index: int,
    max_op_bytes: int,
    max_int_bits: int,
) -> tuple[Dict[str, Any], int]:
    if not isinstance(entry, Mapping):
        raise ValueError(f"perps op {index} must be an object")
    op_obj = dict(entry)
    _assert_ints_within_bits(op_obj, max_bits=max_int_bits, name=f"perps op {index}")
    try:
        op_bytes = bounded_json_utf8_size(op_obj, max_bytes=max_op_bytes)
    except ValueError:
        raise ValueError(f"perps op {index} too large") from None
    except TypeError as exc:
        raise ValueError(f"invalid perps op {index}: {exc}") from exc
    return op_obj, int(op_bytes)


def _parse_perp_module(op_obj: Mapping[str, Any]) -> str:
    module = _require_ascii_token(
        op_obj.get("module"),
        name="perps.module",
        max_len=64,
        allowed=_ASCII_TOKEN_CHARS_MODULE,
    )
    if module != PERP_OP_MODULE:
        raise ValueError(f"invalid perps module: {module}")
    return module


def _parse_perp_version(op_obj: Mapping[str, Any]) -> str:
    version = _require_ascii_token(
        op_obj.get("version"),
        name="perps.version",
        max_len=64,
        allowed=_ASCII_TOKEN_CHARS_VERSION,
    )
    if version not in _PERP_SUPPORTED_VERSIONS:
        raise ValueError(f"invalid perps version: {version}")
    return version


def _parse_perp_market_id(op_obj: Mapping[str, Any]) -> str:
    return _require_ascii_token(
        op_obj.get("market_id"),
        name="perps.market_id",
        max_len=256,
        allowed=_ASCII_TOKEN_CHARS_MARKET_ID,
    )


def _validate_perp_market_version_prefix(*, version: str, market_id: str) -> None:
    is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
    is_ch3p = version == PERP_OP_VERSION_CH3P_V1_1
    is_chnp = version == PERP_OP_VERSION_CHNP_V1_2
    if is_chnp:
        if not market_id.startswith(PERP_CHNP_MARKET_PREFIX):
            raise ValueError(f"clearinghouse_np markets must start with {PERP_CHNP_MARKET_PREFIX!r}")
        return
    if market_id.startswith(PERP_CHNP_MARKET_PREFIX):
        raise ValueError("non-NP perps markets cannot start with clearinghouse_np prefix")

    version_prefix_guard = evaluate_perp_market_version_prefix_guard(
        version_is_v0_1=version == PERP_OP_VERSION_V0_1,
        version_is_ch2p=is_ch2p,
        version_is_ch3p=is_ch3p,
        market_has_ch2p_prefix=market_id.startswith(PERP_CH2P_MARKET_PREFIX),
        market_has_ch3p_prefix=market_id.startswith(PERP_CH3P_MARKET_PREFIX),
    )
    if version_prefix_guard.admission_ok:
        return
    if version_prefix_guard.reject_code == REJECT_INVALID_VERSION:
        raise ValueError(f"invalid perps version: {version}")
    if version_prefix_guard.reject_code == REJECT_CH2P_PREFIX_MISMATCH:
        raise ValueError(f"clearinghouse markets must start with {PERP_CH2P_MARKET_PREFIX!r}")
    if version_prefix_guard.reject_code == REJECT_CH3P_PREFIX_MISMATCH:
        raise ValueError(f"clearinghouse markets must start with {PERP_CH3P_MARKET_PREFIX!r}")
    if version_prefix_guard.reject_code == REJECT_ISOLATED_PREFIX_CONFLICT:
        raise ValueError("isolated markets cannot start with clearinghouse prefixes")
    raise ValueError("invalid perps version/prefix posture")


def _parse_perp_action(op_obj: Mapping[str, Any]) -> str:
    return _require_ascii_token(
        op_obj.get("action"),
        name="perps.action",
        max_len=64,
        allowed=_ASCII_TOKEN_CHARS_ACTION,
    )


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

    selected_key, raw = _select_perp_ops_stream(operations)
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError(f"operations[{selected_key!r}] must be a list")
    if len(raw) > max_ops:
        raise ValueError(f"too many perps ops: {len(raw)} > {max_ops}")

    total_bytes = 0
    out: List[PerpOp] = []
    for i, entry in enumerate(raw):
        op_obj, op_bytes = _validated_perp_op_obj(
            entry,
            index=i,
            max_op_bytes=max_op_bytes,
            max_int_bits=max_int_bits,
        )
        total_bytes += op_bytes
        if total_bytes > max_total_ops_bytes:
            raise ValueError("perps ops too large (total bytes limit)")

        _parse_perp_module(op_obj)
        version = _parse_perp_version(op_obj)
        market_id = _parse_perp_market_id(op_obj)
        _validate_perp_market_version_prefix(version=version, market_id=market_id)
        action = _parse_perp_action(op_obj)
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
    except (TypeError, ValueError) as exc:
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


@dataclass(frozen=True)
class _OracleAdapterBridgeRequirement:
    config: PerpEngineConfig
    data: Mapping[str, Any]
    consumer_module: str
    action_kind: str
    expected_query_id: Optional[str] = None
    expected_profile_id: Optional[str] = None
    expected_action_id: Optional[str] = None
    expected_runtime_value_e8: Optional[int] = None
    expected_runtime_epoch: Optional[int] = None
    required: bool = False


@dataclass(frozen=True)
class _LiquidateAccountOracleRuntimeRequest:
    config: PerpEngineConfig
    market_id: str
    market: PerpMarketState
    account_pubkey: str
    fraction_bps: int


@dataclass(frozen=True)
class _ClearinghouseOracleRuntimeRequest:
    config: PerpEngineConfig
    market_id: str
    action_kind: str
    market_kind: str
    quote_asset: str
    state: Mapping[str, Any]
    participant_pubkeys: tuple[str, ...]


def _check_oracle_adapter_bridge(
    requirement: _OracleAdapterBridgeRequirement,
) -> tuple[Optional[str], Any | None]:
    if "oracle_adapter_bridge" not in requirement.data:
        if requirement.required:
            return f"{requirement.action_kind} requires oracle_adapter_bridge", None
        return None, None

    bridge = requirement.data.get("oracle_adapter_bridge")
    if not isinstance(bridge, Mapping):
        return "oracle_adapter_bridge must be an object", None
    verifier = requirement.config.oracle_adapter_bridge_verifier
    if verifier is None:
        return "oracle_adapter_bridge verifier not configured", None
    try:
        result = verifier(bridge)
    except Exception as exc:
        return f"oracle_adapter_bridge verifier error: {_safe_error_str(exc)}", None

    if _oracle_adapter_result_get(result, "status") != "accepted":
        return (
            f"oracle_adapter_bridge rejected: {_oracle_adapter_error_summary(result)}",
            None,
        )
    result_consumer = _oracle_adapter_result_get(result, "consumer_module")
    result_action = _oracle_adapter_result_get(result, "action_kind")
    if result_consumer != requirement.consumer_module:
        return "oracle_adapter_bridge consumer mismatch", None
    if result_action != requirement.action_kind:
        return "oracle_adapter_bridge action mismatch", None
    result_query_id = _oracle_adapter_result_get(result, "query_id")
    if requirement.expected_query_id is not None and result_query_id != requirement.expected_query_id:
        return "oracle_adapter_bridge query mismatch", None
    result_profile_id = _oracle_adapter_result_get(result, "profile_id")
    if requirement.expected_profile_id is not None and result_profile_id != requirement.expected_profile_id:
        return "oracle_adapter_bridge profile mismatch", None
    result_action_id = _oracle_adapter_result_get(result, "action_id")
    if requirement.expected_action_id is not None and result_action_id != requirement.expected_action_id:
        return "oracle_adapter_bridge action_id mismatch", None
    if requirement.expected_runtime_value_e8 is not None:
        expected_value_e8 = requirement.expected_runtime_value_e8
        if not isinstance(expected_value_e8, int) or isinstance(expected_value_e8, bool):
            return "oracle_adapter_bridge runtime value_e8 must be a non-bool int", None
        result_value_e8 = _oracle_adapter_result_get(result, "value_e8")
        if not isinstance(result_value_e8, int) or isinstance(result_value_e8, bool):
            return "oracle_adapter_bridge value_e8 must be a non-bool int", None
        if result_value_e8 != expected_value_e8:
            return "oracle_adapter_bridge value_e8 mismatch", None
    if requirement.expected_runtime_epoch is not None:
        expected_epoch = requirement.expected_runtime_epoch
        if not isinstance(expected_epoch, int) or isinstance(expected_epoch, bool):
            return "oracle_adapter_bridge runtime epoch must be a non-bool int", None
        result_action_epoch = _oracle_adapter_result_get(result, "action_epoch")
        if not isinstance(result_action_epoch, int) or isinstance(result_action_epoch, bool):
            return "oracle_adapter_bridge action_epoch must be a non-bool int", None
        if result_action_epoch != expected_epoch:
            return "oracle_adapter_bridge action_epoch mismatch", None
    return None, result


def _require_oracle_adapter_bridge(
    requirement: _OracleAdapterBridgeRequirement,
) -> Optional[str]:
    err, _result = _check_oracle_adapter_bridge(requirement)
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
    request: _LiquidateAccountOracleRuntimeRequest,
) -> str:
    global_state = request.market.global_state
    acct = request.market.accounts.get(request.account_pubkey) or _kernel_initial_account_state()
    payload = {
        "schema": "zenodex.oracle.perps_runtime_action_id.v1",
        "chain_id": request.config.chain_id,
        "consumer_module": "zenodex.perps",
        "action_kind": "liquidate_account",
        "market_id": request.market_id,
        "quote_asset": request.market.quote_asset,
        "account_pubkey": str(request.account_pubkey),
        "fraction_bps": int(request.fraction_bps),
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
    request: _ClearinghouseOracleRuntimeRequest,
) -> str:
    payload = {
        "schema": "zenodex.oracle.perps_clearinghouse_runtime_action_id.v1",
        "chain_id": request.config.chain_id,
        "consumer_module": "zenodex.perps",
        "action_kind": request.action_kind,
        "market_kind": request.market_kind,
        "market_id": request.market_id,
        "quote_asset": request.quote_asset,
        "participant_pubkeys": list(request.participant_pubkeys),
        "now_epoch": int(request.state.get("now_epoch", 0)),
        "clearing_price_epoch": int(request.state.get("clearing_price_epoch", 0)),
        "clearing_price_e8": int(request.state.get("clearing_price_e8", 0)),
        "index_price_e8": int(request.state.get("index_price_e8", 0)),
        "oracle_last_update_epoch": int(request.state.get("oracle_last_update_epoch", 0)),
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
        _ClearinghouseOracleRuntimeRequest(
            config=config,
            market_id=market_id,
            action_kind="settle_epoch",
            market_kind=market_kind,
            quote_asset=quote_asset,
            state=state,
            participant_pubkeys=participant_pubkeys,
        )
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
        "runtime_value_e8": int(state.get("clearing_price_e8", 0)),
    }


def _clearinghouse_settle_runtime_numbers(
    runtime: Mapping[str, Any],
) -> tuple[Optional[str], Optional[int], Optional[int]]:
    runtime_value_e8 = runtime.get("runtime_value_e8")
    now_epoch = runtime.get("now_epoch")
    if (
        not isinstance(runtime_value_e8, int)
        or isinstance(runtime_value_e8, bool)
        or not isinstance(now_epoch, int)
        or isinstance(now_epoch, bool)
    ):
        # Runtime facts are produced locally, but this boundary feeds the typed
        # oracle verifier. Reject malformed facts before verifier input.
        return "clearinghouse_settle_oracle_authorization_rejected: malformed runtime facts", None, None
    return None, runtime_value_e8, now_epoch


def _check_clearinghouse_typed_oracle_authorization(
    authorization: Mapping[str, Any],
    *,
    config: PerpEngineConfig,
    runtime: Mapping[str, Any],
    runtime_value_e8: int,
    now_epoch: int,
) -> Optional[str]:
    try:
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            action_id=str(runtime["action_id"]),
            action_facts_hash=str(runtime["action_facts_hash"]),
            pre_state_hash=str(runtime["pre_state_hash"]),
            query_id=str(runtime["query_id"]),
            runtime_value_e8=runtime_value_e8,
            now_epoch=now_epoch,
            profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            max_freshness_window_epochs=2,
            expected_receipt_graph_root=config.oracle_authorization_receipt_graph_root,
        )
    except Exception as exc:
        return f"clearinghouse_settle_oracle_authorization_rejected: {_safe_error_str(exc)}"
    if not bool(result.get("typed_ok", False)):
        errors = result.get("typed_errors") or result.get("opaque_errors") or ["typed authorization rejected"]
        return "clearinghouse_settle_oracle_authorization_rejected: " + "; ".join(str(err) for err in errors)
    return None


@dataclass(frozen=True)
class _ClearinghouseSettleOracleAuthorizationRequest:
    config: PerpEngineConfig
    data: Mapping[str, Any]
    market_id: str
    market_kind: str
    quote_asset: str
    state: Mapping[str, Any]
    participant_pubkeys: tuple[str, ...]


def _check_clearinghouse_settle_oracle_authorization(
    request: _ClearinghouseSettleOracleAuthorizationRequest,
) -> Optional[str]:
    authorization_required = bool(request.config.require_oracle_authorization_for_clearinghouse_settle_epoch)
    authorization = request.data.get("oracle_authorization")
    if authorization is None:
        if authorization_required:
            return "clearinghouse_settle_oracle_authorization_required"
        return None
    if not isinstance(authorization, Mapping):
        return "clearinghouse settle oracle_authorization must be an object"
    if authorization_required and "oracle_adapter_bridge" not in request.data:
        return "settle_epoch requires oracle_adapter_bridge"
    if int(request.state.get("clearing_price_e8", 0)) <= 0:
        return "clearinghouse_settle_oracle_authorization_rejected: clearing_price_e8 must be positive"

    runtime = _perps_clearinghouse_settle_oracle_runtime_facts(
        request.config,
        market_id=request.market_id,
        market_kind=request.market_kind,
        quote_asset=request.quote_asset,
        state=request.state,
        participant_pubkeys=request.participant_pubkeys,
    )
    err, runtime_value_e8, now_epoch = _clearinghouse_settle_runtime_numbers(runtime)
    if err is not None:
        return err
    if runtime_value_e8 is None or now_epoch is None:
        return "clearinghouse_settle_oracle_authorization_rejected: malformed runtime facts"

    return _check_clearinghouse_typed_oracle_authorization(
        authorization,
        config=request.config,
        runtime=runtime,
        runtime_value_e8=runtime_value_e8,
        now_epoch=now_epoch,
    )


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


@dataclass(frozen=True)
class _PerpSignaturePrecheck:
    signer_nonce_key: str
    deadline_ok: bool
    nonce_domain_ok: bool
    nonce_expected_ok: bool


@dataclass(frozen=True)
class _PerpSignatureVerificationRequest:
    config: PerpEngineConfig
    signer_pubkey: str
    nonce: int
    signature: str
    op: Mapping[str, Any]
    nonces: NonceTable
    block_timestamp: int


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


def _perp_submission_auth_error(precheck: _PerpSignaturePrecheck, *, signature_ok: bool) -> Optional[str]:
    outcome = evaluate_perp_submission_auth_gate(
        mode_signed=True,
        mode_sender_bound=False,
        signed_surface_ok=True,
        signer_role_set_ok=True,
        deadline_ok=precheck.deadline_ok,
        nonce_domain_ok=precheck.nonce_domain_ok,
        nonce_expected_ok=precheck.nonce_expected_ok,
        signature_ok=signature_ok,
        tx_sender_binding_ok=True,
    )
    if outcome.admission_ok:
        return None
    return perp_submission_auth_gate_error(outcome) or "signed auth rejected"


def _precheck_perp_signature(
    request: _PerpSignatureVerificationRequest,
) -> tuple[Optional[str], Optional[_PerpSignaturePrecheck]]:
    try:
        signer_nonce_key = canonical_hex_fixed_allow_0x(request.signer_pubkey, nbytes=48, name="signer_pubkey")
    except (TypeError, ValueError) as exc:
        return str(exc), None

    try:
        deadline = _require_int(request.op.get("deadline"), name="deadline", non_negative=True)
    except ValueError as exc:
        return _safe_error_str(exc), None

    nonce_domain_ok = (
        isinstance(request.nonce, int) and not isinstance(request.nonce, bool) and 0 < int(request.nonce) <= _U32_MAX
    )
    expected = int(request.nonces.get_last(signer_nonce_key)) + 1
    precheck = _PerpSignaturePrecheck(
        signer_nonce_key=signer_nonce_key,
        deadline_ok=int(request.block_timestamp) <= int(deadline),
        nonce_domain_ok=nonce_domain_ok,
        nonce_expected_ok=bool(nonce_domain_ok and int(request.nonce) == expected),
    )
    auth_error = _perp_submission_auth_error(precheck, signature_ok=True)
    if auth_error is not None:
        return auth_error, None
    return None, precheck


def _perp_signature_bytes(*, signer_pubkey: str, signature: str) -> tuple[Optional[str], Optional[bytes], Optional[bytes]]:
    try:
        pubkey_bytes = _hex_to_bytes_allow_0x(signer_pubkey, name="signer_pubkey", expected_nbytes=48)
        sig_bytes = _hex_to_bytes_allow_0x(signature, name="signature", expected_nbytes=96)
    except (TypeError, ValueError) as exc:
        return str(exc), None, None
    return None, pubkey_bytes, sig_bytes


def _verify_perp_bls_signature(
    request: _PerpSignatureVerificationRequest,
    *,
    pubkey_bytes: bytes,
    sig_bytes: bytes,
) -> tuple[Optional[str], bool]:
    try:
        msg_hash = hash_perp_op_auth_message_v1(
            request.op,
            chain_id=request.config.chain_id,
            signer_pubkey=request.signer_pubkey,
            nonce=int(request.nonce),
        )
        return None, bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))
    except Exception as exc:
        return f"signature verification error: {_safe_error_str(exc)}", False


def _verify_perp_op_signature(request: _PerpSignatureVerificationRequest) -> Optional[str]:
    """Verify and consume a per-op signature (fail-closed).

    Verification steps (in order):
    1) Validate pubkey/signature encoding.
    2) Check deadline against `block_timestamp`.
    3) Enforce the expected next nonce (per signer).
    4) Reconstruct the canonical signing dict and verify the BLS signature over
       a domain-separated hash (bound to `config.chain_id`).
    5) Consume the nonce **only after** successful signature verification.

    """
    if not _BLS_AVAILABLE:
        return "BLS verification not available (install py-ecc)"

    err, precheck = _precheck_perp_signature(request)
    if err is not None:
        return err
    if precheck is None:
        return "signed auth rejected"

    err, pubkey_bytes, sig_bytes = _perp_signature_bytes(
        signer_pubkey=request.signer_pubkey,
        signature=request.signature,
    )
    if err is not None:
        return err
    if pubkey_bytes is None or sig_bytes is None:
        return "invalid signature"

    err, signature_ok = _verify_perp_bls_signature(
        request,
        pubkey_bytes=pubkey_bytes,
        sig_bytes=sig_bytes,
    )
    if err is not None:
        return err
    auth_error = _perp_submission_auth_error(precheck, signature_ok=signature_ok)
    if auth_error is not None:
        return auth_error

    # Commit nonce consumption after signature verification.
    request.nonces.set_last(precheck.signer_nonce_key, int(request.nonce))
    return None


def _require_sender_bound_account_pubkey(*, account_pubkey: str, tx_sender_pubkey: str) -> str | None:
    try:
        acct_b = _hex_to_bytes_allow_0x(account_pubkey, name="account_pubkey", expected_nbytes=48)
        sender_b = _hex_to_bytes_allow_0x(tx_sender_pubkey, name="tx_sender_pubkey", expected_nbytes=48)
    except (TypeError, ValueError) as exc:
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
    perps_version: int


@dataclass(frozen=True)
class _IsolatedSettleAccounting:
    fee_pool_quote: int
    fee_income_quote: int
    initial_insurance_quote: int
    claims_paid_quote: int
    insurance_balance_quote: int


@dataclass(frozen=True)
class _IsolatedSettleGlobalStep:
    global_state: Dict[str, Any]
    effects: Dict[str, Any]


@dataclass(frozen=True)
class _IsolatedSettleAccountStep:
    account: PerpAccountState
    fee_pool_delta_quote: int
    raw_liquidation_penalty_quote: int


@dataclass(frozen=True)
class _IsolatedSettleTotals:
    accounts: Dict[str, PerpAccountState]
    penalty_delta_quote: int
    raw_liquidation_penalty_quote: int
    liquidation_penalty_shortfall_quote: int
    liquidation_penalty_cap_bound_count: int


@dataclass(frozen=True)
class _IsolatedFundingSnapshot:
    now_epoch: int
    pre_fee_pool_quote: int
    pre_fee_income_quote: int
    pre_insurance_balance_quote: int
    max_fee_pool_quote: int
    open_accounts: tuple[tuple[str, PerpAccountState], ...]
    any_funding_applied_this_epoch: bool


@dataclass(frozen=True)
class _IsolatedFundingAccountApply:
    accounts: Dict[str, PerpAccountState]
    applied_accounts: int


@dataclass(frozen=True)
class _IsolatedCarriedFundingSettlement:
    accounts: Dict[str, PerpAccountState]
    total_claim_quote: int
    total_payable_quote: int
    total_haircut_quote: int
    receiver_payments_by_account: Mapping[str, int]
    receiver_haircuts_by_account: Mapping[str, int]


@dataclass(frozen=True)
class _IsolatedFundingCloseoutAdmission:
    projected_net_funding_quote: int
    receiver_haircut_quote: int
    receiver_haircuts_by_account: Mapping[str, int]
    allocation_receipt_applied: bool
    policy_ledger_hash: str | None = None
    policy_ledger_payload: Mapping[str, Any] | None = None
    receiver_claims_by_account: Mapping[str, int] | None = None


@dataclass(frozen=True)
class _IsolatedPartialLiquidateResult:
    global_state: Mapping[str, Any]
    account: PerpAccountState
    effects: Mapping[str, Any]


@dataclass(frozen=True)
class _InitMarketNpInputs:
    quote_asset: str
    index_price_e8: int
    insurance_seed_e8: int
    insurance_seed_quote: int
    params_obj: Mapping[str, Any]


def _reject_unknown_fields(data: Mapping[str, Any], allowed: set[str], *, error: str) -> Optional[str]:
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


@dataclass(frozen=True)
class _ClearinghouseKernelCommit:
    i: int
    op: PerpOp
    market: Any
    step: Callable[..., tuple[Dict[str, Any], Dict[str, Any]]]
    replace_state: Callable[..., PerpAnyMarketState]
    tag: str
    args: Mapping[str, Any]


@dataclass(frozen=True)
class _ClearinghousePublishPriceRequest:
    i: int
    op: PerpOp
    market: Any
    version_ok: bool
    step: Callable[..., tuple[Dict[str, Any], Dict[str, Any]]]
    replace_state: Callable[..., PerpAnyMarketState]


@dataclass(frozen=True)
class _ClearinghouseMarketParamsRequest:
    i: int
    op: PerpOp
    market: Any
    market_kind: int
    kind: str
    replace_state: Callable[..., PerpAnyMarketState]


@dataclass(frozen=True)
class _ClearinghouseCollateralRequest:
    i: int
    op: PerpOp
    market: Any
    market_label: str
    step: Callable[..., tuple[Dict[str, Any], Dict[str, Any]]]
    replace_state: Callable[..., PerpAnyMarketState]


@dataclass(frozen=True)
class _Ch2pPositionAuth:
    nonce_a: int
    sig_a: str
    nonce_b: int
    sig_b: str


@dataclass(frozen=True)
class _Ch2pPositionAccounts:
    account_a_pubkey: str
    account_b_pubkey: str


@dataclass(frozen=True)
class _Ch2pPositionValues:
    new_a: int
    new_b: int


@dataclass(frozen=True)
class _InitMarket2pSpec:
    quote_asset: str
    accounts: _Ch2pPositionAccounts


@dataclass(frozen=True)
class _Ch3pPositionAuth:
    nonce_a: int
    sig_a: str
    nonce_b: int
    sig_b: str
    nonce_c: int
    sig_c: str


@dataclass(frozen=True)
class _Ch3pPositionAccounts:
    account_a_pubkey: str
    account_b_pubkey: str
    account_c_pubkey: str


@dataclass(frozen=True)
class _Ch3pPositionValues:
    new_a: int
    new_b: int
    new_c: int


@dataclass(frozen=True)
class _InitMarket3pSpec:
    quote_asset: str
    accounts: _Ch3pPositionAccounts


def _commit_clearinghouse_kernel_step(ctx: _PerpApplyCtx, commit: _ClearinghouseKernelCommit) -> str | None:
    try:
        next_state, eff = commit.step(commit.market.state, tag=commit.tag, args=commit.args)
    except ValueError as exc:
        return str(exc)
    ctx.markets[commit.op.market_id] = commit.replace_state(commit.market, state=next_state)
    ctx.effects.append({"i": commit.i, "market_id": commit.op.market_id, "action": commit.op.action, "effects": eff})
    return None


_PUBLISH_CLEARING_PRICE_FIELDS = frozenset(
    {"module", "version", "market_id", "action", "price_e8", "deadline", "oracle_nonce", "oracle_sig"}
)


def _read_clearinghouse_signed_price(
    ctx: _PerpApplyCtx, request: _ClearinghousePublishPriceRequest
) -> tuple[str | None, int | None]:
    data = request.op.data
    oracle_pubkey = (ctx.config.oracle_pubkey or "").strip()
    if not oracle_pubkey:
        return "oracle signer not configured (set PerpEngineConfig.oracle_pubkey)", None
    if not request.version_ok:
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_PUBLISH_CLEARING_PRICE,
            action=request.op.action,
            version_ok=False,
            unknown_fields_ok=True,
        )
        return surface_err or "publish_clearing_price requires a clearinghouse perps.version", None

    oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
    oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)

    unknown_fields_ok = not (set(data.keys()) - _PUBLISH_CLEARING_PRICE_FIELDS)
    if not unknown_fields_ok:
        surface_err = _evaluate_signed_surface(
            action_kind=ACTION_PUBLISH_CLEARING_PRICE,
            action=request.op.action,
            version_ok=request.version_ok,
            unknown_fields_ok=False,
        )
        return surface_err or "publish_clearing_price has unknown fields", None

    price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_PUBLISH_CLEARING_PRICE,
        action=request.op.action,
        version_ok=request.version_ok,
        unknown_fields_ok=unknown_fields_ok,
        positive_price_ok=price_e8 > 0,
    )
    if surface_err is not None:
        return surface_err, None

    sig_err = _verify_perp_op_signature(
        _PerpSignatureVerificationRequest(
            config=ctx.config,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
            signature=oracle_sig,
            op=data,
            nonces=ctx.nonces,
            block_timestamp=ctx.block_timestamp,
        )
    )
    if sig_err is not None:
        return f"oracle signature invalid: {sig_err}", None
    return None, price_e8


def _apply_clearinghouse_publish_clearing_price(
    ctx: _PerpApplyCtx, request: _ClearinghousePublishPriceRequest
) -> str | None:
    err, price_e8 = _read_clearinghouse_signed_price(ctx, request)
    if err is not None:
        return err
    if price_e8 is None:
        return "internal error: publish_clearing_price missing price"

    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(
            request.i,
            request.op,
            request.market,
            request.step,
            request.replace_state,
            "publish_clearing_price",
            {"price_e8": price_e8},
        ),
    )


def _apply_clearinghouse_set_market_params(
    ctx: _PerpApplyCtx, request: _ClearinghouseMarketParamsRequest
) -> str | None:
    data = request.op.data
    state = request.market.state
    operator_ok = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey) is None
    epoch_settled_ok = int(state.get("oracle_last_update_epoch", 0)) == int(state.get("now_epoch", 0))
    pre_guard = evaluate_perp_clearinghouse_market_params_guard(
        market_kind=request.market_kind,
        operator_ok=operator_ok,
        epoch_settled_ok=epoch_settled_ok,
        position_base_a=int(state.get("position_base_a", 0)),
        position_base_b=int(state.get("position_base_b", 0)),
        position_base_c=int(state.get("position_base_c", 0)),
        old_liquidation_penalty_bps=int(state.get("liquidation_penalty_bps", 0)),
        new_liquidation_penalty_bps=int(state.get("liquidation_penalty_bps", 0)),
        new_initial_margin_bps=int(state.get("initial_margin_bps", 0)),
        new_maintenance_margin_bps=int(state.get("maintenance_margin_bps", 0)),
        new_max_oracle_move_bps=int(state.get("max_oracle_move_bps", 0)),
    )
    pre_guard_error = perp_clearinghouse_market_params_guard_error(pre_guard)
    if pre_guard_error is not None:
        return pre_guard_error

    unknown = _reject_unknown_fields(
        data,
        {"module", "version", "market_id", "action", "params"},
        error="set_market_params has unknown fields",
    )
    if unknown is not None:
        return unknown

    params = data.get("params")
    if not isinstance(params, Mapping):
        return "params must be an object"
    try:
        next_state = _apply_clearinghouse_market_params(
            state,
            params=params,
            kind=request.kind,
            operator_ok=operator_ok,
            epoch_settled_ok=epoch_settled_ok,
        )
    except ValueError as exc:
        return str(exc)
    ctx.markets[request.op.market_id] = request.replace_state(request.market, state=next_state)
    ctx.effects.append({"i": request.i, "market_id": request.op.market_id, "action": request.op.action, "params": dict(params)})
    return None


def _apply_clearinghouse_collateral(ctx: _PerpApplyCtx, request: _ClearinghouseCollateralRequest) -> str | None:
    action = request.op.action
    data = request.op.data
    allowed = {"module", "version", "market_id", "action", "account_pubkey", "amount"}
    unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
    if unknown is not None:
        return unknown

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    if sender_err is not None:
        return sender_err

    role = request.market.role_for_pubkey(account_pubkey)
    if role is None:
        return f"unknown account_pubkey for this {request.market_label} market"

    amount = _require_int(data.get("amount"), name="amount", non_negative=True)
    # Protocol balances are in quote units; the clearinghouse kernel tracks quote-e8 for exact PnL.
    amount_e8 = int(amount) * _E8_SCALE

    if action == "deposit_collateral":
        if ctx.balances.get(account_pubkey, request.market.quote_asset) < amount:
            return "insufficient balance for deposit"
        tag = f"deposit_collateral_{role}"
    else:
        tag = f"withdraw_collateral_{role}"

    try:
        next_state, eff = request.step(
            request.market.state,
            tag=tag,
            args={"amount_e8": amount_e8, "auth_ok": True},
        )
    except ValueError as exc:
        return str(exc)

    if action == "deposit_collateral":
        ctx.balances.subtract(account_pubkey, request.market.quote_asset, amount)
    else:
        ctx.balances.add(account_pubkey, request.market.quote_asset, amount)

    ctx.markets[request.op.market_id] = request.replace_state(request.market, state=next_state)
    ctx.effects.append(
        {"i": request.i, "market_id": request.op.market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff}
    )
    return None


def _apply_ch2p_advance_epoch(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(data, {"module", "version", "market_id", "action", "delta"}, error="advance_epoch has unknown fields")
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
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch2p_market, _ch2p_step, _ch2p_market_with_state, "advance_epoch", {"delta": delta}),
    )


def _apply_ch2p_settle_epoch(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(
        data,
        {"module", "version", "market_id", "action", "oracle_adapter_bridge"},
        error="settle_epoch has unknown fields",
    )
    if unknown is not None:
        return unknown
    err = _require_oracle_adapter_bridge(
        _OracleAdapterBridgeRequirement(
            config=ctx.config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_clearinghouse_runtime_oracle_action_id(
                _ClearinghouseOracleRuntimeRequest(
                    config=ctx.config,
                    market_id=op.market_id,
                    action_kind="settle_epoch",
                    market_kind="clearinghouse_2p_v1",
                    quote_asset=ch2p_market.quote_asset,
                    state=ch2p_market.state,
                    participant_pubkeys=(
                        ch2p_market.account_a_pubkey,
                        ch2p_market.account_b_pubkey,
                    ),
                )
            ),
            expected_runtime_value_e8=ch2p_market.state.get("clearing_price_e8"),
            expected_runtime_epoch=ch2p_market.state.get("now_epoch"),
            required=ctx.config.require_oracle_adapter_for_clearinghouse_settle_epoch,
        )
    )
    if err is not None:
        return err
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch2p_market, _ch2p_step, _ch2p_market_with_state, "settle_epoch", {}),
    )


def _apply_ch2p_clear_breaker(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(data, {"module", "version", "market_id", "action"}, error="clear_breaker has unknown fields")
    if unknown is not None:
        return unknown
    if int(ch2p_market.state.get("position_base_a", 0)) != 0 or int(ch2p_market.state.get("position_base_b", 0)) != 0:
        return "cannot clear breaker while positions are open"
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch2p_market, _ch2p_step, _ch2p_market_with_state, "clear_breaker", {"auth_ok": True}),
    )


def _apply_ch3p_advance_epoch(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(data, {"module", "version", "market_id", "action", "delta"}, error="advance_epoch has unknown fields")
    if unknown is not None:
        return unknown
    if int(ch3p_market.state.get("oracle_last_update_epoch", 0)) != int(ch3p_market.state.get("now_epoch", 0)):
        return "cannot advance epoch before settling current epoch"
    delta = _require_int(data.get("delta"), name="delta", non_negative=True)
    if delta != 1:
        return "advance_epoch delta must be 1 for clearinghouse markets"
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch3p_market, _ch3p_step, _ch3p_market_with_state, "advance_epoch", {"delta": delta}),
    )


def _apply_ch3p_settle_epoch(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(
        data,
        {"module", "version", "market_id", "action", "oracle_adapter_bridge"},
        error="settle_epoch has unknown fields",
    )
    if unknown is not None:
        return unknown
    err = _require_oracle_adapter_bridge(
        _OracleAdapterBridgeRequirement(
            config=ctx.config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_clearinghouse_runtime_oracle_action_id(
                _ClearinghouseOracleRuntimeRequest(
                    config=ctx.config,
                    market_id=op.market_id,
                    action_kind="settle_epoch",
                    market_kind="clearinghouse_3p_transfer_v1",
                    quote_asset=ch3p_market.quote_asset,
                    state=ch3p_market.state,
                    participant_pubkeys=(
                        ch3p_market.account_a_pubkey,
                        ch3p_market.account_b_pubkey,
                        ch3p_market.account_c_pubkey,
                    ),
                )
            ),
            expected_runtime_value_e8=ch3p_market.state.get("clearing_price_e8"),
            expected_runtime_epoch=ch3p_market.state.get("now_epoch"),
            required=ctx.config.require_oracle_adapter_for_clearinghouse_settle_epoch,
        )
    )
    if err is not None:
        return err
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch3p_market, _ch3p_step, _ch3p_market_with_state, "settle_epoch", {}),
    )


def _apply_ch3p_clear_breaker(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    data = op.data
    unknown = _reject_unknown_fields(data, {"module", "version", "market_id", "action"}, error="clear_breaker has unknown fields")
    if unknown is not None:
        return unknown
    if (
        int(ch3p_market.state.get("position_base_a", 0)) != 0
        or int(ch3p_market.state.get("position_base_b", 0)) != 0
        or int(ch3p_market.state.get("position_base_c", 0)) != 0
    ):
        return "cannot clear breaker while positions are open"
    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch3p_market, _ch3p_step, _ch3p_market_with_state, "clear_breaker", {"auth_ok": True}),
    )


def _apply_ch2p_publish_clearing_price(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    version_ok = op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
    return _apply_clearinghouse_publish_clearing_price(
        ctx,
        _ClearinghousePublishPriceRequest(
            i,
            op,
            ch2p_market,
            version_ok,
            _ch2p_step,
            _ch2p_market_with_state,
        ),
    )


def _apply_ch3p_publish_clearing_price(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    version_ok = op.version == PERP_OP_VERSION_CH3P_V1_1
    return _apply_clearinghouse_publish_clearing_price(
        ctx,
        _ClearinghousePublishPriceRequest(
            i,
            op,
            ch3p_market,
            version_ok,
            _ch3p_step,
            _ch3p_market_with_state,
        ),
    )


def _apply_ch2p_set_market_params(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    return _apply_clearinghouse_set_market_params(
        ctx,
        _ClearinghouseMarketParamsRequest(
            i,
            op,
            ch2p_market,
            MARKET_KIND_CH2P,
            "ch2p",
            _ch2p_market_with_state,
        ),
    )


def _apply_ch3p_set_market_params(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    return _apply_clearinghouse_set_market_params(
        ctx,
        _ClearinghouseMarketParamsRequest(
            i,
            op,
            ch3p_market,
            MARKET_KIND_CH3P,
            "ch3p",
            _ch3p_market_with_state,
        ),
    )


def _apply_ch2p_collateral(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    return _apply_clearinghouse_collateral(
        ctx,
        _ClearinghouseCollateralRequest(
            i,
            op,
            ch2p_market,
            "clearinghouse_2p",
            _ch2p_step,
            _ch2p_market_with_state,
        ),
    )


def _apply_ch3p_collateral(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    return _apply_clearinghouse_collateral(
        ctx,
        _ClearinghouseCollateralRequest(
            i,
            op,
            ch3p_market,
            "clearinghouse_3p",
            _ch3p_step,
            _ch3p_market_with_state,
        ),
    )


def _read_ch2p_position_auth(data: Mapping[str, Any]) -> _Ch2pPositionAuth:
    return _Ch2pPositionAuth(
        nonce_a=_require_int_u32_pos(data.get("nonce_a"), name="nonce_a"),
        sig_a=_require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096),
        nonce_b=_require_int_u32_pos(data.get("nonce_b"), name="nonce_b"),
        sig_b=_require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096),
    )


def _read_ch2p_position_accounts(data: Mapping[str, Any]) -> _Ch2pPositionAccounts:
    return _Ch2pPositionAccounts(
        account_a_pubkey=_require_str(
            data.get("account_a_pubkey"),
            name="account_a_pubkey",
            non_empty=True,
            max_len=512,
        ),
        account_b_pubkey=_require_str(
            data.get("account_b_pubkey"),
            name="account_b_pubkey",
            non_empty=True,
            max_len=512,
        ),
    )


def _read_ch2p_position_values(data: Mapping[str, Any]) -> _Ch2pPositionValues:
    return _Ch2pPositionValues(
        new_a=_require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False),
        new_b=_require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False),
    )


def _ch2p_market_accounts_match_error(
    accounts: _Ch2pPositionAccounts,
    market: PerpClearinghouse2pMarketState,
) -> tuple[Optional[str], bool]:
    try:
        a_b = _hex_to_bytes_allow_0x(accounts.account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
        b_b = _hex_to_bytes_allow_0x(accounts.account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
        ma_b = _hex_to_bytes_allow_0x(market.account_a_pubkey, name="market.account_a_pubkey", expected_nbytes=48)
        mb_b = _hex_to_bytes_allow_0x(market.account_b_pubkey, name="market.account_b_pubkey", expected_nbytes=48)
    except (TypeError, ValueError) as exc:
        return str(exc), False
    return None, bool(a_b == ma_b and b_b == mb_b)


def _verify_ch2p_position_signatures(
    ctx: _PerpApplyCtx,
    *,
    data: Mapping[str, Any],
    accounts: _Ch2pPositionAccounts,
    auth: _Ch2pPositionAuth,
) -> Optional[str]:
    signers = (
        ("account_a", accounts.account_a_pubkey, auth.nonce_a, auth.sig_a),
        ("account_b", accounts.account_b_pubkey, auth.nonce_b, auth.sig_b),
    )
    for label, signer_pubkey, nonce, signature in signers:
        sig_err = _verify_perp_op_signature(
            _PerpSignatureVerificationRequest(
                config=ctx.config,
                signer_pubkey=signer_pubkey,
                nonce=nonce,
                signature=signature,
                op=data,
                nonces=ctx.nonces,
                block_timestamp=ctx.block_timestamp,
            )
        )
        if sig_err is not None:
            return f"{label} signature invalid: {sig_err}"
    return None


_CH2P_SET_POSITION_PAIR_FIELDS = frozenset(
    {
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
)


def _ch2p_position_version_error(action: str, *, version_ok: bool) -> Optional[str]:
    if version_ok:
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_PAIR,
        action=action,
        version_ok=False,
        unknown_fields_ok=True,
    )
    return surface_err or "set_position_pair requires perps.version=0.2 or 1.0"


def _ch2p_position_unknown_fields_error(
    action: str,
    *,
    data: Mapping[str, Any],
    version_ok: bool,
) -> Optional[str]:
    if not (set(data.keys()) - _CH2P_SET_POSITION_PAIR_FIELDS):
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_PAIR,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=False,
    )
    return surface_err or "set_position_pair has unknown fields"


def _ch2p_position_surface_error(
    action: str,
    *,
    version_ok: bool,
    market_accounts_match_ok: bool,
    values: _Ch2pPositionValues,
) -> Optional[str]:
    return _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_PAIR,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=True,
        market_accounts_match_ok=market_accounts_match_ok,
        net_zero_ok=values.new_b == -values.new_a,
    )


def _apply_ch2p_set_position_pair(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch2p_market: PerpClearinghouse2pMarketState
) -> str | None:
    action = op.action
    data = op.data
    version_ok = op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
    version_err = _ch2p_position_version_error(action, version_ok=version_ok)
    if version_err is not None:
        return version_err

    auth = _read_ch2p_position_auth(data)
    field_err = _ch2p_position_unknown_fields_error(action, data=data, version_ok=version_ok)
    if field_err is not None:
        return field_err

    accounts = _read_ch2p_position_accounts(data)
    account_err, market_accounts_match_ok = _ch2p_market_accounts_match_error(accounts, ch2p_market)
    if account_err is not None:
        return account_err

    values = _read_ch2p_position_values(data)
    surface_err = _ch2p_position_surface_error(
        action=action,
        version_ok=version_ok,
        market_accounts_match_ok=market_accounts_match_ok,
        values=values,
    )
    if surface_err is not None:
        return surface_err

    if not clearinghouse_position_update_allowed(ch2p_market.state):
        return "set_position_pair requires settlement of the published clearing price"

    sig_err = _verify_ch2p_position_signatures(ctx, data=data, accounts=accounts, auth=auth)
    if sig_err is not None:
        return sig_err

    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(
            i,
            op,
            ch2p_market,
            _ch2p_step,
            _ch2p_market_with_state,
            "set_position_pair",
            {"new_position_base_a": values.new_a, "auth_ok": True},
        ),
    )


def _read_ch3p_position_auth(data: Mapping[str, Any]) -> _Ch3pPositionAuth:
    return _Ch3pPositionAuth(
        nonce_a=_require_int_u32_pos(data.get("nonce_a"), name="nonce_a"),
        sig_a=_require_str(data.get("sig_a"), name="sig_a", non_empty=True, max_len=4096),
        nonce_b=_require_int_u32_pos(data.get("nonce_b"), name="nonce_b"),
        sig_b=_require_str(data.get("sig_b"), name="sig_b", non_empty=True, max_len=4096),
        nonce_c=_require_int_u32_pos(data.get("nonce_c"), name="nonce_c"),
        sig_c=_require_str(data.get("sig_c"), name="sig_c", non_empty=True, max_len=4096),
    )


def _read_ch3p_position_accounts(data: Mapping[str, Any]) -> _Ch3pPositionAccounts:
    return _Ch3pPositionAccounts(
        account_a_pubkey=_require_str(
            data.get("account_a_pubkey"),
            name="account_a_pubkey",
            non_empty=True,
            max_len=512,
        ),
        account_b_pubkey=_require_str(
            data.get("account_b_pubkey"),
            name="account_b_pubkey",
            non_empty=True,
            max_len=512,
        ),
        account_c_pubkey=_require_str(
            data.get("account_c_pubkey"),
            name="account_c_pubkey",
            non_empty=True,
            max_len=512,
        ),
    )


def _ch3p_market_accounts_match_error(
    accounts: _Ch3pPositionAccounts,
    market: PerpClearinghouse3pTransferMarketState,
) -> tuple[Optional[str], bool]:
    try:
        a_b = _hex_to_bytes_allow_0x(accounts.account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
        b_b = _hex_to_bytes_allow_0x(accounts.account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
        c_b = _hex_to_bytes_allow_0x(accounts.account_c_pubkey, name="account_c_pubkey", expected_nbytes=48)
        ma_b = _hex_to_bytes_allow_0x(market.account_a_pubkey, name="market.account_a_pubkey", expected_nbytes=48)
        mb_b = _hex_to_bytes_allow_0x(market.account_b_pubkey, name="market.account_b_pubkey", expected_nbytes=48)
        mc_b = _hex_to_bytes_allow_0x(market.account_c_pubkey, name="market.account_c_pubkey", expected_nbytes=48)
    except (TypeError, ValueError) as exc:
        return str(exc), False
    return None, bool(a_b == ma_b and b_b == mb_b and c_b == mc_b)


def _read_ch3p_position_values(data: Mapping[str, Any]) -> _Ch3pPositionValues:
    return _Ch3pPositionValues(
        new_a=_require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False),
        new_b=_require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False),
        new_c=_require_int(data.get("new_position_base_c"), name="new_position_base_c", non_negative=False),
    )


def _verify_ch3p_position_signatures(
    ctx: _PerpApplyCtx,
    *,
    data: Mapping[str, Any],
    accounts: _Ch3pPositionAccounts,
    auth: _Ch3pPositionAuth,
) -> Optional[str]:
    signers = (
        ("account_a", accounts.account_a_pubkey, auth.nonce_a, auth.sig_a),
        ("account_b", accounts.account_b_pubkey, auth.nonce_b, auth.sig_b),
        ("account_c", accounts.account_c_pubkey, auth.nonce_c, auth.sig_c),
    )
    for label, signer_pubkey, nonce, signature in signers:
        sig_err = _verify_perp_op_signature(
            _PerpSignatureVerificationRequest(
                config=ctx.config,
                signer_pubkey=signer_pubkey,
                nonce=nonce,
                signature=signature,
                op=data,
                nonces=ctx.nonces,
                block_timestamp=ctx.block_timestamp,
            )
        )
        if sig_err is not None:
            return f"{label} signature invalid: {sig_err}"
    return None


def _ch3p_position_pair_commit(values: _Ch3pPositionValues) -> tuple[Optional[str], Optional[str], Optional[Dict[str, Any]]]:
    if values.new_c == 0:
        if values.new_b != -values.new_a:
            return "clearinghouse_3p AB pair requires new_b == -new_a", None, None
        return None, "set_position_pair_ab", {"new_position_base_a": values.new_a, "auth_ok": True}
    if values.new_b == 0:
        if values.new_c != -values.new_a:
            return "clearinghouse_3p AC pair requires new_c == -new_a", None, None
        return None, "set_position_pair_ac", {"new_position_base_a": values.new_a, "auth_ok": True}
    if values.new_c != -values.new_b:
        return "clearinghouse_3p BC pair requires new_c == -new_b", None, None
    return None, "set_position_pair_bc", {"new_position_base_b": values.new_b, "auth_ok": True}


_CH3P_SET_POSITION_TRIPLET_FIELDS = frozenset(
    {
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
)


def _ch3p_position_version_error(action: str, *, version_ok: bool) -> Optional[str]:
    if version_ok:
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_TRIPLET,
        action=action,
        version_ok=False,
        unknown_fields_ok=True,
    )
    return surface_err or "set_position_triplet requires perps.version=1.1"


def _ch3p_position_unknown_fields_error(
    action: str,
    *,
    data: Mapping[str, Any],
    version_ok: bool,
) -> Optional[str]:
    if not (set(data.keys()) - _CH3P_SET_POSITION_TRIPLET_FIELDS):
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_TRIPLET,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=False,
    )
    return surface_err or "set_position_triplet has unknown fields"


def _ch3p_position_surface_error(
    action: str,
    *,
    version_ok: bool,
    market_accounts_match_ok: bool,
    values: _Ch3pPositionValues,
) -> Optional[str]:
    return _evaluate_signed_surface(
        action_kind=ACTION_SET_POSITION_TRIPLET,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=True,
        market_accounts_match_ok=market_accounts_match_ok,
        net_zero_ok=(values.new_a + values.new_b + values.new_c == 0),
        idle_leg_ok=(values.new_a == 0 or values.new_b == 0 or values.new_c == 0),
    )


def _apply_ch3p_set_position_triplet(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, ch3p_market: PerpClearinghouse3pTransferMarketState
) -> str | None:
    action = op.action
    data = op.data
    version_ok = op.version == PERP_OP_VERSION_CH3P_V1_1
    version_err = _ch3p_position_version_error(action, version_ok=version_ok)
    if version_err is not None:
        return version_err

    auth = _read_ch3p_position_auth(data)
    field_err = _ch3p_position_unknown_fields_error(action, data=data, version_ok=version_ok)
    if field_err is not None:
        return field_err
    accounts = _read_ch3p_position_accounts(data)
    account_err, market_accounts_match_ok = _ch3p_market_accounts_match_error(accounts, ch3p_market)
    if account_err is not None:
        return account_err

    values = _read_ch3p_position_values(data)
    surface_err = _ch3p_position_surface_error(
        action=action,
        version_ok=version_ok,
        market_accounts_match_ok=market_accounts_match_ok,
        values=values,
    )
    if surface_err is not None:
        return surface_err

    if not clearinghouse_position_update_allowed(ch3p_market.state):
        return "set_position_triplet requires settlement of the published clearing price"

    sig_err = _verify_ch3p_position_signatures(ctx, data=data, accounts=accounts, auth=auth)
    if sig_err is not None:
        return sig_err

    err, tag, args = _ch3p_position_pair_commit(values)
    if err is not None:
        return err
    if tag is None or args is None:
        return "internal error: set_position_triplet commit missing"

    return _commit_clearinghouse_kernel_step(
        ctx,
        _ClearinghouseKernelCommit(i, op, ch3p_market, _ch3p_step, _ch3p_market_with_state, tag, args),
    )


def _apply_ch2p_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    ch2p_market: PerpClearinghouse2pMarketState,
) -> str | None:
    action = op.action

    if action == "advance_epoch":
        return _apply_ch2p_advance_epoch(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action == "publish_clearing_price":
        return _apply_ch2p_publish_clearing_price(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action == "settle_epoch":
        return _apply_ch2p_settle_epoch(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action == "clear_breaker":
        return _apply_ch2p_clear_breaker(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action == "set_market_params":
        return _apply_ch2p_set_market_params(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action in ("deposit_collateral", "withdraw_collateral"):
        return _apply_ch2p_collateral(ctx, i=i, op=op, ch2p_market=ch2p_market)

    if action == "set_position_pair":
        return _apply_ch2p_set_position_pair(ctx, i=i, op=op, ch2p_market=ch2p_market)

    return f"unknown perps action: {action}"


def _apply_ch3p_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    ch3p_market: PerpClearinghouse3pTransferMarketState,
) -> str | None:
    action = op.action

    if action == "advance_epoch":
        return _apply_ch3p_advance_epoch(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action == "publish_clearing_price":
        return _apply_ch3p_publish_clearing_price(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action == "settle_epoch":
        return _apply_ch3p_settle_epoch(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action == "clear_breaker":
        return _apply_ch3p_clear_breaker(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action == "set_market_params":
        return _apply_ch3p_set_market_params(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action in ("deposit_collateral", "withdraw_collateral"):
        return _apply_ch3p_collateral(ctx, i=i, op=op, ch3p_market=ch3p_market)

    if action == "set_position_triplet":
        return _apply_ch3p_set_position_triplet(ctx, i=i, op=op, ch3p_market=ch3p_market)

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
    pending_closeout_error = _isolated_pending_funding_closeout_boundary_error(
        action,
        market,
    )
    if pending_closeout_error is not None:
        return pending_closeout_error
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
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=new_global,
        accounts=market.accounts,
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
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=new_global,
        accounts=market.accounts,
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
    return None


def _isolated_apply_funding_auto_admission_error(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
) -> Optional[str]:
    allowed = {
        "module",
        "version",
        "market_id",
        "action",
        "funding_closeout_liability_certificate",
        "funding_closeout_liability_receipt",
        "funding_closeout_allocation_receipt",
        "funding_closeout_policy_ledger",
    }
    return _operator_gate_error(
        action_kind=RUNTIME_ACTION_APPLY_FUNDING_AUTO,
        action=op.action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(op.data.keys()) - allowed),
    )


def _funding_closeout_receipt_expected_root(
    ctx: _PerpApplyCtx,
    *,
    market: PerpMarketState,
    receipt_payload: object,
) -> tuple[Optional[str], Optional[str]]:
    pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    if pending_roots:
        if not isinstance(receipt_payload, Mapping):
            return "invalid funding closeout liability receipt: receipt must be an object", None
        receipt_root = receipt_payload.get("pre_close_state_root_hash")
        if not isinstance(receipt_root, str) or receipt_root not in pending_roots:
            return "funding closeout receipt root not pending", None
        return None, receipt_root
    expected_root = ctx.config.isolated_funding_closeout_pre_state_root_hash
    if expected_root is None:
        return "funding closeout pre_close_state_root_hash required", None
    return None, expected_root


def _funding_closeout_source_expected_hash(
    ctx: _PerpApplyCtx,
    *,
    market: PerpMarketState,
    receipt_payload: object,
) -> tuple[Optional[str], Optional[str]]:
    pending_source_roots = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    if pending_source_roots:
        if len(pending_source_roots) != 1:
            return "funding closeout source availability root is ambiguous", None
        if not isinstance(receipt_payload, Mapping):
            return "invalid funding closeout allocation receipt: allocation_receipt must be an object", None
        receipt_source_hash = receipt_payload.get("source_availability_hash")
        if not isinstance(receipt_source_hash, str) or receipt_source_hash not in pending_source_roots:
            return "funding closeout source availability root not pending", None
        return None, receipt_source_hash
    expected_source_hash = ctx.config.isolated_funding_closeout_source_availability_hash
    if expected_source_hash is None:
        return "funding closeout source availability hash required", None
    return None, expected_source_hash


def _isolated_funding_closeout_admission(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    market: PerpMarketState,
    snapshot: _IsolatedFundingSnapshot,
    funding_rate_bps: int,
    raw_projected_net_funding_quote: int,
) -> tuple[Optional[str], _IsolatedFundingCloseoutAdmission]:
    default = _IsolatedFundingCloseoutAdmission(
        projected_net_funding_quote=int(raw_projected_net_funding_quote),
        receiver_haircut_quote=0,
        receiver_haircuts_by_account={},
        allocation_receipt_applied=False,
    )
    cert_payload = op.data.get("funding_closeout_liability_certificate")
    receipt_payload = op.data.get("funding_closeout_liability_receipt")
    allocation_receipt_payload = op.data.get("funding_closeout_allocation_receipt")
    policy_ledger_payload = op.data.get("funding_closeout_policy_ledger")
    if policy_ledger_payload is not None and allocation_receipt_payload is None:
        return "funding closeout policy ledger requires source-portfolio allocation receipt", default
    if (
        int(cert_payload is not None)
        + int(receipt_payload is not None)
        + int(allocation_receipt_payload is not None)
        > 1
    ):
        return "funding closeout certificate and receipt are mutually exclusive", default

    allocation_required = (
        bool(
            ctx.config.require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding
        )
        and int(raw_projected_net_funding_quote) < 0
    )
    if allocation_receipt_payload is not None or allocation_required:
        if allocation_receipt_payload is None:
            return "funding closeout allocation receipt required for negative net funding", default
        if int(raw_projected_net_funding_quote) >= 0:
            return "funding closeout allocation receipt only allowed for negative net funding", default
        if not isinstance(allocation_receipt_payload, Mapping):
            return "invalid funding closeout allocation receipt: allocation_receipt must be an object", default
        allocation_schema = allocation_receipt_payload.get("schema")
        pending_source_roots = tuple(
            getattr(market, "pending_funding_closeout_source_availability_hashes", ())
        )
        source_binding_required = bool(
            pending_source_roots
        ) or (
            ctx.config.isolated_funding_closeout_source_availability_hash is not None
        )
        if (
            len(pending_source_roots) > 1
            and allocation_schema
            != SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA
        ):
            return "funding closeout source-portfolio allocation receipt required", default
        if (
            source_binding_required
            and allocation_schema
            not in (
                SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
                SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
            )
        ):
            return "funding closeout source-bound allocation receipt required", default
        if allocation_schema == SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            if not pending_source_roots:
                return "funding closeout source-portfolio allocation receipt requires pending source roots", default
            post_open_accounts = tuple(
                PositionAccount(pk, acct.position_base)
                for pk, acct in snapshot.open_accounts
            )
            expected_receiver_claim_rows = post_open_receiver_claim_rows(
                post_open_accounts,
                price_e8=int(market.global_state.get("index_price_e8", 0)),
                funding_rate_bps=int(funding_rate_bps),
            )
            if len(expected_receiver_claim_rows) == 0:
                return "funding closeout rationed allocation receipt requires open funding receivers", default
            receiver_claim_sum = sum(
                row.claim_quote for row in expected_receiver_claim_rows
            )
            if -int(receiver_claim_sum) != int(raw_projected_net_funding_quote):
                return "funding closeout rationed allocation receipt requires only open funding receivers", default
            root_error, expected_root = _funding_closeout_receipt_expected_root(
                ctx,
                market=market,
                receipt_payload=allocation_receipt_payload,
            )
            if root_error is not None:
                return root_error, default
            verdict = verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
                allocation_receipt_payload,
                expected_market_id=op.market_id,
                expected_epoch=int(market.global_state.get("now_epoch", 0)),
                expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
                expected_funding_rate_bps=int(funding_rate_bps),
                expected_pre_close_state_root_hash=expected_root,
                expected_pending_source_availability_hashes=pending_source_roots,
                expected_aggregate_sink_capacity_quote=int(
                    market.global_state.get("fee_pool_quote", 0)
                ),
                expected_raw_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
                expected_receiver_claim_rows=expected_receiver_claim_rows,
            )
            if not verdict.ok:
                return (
                    f"invalid funding closeout source-portfolio allocation receipt: {verdict.error or 'rejected'}",
                    default,
                )
            try:
                source_portfolio_receipt = (
                    funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload(
                        allocation_receipt_payload
                    )
                )
            except (TypeError, ValueError) as exc:
                return f"invalid funding closeout source-portfolio allocation receipt: {exc}", default
            if policy_ledger_payload is None:
                return (
                    "funding closeout policy ledger required for source-portfolio allocation receipt",
                    default,
                )
            if not isinstance(policy_ledger_payload, Mapping):
                return "invalid funding closeout policy ledger: policy_ledger must be an object", default
            policy_verdict = verify_funding_closeout_policy_ledger_payload(
                policy_ledger_payload,
                source_portfolio_receipt=source_portfolio_receipt,
            )
            if not policy_verdict.ok:
                return (
                    f"invalid funding closeout policy ledger: {policy_verdict.error or 'rejected'}",
                    default,
                )
            try:
                policy_ledger = funding_closeout_policy_ledger_from_payload(
                    policy_ledger_payload
                )
            except (TypeError, ValueError) as exc:
                return f"invalid funding closeout policy ledger: {exc}", default
            policy_ledger_root = funding_closeout_policy_ledger_hash(policy_ledger)
            canonical_policy_payload = funding_closeout_policy_ledger_to_payload(
                policy_ledger
            )
            receiver_claims = {}
            if policy_ledger.haircut_policy == HAIRCUT_POLICY_RECOVERABLE_CLAIM:
                receiver_claims = {
                    row.account_pubkey: int(row.recoverable_claim_quote)
                    for row in policy_ledger.receiver_haircut_rows
                    if int(row.recoverable_claim_quote) > 0
                }
            payable_net_funding = int(
                source_portfolio_receipt.certificate.payable_post_open_due_sum_quote
            )
            receiver_haircuts = {
                row.account_pubkey: int(row.haircut_quote)
                for row in source_portfolio_receipt.receiver_haircut_rationing.receiver_rows
            }
            receiver_haircut = sum(receiver_haircuts.values())
            if payable_net_funding > 0 or payable_net_funding < int(raw_projected_net_funding_quote):
                return "funding closeout allocation payable sum out of bounds", default
            if int(raw_projected_net_funding_quote) + receiver_haircut != payable_net_funding:
                return "funding closeout allocation payable sum mismatch", default
            return (
                None,
                _IsolatedFundingCloseoutAdmission(
                    projected_net_funding_quote=payable_net_funding,
                    receiver_haircut_quote=receiver_haircut,
                    receiver_haircuts_by_account=receiver_haircuts,
                    allocation_receipt_applied=True,
                    policy_ledger_hash=policy_ledger_root,
                    policy_ledger_payload=canonical_policy_payload,
                    receiver_claims_by_account=receiver_claims,
                ),
            )
        if policy_ledger_payload is not None:
            return "funding closeout policy ledger only allowed for source-portfolio allocation receipt", default
        if allocation_schema == MIXED_OPEN_NETTING_SCHEMA:
            post_open_accounts = tuple(
                PositionAccount(pk, acct.position_base)
                for pk, acct in snapshot.open_accounts
            )
            verdict = verify_mixed_open_funding_netting_certificate_payload(
                allocation_receipt_payload,
                post_accounts=post_open_accounts,
            )
            if not verdict.ok:
                return (
                    f"invalid funding closeout mixed-open netting receipt: {verdict.error or 'rejected'}",
                    default,
                )
            try:
                mixed_receipt = mixed_open_funding_netting_certificate_from_payload(
                    allocation_receipt_payload
                )
            except (TypeError, ValueError) as exc:
                return f"invalid funding closeout mixed-open netting receipt: {exc}", default
            if int(mixed_receipt.epoch) != int(
                market.global_state.get("now_epoch", 0)
            ):
                return "invalid funding closeout mixed-open netting receipt: epoch mismatch", default
            if int(mixed_receipt.price_e8) != int(
                market.global_state.get("index_price_e8", 0)
            ):
                return "invalid funding closeout mixed-open netting receipt: price_e8 mismatch", default
            if int(mixed_receipt.funding_rate_bps) != int(funding_rate_bps):
                return "invalid funding closeout mixed-open netting receipt: funding_rate_bps mismatch", default
            payable_net_funding = int(mixed_receipt.payable_post_open_due_sum_quote)
            receiver_haircuts = {
                row.account_pubkey: int(row.haircut_quote)
                for row in mixed_receipt.receiver_haircut_rationing.receiver_rows
            }
            receiver_haircut = sum(receiver_haircuts.values())
            if int(mixed_receipt.raw_post_open_due_sum_quote) != int(
                raw_projected_net_funding_quote
            ):
                return "funding closeout mixed-open netting raw sum mismatch", default
            if payable_net_funding > 0 or payable_net_funding < int(
                raw_projected_net_funding_quote
            ):
                return "funding closeout allocation payable sum out of bounds", default
            if (
                int(raw_projected_net_funding_quote) + receiver_haircut
                != payable_net_funding
            ):
                return "funding closeout allocation payable sum mismatch", default
            return (
                None,
                _IsolatedFundingCloseoutAdmission(
                    projected_net_funding_quote=payable_net_funding,
                    receiver_haircut_quote=receiver_haircut,
                    receiver_haircuts_by_account=receiver_haircuts,
                    allocation_receipt_applied=True,
                ),
            )
        if allocation_schema == SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            source_error, expected_source_hash = _funding_closeout_source_expected_hash(
                ctx,
                market=market,
                receipt_payload=allocation_receipt_payload,
            )
            if source_error is not None:
                return source_error, default
            post_open_accounts = tuple(
                PositionAccount(pk, acct.position_base)
                for pk, acct in snapshot.open_accounts
            )
            expected_receiver_claim_rows = post_open_receiver_claim_rows(
                post_open_accounts,
                price_e8=int(market.global_state.get("index_price_e8", 0)),
                funding_rate_bps=int(funding_rate_bps),
            )
            if len(expected_receiver_claim_rows) == 0:
                return "funding closeout rationed allocation receipt requires open funding receivers", default
            receiver_claim_sum = sum(
                row.claim_quote for row in expected_receiver_claim_rows
            )
            if -int(receiver_claim_sum) != int(raw_projected_net_funding_quote):
                return "funding closeout rationed allocation receipt requires only open funding receivers", default
            root_error, expected_root = _funding_closeout_receipt_expected_root(
                ctx,
                market=market,
                receipt_payload=allocation_receipt_payload,
            )
            if root_error is not None:
                return root_error, default
            verdict = verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
                allocation_receipt_payload,
                expected_market_id=op.market_id,
                expected_epoch=int(market.global_state.get("now_epoch", 0)),
                expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
                expected_funding_rate_bps=int(funding_rate_bps),
                expected_pre_close_state_root_hash=expected_root,
                expected_source_availability_hash=expected_source_hash,
                expected_raw_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
                expected_receiver_claim_rows=expected_receiver_claim_rows,
            )
            if not verdict.ok:
                return (
                    f"invalid funding closeout source-bound allocation receipt: {verdict.error or 'rejected'}",
                    default,
                )
            try:
                source_bound_receipt = (
                    funding_closeout_source_bound_rationed_allocation_receipt_from_payload(
                        allocation_receipt_payload
                    )
                )
            except (TypeError, ValueError) as exc:
                return f"invalid funding closeout source-bound allocation receipt: {exc}", default
            payable_net_funding = int(
                source_bound_receipt.certificate.payable_post_open_due_sum_quote
            )
            receiver_haircuts = {
                row.account_pubkey: int(row.haircut_quote)
                for row in source_bound_receipt.receiver_haircut_rationing.receiver_rows
            }
            receiver_haircut = sum(receiver_haircuts.values())
            if payable_net_funding > 0 or payable_net_funding < int(raw_projected_net_funding_quote):
                return "funding closeout allocation payable sum out of bounds", default
            if int(raw_projected_net_funding_quote) + receiver_haircut != payable_net_funding:
                return "funding closeout allocation payable sum mismatch", default
            return (
                None,
                _IsolatedFundingCloseoutAdmission(
                    projected_net_funding_quote=payable_net_funding,
                    receiver_haircut_quote=receiver_haircut,
                    receiver_haircuts_by_account=receiver_haircuts,
                    allocation_receipt_applied=True,
                ),
            )
        if allocation_schema == RATIONED_ALLOCATION_RECEIPT_SCHEMA:
            post_open_accounts = tuple(
                PositionAccount(pk, acct.position_base)
                for pk, acct in snapshot.open_accounts
            )
            expected_receiver_claim_rows = post_open_receiver_claim_rows(
                post_open_accounts,
                price_e8=int(market.global_state.get("index_price_e8", 0)),
                funding_rate_bps=int(funding_rate_bps),
            )
            if len(expected_receiver_claim_rows) == 0:
                return "funding closeout rationed allocation receipt requires open funding receivers", default
            receiver_claim_sum = sum(
                row.claim_quote for row in expected_receiver_claim_rows
            )
            if -int(receiver_claim_sum) != int(raw_projected_net_funding_quote):
                return "funding closeout rationed allocation receipt requires only open funding receivers", default
            root_error, expected_root = _funding_closeout_receipt_expected_root(
                ctx,
                market=market,
                receipt_payload=allocation_receipt_payload,
            )
            if root_error is not None:
                return root_error, default
            verdict = verify_funding_closeout_rationed_allocation_receipt_payload(
                allocation_receipt_payload,
                expected_market_id=op.market_id,
                expected_epoch=int(market.global_state.get("now_epoch", 0)),
                expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
                expected_funding_rate_bps=int(funding_rate_bps),
                expected_pre_close_state_root_hash=expected_root,
                expected_raw_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
                expected_receiver_claim_rows=expected_receiver_claim_rows,
            )
            if not verdict.ok:
                return (
                    f"invalid funding closeout rationed allocation receipt: {verdict.error or 'rejected'}",
                    default,
                )
            try:
                rationed_receipt = (
                    funding_closeout_rationed_allocation_receipt_from_payload(
                        allocation_receipt_payload
                    )
                )
            except (TypeError, ValueError) as exc:
                return f"invalid funding closeout rationed allocation receipt: {exc}", default
            payable_net_funding = int(
                rationed_receipt.certificate.payable_post_open_due_sum_quote
            )
            receiver_haircuts = {
                row.account_pubkey: int(row.haircut_quote)
                for row in rationed_receipt.receiver_haircut_rationing.receiver_rows
            }
            receiver_haircut = sum(receiver_haircuts.values())
            if payable_net_funding > 0 or payable_net_funding < int(raw_projected_net_funding_quote):
                return "funding closeout allocation payable sum out of bounds", default
            if int(raw_projected_net_funding_quote) + receiver_haircut != payable_net_funding:
                return "funding closeout allocation payable sum mismatch", default
            return (
                None,
                _IsolatedFundingCloseoutAdmission(
                    projected_net_funding_quote=payable_net_funding,
                    receiver_haircut_quote=receiver_haircut,
                    receiver_haircuts_by_account=receiver_haircuts,
                    allocation_receipt_applied=True,
                ),
            )
        if len(snapshot.open_accounts) != 1:
            return "funding closeout allocation receipt requires exactly one open funding receiver", default
        receiver_pk, receiver_account = snapshot.open_accounts[0]
        raw_account_funding = _perp_v2_funding_payment(
            receiver_account.position_base,
            int(market.global_state.get("index_price_e8", 0)),
            int(funding_rate_bps),
        )
        if int(raw_account_funding) >= 0:
            return "funding closeout allocation receipt requires open funding receiver", default
        root_error, expected_root = _funding_closeout_receipt_expected_root(
            ctx,
            market=market,
            receipt_payload=allocation_receipt_payload,
        )
        if root_error is not None:
            return root_error, default
        verdict = verify_funding_closeout_allocation_receipt_payload(
            allocation_receipt_payload,
            expected_market_id=op.market_id,
            expected_epoch=int(market.global_state.get("now_epoch", 0)),
            expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
            expected_funding_rate_bps=int(funding_rate_bps),
            expected_pre_close_state_root_hash=expected_root,
            expected_raw_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
        )
        if not verdict.ok:
            return (
                f"invalid funding closeout allocation receipt: {verdict.error or 'rejected'}",
                default,
            )
        try:
            allocation_receipt = funding_closeout_allocation_receipt_from_payload(
                allocation_receipt_payload
            )
        except (TypeError, ValueError) as exc:
            return f"invalid funding closeout allocation receipt: {exc}", default
        payable_net_funding = int(
            allocation_receipt.certificate.payable_post_open_due_sum_quote
        )
        receiver_haircut = int(
            allocation_receipt.certificate.receiver_haircut_sum_quote
        )
        if payable_net_funding > 0 or payable_net_funding < int(raw_projected_net_funding_quote):
            return "funding closeout allocation payable sum out of bounds", default
        if int(raw_projected_net_funding_quote) + receiver_haircut != payable_net_funding:
            return "funding closeout allocation payable sum mismatch", default
        return (
            None,
                _IsolatedFundingCloseoutAdmission(
                    projected_net_funding_quote=payable_net_funding,
                    receiver_haircut_quote=receiver_haircut,
                    receiver_haircuts_by_account={str(receiver_pk): receiver_haircut},
                    allocation_receipt_applied=True,
                ),
            )

    receipt_required = (
        bool(ctx.config.require_isolated_funding_closeout_liability_receipt_on_negative_net_funding)
        and int(raw_projected_net_funding_quote) < 0
    )
    if receipt_payload is not None or receipt_required:
        if receipt_payload is None:
            return "funding closeout liability receipt required for negative net funding", default
        root_error, expected_root = _funding_closeout_receipt_expected_root(
            ctx,
            market=market,
            receipt_payload=receipt_payload,
        )
        if root_error is not None:
            return root_error, default
        verdict = verify_funding_closeout_liability_receipt_payload(
            receipt_payload,
            expected_market_id=op.market_id,
            expected_epoch=int(market.global_state.get("now_epoch", 0)),
            expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
            expected_funding_rate_bps=int(funding_rate_bps),
            expected_pre_close_state_root_hash=expected_root,
            expected_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
        )
        if not verdict.ok:
            return f"invalid funding closeout liability receipt: {verdict.error or 'rejected'}", default
        return None, default

    cert_required = (
        bool(ctx.config.require_isolated_funding_closeout_liability_certificate_on_negative_net_funding)
        and int(raw_projected_net_funding_quote) < 0
    )
    if cert_payload is None:
        if cert_required:
            return "funding closeout liability certificate required for negative net funding", default
        return None, default

    expected_hash = ctx.config.isolated_funding_closeout_pre_due_vector_hash
    if expected_hash is None:
        return "funding closeout pre_due_vector_hash required", default
    verdict = verify_funding_closeout_liability_certificate_payload(
        cert_payload,
        expected_epoch=int(market.global_state.get("now_epoch", 0)),
        expected_price_e8=int(market.global_state.get("index_price_e8", 0)),
        expected_funding_rate_bps=int(funding_rate_bps),
        expected_pre_due_vector_hash=expected_hash,
        expected_post_open_due_sum_quote=int(raw_projected_net_funding_quote),
    )
    if not verdict.ok:
        return f"invalid funding closeout liability certificate: {verdict.error or 'rejected'}", default
    return None, default


def _isolated_funding_snapshot(market: PerpMarketState) -> _IsolatedFundingSnapshot:
    now_epoch = int(market.global_state.get("now_epoch", 0))
    open_accounts = tuple(
        (pk, acct)
        for pk, acct in tuple(sorted(market.accounts.items()))
        if int(acct.position_base) != 0
    )
    return _IsolatedFundingSnapshot(
        now_epoch=now_epoch,
        pre_fee_pool_quote=int(market.global_state.get("fee_pool_quote", 0)),
        pre_fee_income_quote=int(market.global_state.get("fee_income", 0)),
        pre_insurance_balance_quote=int(market.global_state.get("insurance_balance", 0)),
        max_fee_pool_quote=int(perp_epoch_isolated_default_fee_pool_max_quote()),
        open_accounts=open_accounts,
        any_funding_applied_this_epoch=any(
            int(acct.funding_last_applied_epoch) >= now_epoch for _, acct in open_accounts
        ),
    )


def _evaluate_isolated_funding_gate(
    market: PerpMarketState,
    snapshot: _IsolatedFundingSnapshot,
    *,
    projected_net_funding_quote: int,
) -> Any:
    return evaluate_perp_apply_funding_auto_gate(
        now_epoch=snapshot.now_epoch,
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
        projected_net_funding_quote=int(projected_net_funding_quote),
        any_funding_applied_this_epoch=snapshot.any_funding_applied_this_epoch,
        fee_pool_quote=snapshot.pre_fee_pool_quote,
        fee_income_quote=snapshot.pre_fee_income_quote,
        insurance_balance_quote=snapshot.pre_insurance_balance_quote,
        max_fee_pool_quote=snapshot.max_fee_pool_quote,
    )


def _project_isolated_net_funding(
    market: PerpMarketState,
    snapshot: _IsolatedFundingSnapshot,
    *,
    new_rate_bps: int,
) -> int:
    projected_net_funding = 0
    for _, acct in snapshot.open_accounts:
        projected_net_funding += _perp_v2_funding_payment(
            acct.position_base,
            int(market.global_state.get("index_price_e8", 0)),
            int(new_rate_bps),
        )
    return int(projected_net_funding)


def _apply_isolated_funding_to_accounts(
    market: PerpMarketState,
    snapshot: _IsolatedFundingSnapshot,
    *,
    new_rate_bps: int,
    receiver_haircut_quote: int = 0,
    receiver_haircuts_by_account: Mapping[str, int] | None = None,
) -> tuple[Optional[str], Optional[_IsolatedFundingAccountApply]]:
    pre_global = dict(market.global_state)
    expected_account_global = dict(pre_global)
    expected_account_global["funding_rate_bps"] = int(new_rate_bps)

    new_accounts: Dict[str, PerpAccountState] = dict(market.accounts)
    applied_accounts = 0
    for pk, acct in snapshot.open_accounts:
        res = perp_epoch_isolated_default_apply(
            state={**pre_global, **acct.to_kernel_state()},
            action="apply_funding",
            params={"new_rate_bps": int(new_rate_bps), "auth_ok": True},
        )
        if not res.ok or res.state is None:
            return f"apply_funding rejected for account {pk}: {res.error or ''}".strip(), None
        post_global, post_acct = _split_kernel_state(res.state)
        _preserve_isolated_shell_global_fields(pre_global=pre_global, post_global=post_global)
        if post_global != expected_account_global:
            return "internal error: apply_funding mutated unexpected global fields", None
        new_accounts[str(pk)] = post_acct
        applied_accounts += 1
    haircut_by_account = {
        str(pk): int(amount)
        for pk, amount in dict(receiver_haircuts_by_account or {}).items()
        if int(amount) != 0
    }
    if not haircut_by_account and int(receiver_haircut_quote) > 0:
        if len(snapshot.open_accounts) != 1:
            return "funding closeout allocation haircut requires exactly one open funding receiver", None
        pk, _pre_acct = snapshot.open_accounts[0]
        haircut_by_account[str(pk)] = int(receiver_haircut_quote)
    if sum(haircut_by_account.values()) != int(receiver_haircut_quote):
        return "funding closeout allocation haircut map mismatch", None
    open_accounts = {str(pk): acct for pk, acct in snapshot.open_accounts}
    for pk, haircut_quote in haircut_by_account.items():
        if haircut_quote < 0:
            return "funding closeout allocation haircut must be non-negative", None
        if pk not in open_accounts:
            return "funding closeout allocation haircut account is not open", None
        pre_acct = open_accounts[pk]
        raw_account_funding = _perp_v2_funding_payment(
            pre_acct.position_base,
            int(market.global_state.get("index_price_e8", 0)),
            int(new_rate_bps),
        )
        if int(raw_account_funding) >= 0:
            return "funding closeout allocation haircut requires open funding receiver", None
        post_acct = new_accounts[pk]
        adjusted_collateral = int(post_acct.collateral_quote) - int(haircut_quote)
        adjusted_funding_paid = int(post_acct.funding_paid_cumulative) + int(haircut_quote)
        if adjusted_collateral < 0 or adjusted_collateral > MAX_COLLATERAL:
            return "funding closeout allocation haircut would violate collateral bounds", None
        new_accounts[pk] = replace(
            post_acct,
            collateral_quote=adjusted_collateral,
            funding_paid_cumulative=adjusted_funding_paid,
        )
    return None, _IsolatedFundingAccountApply(accounts=new_accounts, applied_accounts=int(applied_accounts))


def _commit_isolated_apply_funding_auto(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
    funding_gate: Any,
    account_apply: _IsolatedFundingAccountApply,
    projected_net_funding_quote: int,
    receiver_haircut_quote: int = 0,
    receiver_haircuts_by_account: Mapping[str, int] | None = None,
    allocation_receipt_applied: bool = False,
    policy_ledger_hash: str | None = None,
    policy_ledger_payload: Mapping[str, Any] | None = None,
    receiver_claims_by_account: Mapping[str, int] | None = None,
) -> None:
    expected_global = dict(market.global_state)
    expected_global["funding_rate_bps"] = int(funding_gate.funding_rate_bps)
    expected_global["fee_pool_quote"] = int(funding_gate.fee_pool_after_funding_quote)
    expected_global["fee_income"] = int(funding_gate.fee_income_after_funding_quote)
    expected_global["insurance_balance"] = int(funding_gate.insurance_after_funding_quote)

    consumed_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    consumed_source_roots = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    policy_ledger_roots = tuple(
        getattr(market, "funding_closeout_policy_ledger_hashes", ())
    )
    if policy_ledger_hash is not None:
        policy_ledger_roots = _append_funding_closeout_policy_ledger_hash(
            market,
            policy_ledger_hash,
        )
    receiver_claim_lots = _add_funding_closeout_receiver_claim_lots(
        market,
        receiver_claims_by_account=receiver_claims_by_account or {},
        policy_hash=policy_ledger_hash,
    )
    if receiver_claim_lots:
        receiver_claim_balances = funding_closeout_receiver_claim_balances_from_lots(
            receiver_claim_lots
        )
    else:
        receiver_claim_balances = tuple(
            getattr(market, "funding_closeout_receiver_claim_balances_quote", ())
        )
    next_receiver_claim_lots = (
        receiver_claim_lots
        if receiver_claim_lots
        else tuple(getattr(market, "funding_closeout_receiver_claim_lots_quote", ()))
    )
    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=expected_global,
        accounts=account_apply.accounts,
        pending_funding_closeout_root_hashes=(),
        pending_funding_closeout_source_availability_hashes=(),
        funding_closeout_policy_ledger_hashes=policy_ledger_roots,
        funding_closeout_receiver_claim_balances_quote=receiver_claim_balances,
        funding_closeout_receiver_claim_lots_quote=next_receiver_claim_lots,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "funding_rate_bps": int(funding_gate.funding_rate_bps),
            "mark_price_e8": int(funding_gate.mark_price_e8),
            "accounts_applied": int(account_apply.applied_accounts),
            "projected_net_funding_quote": int(projected_net_funding_quote),
            "fee_pool_delta_quote": int(projected_net_funding_quote),
            "fee_pool_after_quote": int(funding_gate.fee_pool_after_funding_quote),
            "fee_income_after_quote": int(funding_gate.fee_income_after_funding_quote),
            "insurance_after_quote": int(funding_gate.insurance_after_funding_quote),
            "funding_closeout_pending_root_hashes_consumed": list(consumed_roots),
            "funding_closeout_pending_source_availability_hashes_consumed": list(
                consumed_source_roots
            ),
            "funding_closeout_receiver_haircut_quote": int(receiver_haircut_quote),
            "funding_closeout_receiver_haircuts_quote_by_account": dict(
                sorted(
                    {
                        str(pk): int(amount)
                        for pk, amount in dict(
                            receiver_haircuts_by_account or {}
                        ).items()
                    }.items()
                )
            ),
            "funding_closeout_allocation_receipt_applied": bool(
                allocation_receipt_applied
            ),
            "funding_closeout_policy_ledger_emitted": policy_ledger_hash is not None,
            "funding_closeout_policy_ledger_hash": policy_ledger_hash,
            "funding_closeout_policy_ledger": (
                dict(policy_ledger_payload) if policy_ledger_payload is not None else None
            ),
            "funding_closeout_receiver_claim_balances_quote": dict(
                receiver_claim_balances
            ),
            "funding_closeout_receiver_claim_lots_quote": [
                {
                    "account_pubkey": account_pubkey,
                    "lot_id": lot_id,
                    "balance_quote": int(balance_quote),
                    "expires_at_epoch": int(expires_at_epoch),
                }
                for account_pubkey, lot_id, balance_quote, expires_at_epoch in (
                    next_receiver_claim_lots
                )
            ],
        }
    )


def _apply_isolated_apply_funding_auto(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    gate_error = _isolated_apply_funding_auto_admission_error(ctx, op=op)
    if gate_error is not None:
        return gate_error

    snapshot = _isolated_funding_snapshot(market)
    provisional_gate = _evaluate_isolated_funding_gate(
        market,
        snapshot,
        projected_net_funding_quote=0,
    )
    new_rate_bps = int(provisional_gate.funding_rate_bps)
    projected_net_funding = _project_isolated_net_funding(
        market,
        snapshot,
        new_rate_bps=new_rate_bps,
    )
    gate_error, closeout_admission = _isolated_funding_closeout_admission(
        ctx,
        op=op,
        market=market,
        snapshot=snapshot,
        funding_rate_bps=new_rate_bps,
        raw_projected_net_funding_quote=projected_net_funding,
    )
    if gate_error is not None:
        return gate_error
    funding_gate = _evaluate_isolated_funding_gate(
        market,
        snapshot,
        projected_net_funding_quote=closeout_admission.projected_net_funding_quote,
    )
    gate_error = perp_apply_funding_auto_gate_error(funding_gate)
    if gate_error is not None:
        return gate_error

    err, account_apply = _apply_isolated_funding_to_accounts(
        market,
        snapshot,
        new_rate_bps=int(funding_gate.funding_rate_bps),
        receiver_haircut_quote=closeout_admission.receiver_haircut_quote,
        receiver_haircuts_by_account=closeout_admission.receiver_haircuts_by_account,
    )
    if err is not None:
        return err
    if account_apply is None:
        return "internal error: apply_funding account step missing"

    _commit_isolated_apply_funding_auto(
        ctx,
        i=i,
        op=op,
        market=market,
        funding_gate=funding_gate,
        account_apply=account_apply,
        projected_net_funding_quote=closeout_admission.projected_net_funding_quote,
        receiver_haircut_quote=closeout_admission.receiver_haircut_quote,
        receiver_haircuts_by_account=closeout_admission.receiver_haircuts_by_account,
        allocation_receipt_applied=closeout_admission.allocation_receipt_applied,
        policy_ledger_hash=closeout_admission.policy_ledger_hash,
        policy_ledger_payload=closeout_admission.policy_ledger_payload,
        receiver_claims_by_account=closeout_admission.receiver_claims_by_account,
    )
    return None


def _apply_isolated_carry_funding_closeout_liability(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    data = op.data
    allowed = {
        "module",
        "version",
        "market_id",
        "action",
        "funding_closeout_carry_forward_receipt",
    }
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_CARRY_FUNDING_CLOSEOUT_LIABILITY,
        action=op.action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error

    pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    pending_source_roots = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    if not pending_roots:
        return "funding closeout root required for carry-forward"
    if not pending_source_roots:
        return "funding closeout source availability root required for carry-forward"

    receipt_payload = data.get("funding_closeout_carry_forward_receipt")
    if not isinstance(receipt_payload, Mapping):
        return "invalid funding closeout carry-forward receipt: receipt must be an object"
    pre_close_root = receipt_payload.get("pre_close_state_root_hash")
    if not isinstance(pre_close_root, str) or pre_close_root not in pending_roots:
        return "funding closeout carry-forward root not pending"

    now_epoch = int(market.global_state.get("now_epoch", 0))
    carry_epoch = now_epoch + 1
    verdict = verify_funding_closeout_carry_forward_receipt_payload(
        receipt_payload,
        expected_market_id=op.market_id,
        expected_source_epoch=now_epoch,
        expected_carry_epoch=carry_epoch,
        expected_pre_close_state_root_hash=pre_close_root,
        expected_pending_source_availability_hashes=pending_source_roots,
        expected_aggregate_sink_capacity_quote=int(market.global_state.get("fee_pool_quote", 0)),
    )
    if not verdict.ok:
        return f"invalid funding closeout carry-forward receipt: {verdict.error or 'rejected'}"

    try:
        receipt = funding_closeout_carry_forward_receipt_from_payload(receipt_payload)
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout carry-forward receipt: {exc}"
    carried_hash = carried_funding_closeout_liability_hash(receipt)
    carried_roots = _append_pending_funding_closeout_carried_liability_hash(
        market,
        carried_hash,
    )

    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=market.global_state,
        accounts=market.accounts,
        pending_funding_closeout_root_hashes=(),
        pending_funding_closeout_source_availability_hashes=(),
        pending_funding_closeout_carried_liability_hashes=carried_roots,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "source_epoch": int(receipt.source_epoch),
            "carry_epoch": int(receipt.carry_epoch),
            "funding_closeout_pending_root_hashes_consumed": list(pending_roots),
            "funding_closeout_pending_source_availability_hashes_consumed": list(
                pending_source_roots
            ),
            "funding_closeout_carried_liability_hash": carried_hash,
            "funding_closeout_carry_forward_receipt": (
                funding_closeout_carry_forward_receipt_to_payload(receipt)
            ),
        }
    )
    return None


def _remove_pending_funding_closeout_carried_liability_hash(
    market: PerpMarketState,
    carried_hash: str,
) -> tuple[str, ...]:
    pending_roots = tuple(
        getattr(market, "pending_funding_closeout_carried_liability_hashes", ())
    )
    return tuple(root for root in pending_roots if root != carried_hash)


def _apply_isolated_carried_funding_to_receivers(
    market: PerpMarketState,
    receipt: Any,
) -> tuple[Optional[str], Optional[_IsolatedCarriedFundingSettlement]]:
    rows = tuple(receipt.source_portfolio_receipt.receiver_haircut_rationing.receiver_rows)
    if not rows:
        return "funding closeout carried settlement requires receiver rows", None

    accounts: Dict[str, PerpAccountState] = dict(market.accounts)
    receiver_payments: Dict[str, int] = {}
    receiver_haircuts: Dict[str, int] = {}
    total_claim = 0
    total_payable = 0
    total_haircut = 0
    source_epoch = int(receipt.source_epoch)
    for row in rows:
        pk = str(row.account_pubkey)
        claim_quote = int(row.claim_quote)
        payable_quote = int(row.payable_quote)
        haircut_quote = int(row.haircut_quote)
        account = accounts.get(pk)
        if account is None:
            return "funding closeout carried settlement receiver account missing", None

        collateral_quote = int(account.collateral_quote) + payable_quote
        funding_paid_cumulative = int(account.funding_paid_cumulative) - payable_quote
        if collateral_quote < 0 or collateral_quote > MAX_COLLATERAL:
            return "funding closeout carried settlement would violate collateral bounds", None
        if abs(funding_paid_cumulative) > MAX_FUNDING_CUMULATIVE:
            return (
                "funding closeout carried settlement would violate cumulative funding bounds",
                None,
            )

        accounts[pk] = replace(
            account,
            collateral_quote=collateral_quote,
            funding_paid_cumulative=funding_paid_cumulative,
            funding_last_applied_epoch=max(
                int(account.funding_last_applied_epoch),
                source_epoch,
            ),
            liquidated_this_step=False,
        )
        receiver_payments[pk] = int(receiver_payments.get(pk, 0)) + payable_quote
        receiver_haircuts[pk] = int(receiver_haircuts.get(pk, 0)) + haircut_quote
        total_claim += claim_quote
        total_payable += payable_quote
        total_haircut += haircut_quote

    return None, _IsolatedCarriedFundingSettlement(
        accounts=accounts,
        total_claim_quote=int(total_claim),
        total_payable_quote=int(total_payable),
        total_haircut_quote=int(total_haircut),
        receiver_payments_by_account=dict(sorted(receiver_payments.items())),
        receiver_haircuts_by_account=dict(sorted(receiver_haircuts.items())),
    )


def _settle_carried_funding_global_state(
    market: PerpMarketState,
    *,
    total_payable_quote: int,
) -> tuple[Optional[str], Optional[Dict[str, Any]]]:
    payable = int(total_payable_quote)
    max_fee_pool = int(perp_epoch_isolated_default_fee_pool_max_quote())
    next_fee_pool = int(market.global_state.get("fee_pool_quote", 0)) - payable
    next_fee_income = int(market.global_state.get("fee_income", 0)) - payable
    next_insurance = int(market.global_state.get("insurance_balance", 0)) - payable
    if (
        next_fee_pool < 0
        or next_fee_income < 0
        or next_insurance < 0
        or next_fee_pool > max_fee_pool
        or next_fee_income > max_fee_pool
        or next_insurance > max_fee_pool
    ):
        return (
            f"funding closeout carried settlement would violate funding sink bounds (payable={payable})",
            None,
        )

    next_global = dict(market.global_state)
    next_global["fee_pool_quote"] = int(next_fee_pool)
    next_global["fee_income"] = int(next_fee_income)
    next_global["insurance_balance"] = int(next_insurance)
    return None, next_global


def _apply_isolated_settle_funding_closeout_carried_liability(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    data = op.data
    allowed = {
        "module",
        "version",
        "market_id",
        "action",
        "funding_closeout_carry_forward_receipt",
    }
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY,
        action=op.action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error
    now_epoch = int(market.global_state.get("now_epoch", 0))
    current_epoch_price_seen = bool(
        market.global_state.get("clearing_price_seen", False)
    ) and int(market.global_state.get("clearing_price_epoch", 0)) == now_epoch
    if current_epoch_price_seen:
        return "cannot settle carried funding closeout after clearing price is published"

    receipt_payload = data.get("funding_closeout_carry_forward_receipt")
    if not isinstance(receipt_payload, Mapping):
        return "invalid funding closeout carry-forward receipt: receipt must be an object"
    expected_carried_hash = receipt_payload.get("carried_liability_hash")
    pending_carried_roots = tuple(
        getattr(market, "pending_funding_closeout_carried_liability_hashes", ())
    )
    if not isinstance(expected_carried_hash, str) or expected_carried_hash not in pending_carried_roots:
        return "funding closeout carried liability root not pending"

    verdict = verify_funding_closeout_carry_forward_receipt_payload(
        receipt_payload,
        expected_market_id=op.market_id,
        expected_carry_epoch=now_epoch,
        expected_carried_liability_hash=expected_carried_hash,
        expected_aggregate_sink_capacity_quote=int(market.global_state.get("fee_pool_quote", 0)),
    )
    if not verdict.ok:
        return f"invalid funding closeout carry-forward receipt: {verdict.error or 'rejected'}"

    try:
        receipt = funding_closeout_carry_forward_receipt_from_payload(receipt_payload)
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout carry-forward receipt: {exc}"
    carried_hash = carried_funding_closeout_liability_hash(receipt)
    if carried_hash != expected_carried_hash:
        return "funding closeout carried liability root mismatch"

    err, settlement = _apply_isolated_carried_funding_to_receivers(market, receipt)
    if err is not None:
        return err
    if settlement is None:
        return "internal error: carried funding settlement missing"
    err, next_global = _settle_carried_funding_global_state(
        market,
        total_payable_quote=settlement.total_payable_quote,
    )
    if err is not None:
        return err
    if next_global is None:
        return "internal error: carried funding settlement global state missing"

    remaining_roots = _remove_pending_funding_closeout_carried_liability_hash(
        market,
        carried_hash,
    )
    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=next_global,
        accounts=settlement.accounts,
        pending_funding_closeout_carried_liability_hashes=remaining_roots,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "source_epoch": int(receipt.source_epoch),
            "carry_epoch": int(receipt.carry_epoch),
            "funding_closeout_carried_liability_hash_consumed": carried_hash,
            "funding_closeout_carried_total_claim_quote": int(
                settlement.total_claim_quote
            ),
            "funding_closeout_carried_total_payable_quote": int(
                settlement.total_payable_quote
            ),
            "funding_closeout_carried_total_haircut_quote": int(
                settlement.total_haircut_quote
            ),
            "funding_closeout_carried_receiver_payments_quote_by_account": dict(
                settlement.receiver_payments_by_account
            ),
            "funding_closeout_carried_receiver_haircuts_quote_by_account": dict(
                settlement.receiver_haircuts_by_account
            ),
            "fee_pool_delta_quote": -int(settlement.total_payable_quote),
            "fee_pool_after_quote": int(next_global["fee_pool_quote"]),
            "fee_income_after_quote": int(next_global["fee_income"]),
            "insurance_after_quote": int(next_global["insurance_balance"]),
            "funding_closeout_carry_forward_receipt": (
                funding_closeout_carry_forward_receipt_to_payload(receipt)
            ),
        }
    )
    return None


def _apply_isolated_settle_funding_closeout_recovery(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    data = op.data
    allowed = {
        "module",
        "version",
        "market_id",
        "action",
        "funding_closeout_policy_ledger",
        "funding_closeout_recovery_priority_certificate",
        "funding_closeout_recovery_collection_receipt",
        "funding_closeout_receiver_recovery_distribution",
        "funding_closeout_sink_recovery_distribution",
    }
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY,
        action=op.action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error

    policy_payload = data.get("funding_closeout_policy_ledger")
    priority_payload = data.get("funding_closeout_recovery_priority_certificate")
    collection_payload = data.get("funding_closeout_recovery_collection_receipt")
    distribution_payload = data.get("funding_closeout_receiver_recovery_distribution")
    sink_distribution_payload = data.get("funding_closeout_sink_recovery_distribution")
    if not isinstance(policy_payload, Mapping):
        return "invalid funding closeout policy ledger: policy_ledger must be an object"
    if not isinstance(priority_payload, Mapping):
        return "invalid funding closeout recovery priority certificate: certificate must be an object"
    if collection_payload is None:
        return "funding closeout recovery collection receipt required"
    if not isinstance(collection_payload, Mapping):
        return "invalid funding closeout recovery collection receipt: receipt must be an object"
    if not isinstance(distribution_payload, Mapping):
        return "invalid funding closeout receiver distribution: distribution must be an object"
    if sink_distribution_payload is None:
        return "funding closeout sink distribution required"
    if not isinstance(sink_distribution_payload, Mapping):
        return "invalid funding closeout sink distribution: distribution must be an object"

    try:
        policy_ledger = funding_closeout_policy_ledger_from_payload(policy_payload)
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout policy ledger: {exc}"
    policy_hash = funding_closeout_policy_ledger_hash(policy_ledger)
    pending_policy_roots = tuple(
        getattr(market, "funding_closeout_policy_ledger_hashes", ())
    )
    if policy_hash not in pending_policy_roots:
        return "funding closeout policy ledger root not pending"

    try:
        priority_certificate = (
            funding_closeout_recovery_priority_certificate_from_payload(
                priority_payload
            )
        )
        validate_recovery_priority_certificate_against_policy_ledger(
            priority_certificate,
            policy_ledger,
        )
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout recovery priority certificate: {exc}"

    try:
        collection_receipt = funding_closeout_recovery_collection_receipt_from_payload(
            collection_payload
        )
        validate_recovery_collection_receipt_against_sources(
            collection_receipt,
            policy_ledger,
            priority_certificate,
        )
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout recovery collection receipt: {exc}"

    authority_payload = ctx.config.isolated_funding_closeout_recovery_source_authority
    if authority_payload is None:
        return "funding closeout recovery source authority required"
    authority_verdict = verify_funding_closeout_recovery_source_authority_payload(
        authority_payload,
        expected_market_id=op.market_id,
        now_epoch=int(market.global_state.get("now_epoch", policy_ledger.epoch)),
        required_source_ids=(collection_receipt.source_id,),
    )
    if not authority_verdict.ok or authority_verdict.authority is None:
        return (
            "invalid funding closeout recovery source authority: "
            f"{authority_verdict.error or 'rejected'}"
        )
    recovery_source_authority = authority_verdict.authority
    binding_payload = (
        ctx.config.isolated_funding_closeout_recovery_source_authority_binding
    )
    if binding_payload is None:
        return "funding closeout recovery source authority binding required"
    authority_state_root_hash = (
        ctx.config
        .isolated_funding_closeout_recovery_source_authority_state_root_hash
    )
    if authority_state_root_hash is None:
        return "funding closeout recovery source authority state root required"
    authority_policy_hash = (
        ctx.config.isolated_funding_closeout_recovery_source_authority_policy_hash
    )
    if authority_policy_hash is None:
        return "funding closeout recovery source authority policy hash required"
    allowed_signers = (
        ctx.config.isolated_funding_closeout_recovery_source_authority_signer_pubkeys
    )
    if not allowed_signers:
        return "funding closeout recovery source authority signer registry required"
    binding_verdict = (
        verify_funding_closeout_recovery_source_authority_binding_payload(
            binding_payload,
            authority=recovery_source_authority,
            expected_market_id=op.market_id,
            now_epoch=int(market.global_state.get("now_epoch", policy_ledger.epoch)),
            expected_authority_state_root_hash=authority_state_root_hash,
            expected_policy_hash=authority_policy_hash,
            allowed_signer_pubkeys=allowed_signers,
        )
    )
    if not binding_verdict.ok or binding_verdict.binding is None:
        return (
            "invalid funding closeout recovery source authority binding: "
            f"{binding_verdict.error or 'rejected'}"
        )
    recovery_source_authority_binding = binding_verdict.binding

    try:
        distribution_certificate = (
            funding_closeout_receiver_recovery_distribution_certificate_from_payload(
                distribution_payload
            )
        )
        validate_receiver_recovery_distribution_against_sources(
            distribution_certificate,
            policy_ledger,
            priority_certificate,
        )
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout receiver distribution: {exc}"

    try:
        sink_distribution_certificate = (
            funding_closeout_sink_recovery_distribution_certificate_from_payload(
                sink_distribution_payload
            )
        )
        validate_sink_recovery_distribution_against_sources(
            sink_distribution_certificate,
            policy_ledger,
            priority_certificate,
        )
    except (TypeError, ValueError) as exc:
        return f"invalid funding closeout sink distribution: {exc}"

    receiver_claim_lots = _receiver_claim_lots_for_mutation(
        market,
        materialize_legacy_balances=bool(
            getattr(market, "funding_closeout_receiver_claim_balances_quote", ())
        ),
    )
    receiver_claim_balance_rows = (
        funding_closeout_receiver_claim_balances_from_lots(receiver_claim_lots)
        if receiver_claim_lots
        else tuple(getattr(market, "funding_closeout_receiver_claim_balances_quote", ()))
    )
    receiver_claim_balances = {
        str(account_pubkey): int(balance_quote)
        for account_pubkey, balance_quote in receiver_claim_balance_rows
    }
    accounts: Dict[str, PerpAccountState] = dict(market.accounts)
    receiver_recoveries: Dict[str, int] = {}
    total_receiver_recovery = 0
    for row in distribution_certificate.receiver_rows:
        pk = str(row.account_pubkey)
        recovery_quote = int(row.recovery_quote)
        if recovery_quote > int(receiver_claim_balances.get(pk, 0)):
            return "funding closeout recovery exceeds receiver claim balance"
        account = accounts.get(pk)
        if account is None:
            return "funding closeout recovery receiver account missing"
        collateral_quote = int(account.collateral_quote) + recovery_quote
        funding_paid_cumulative = int(account.funding_paid_cumulative) - recovery_quote
        if collateral_quote < 0 or collateral_quote > MAX_COLLATERAL:
            return "funding closeout recovery would violate collateral bounds"
        if abs(funding_paid_cumulative) > MAX_FUNDING_CUMULATIVE:
            return "funding closeout recovery would violate cumulative funding bounds"
        accounts[pk] = replace(
            account,
            collateral_quote=collateral_quote,
            funding_paid_cumulative=funding_paid_cumulative,
            funding_last_applied_epoch=max(
                int(account.funding_last_applied_epoch),
                int(policy_ledger.epoch),
            ),
            liquidated_this_step=False,
        )
        receiver_recoveries[pk] = int(receiver_recoveries.get(pk, 0)) + recovery_quote
        total_receiver_recovery += recovery_quote
    lot_debit_error, next_receiver_claim_lots, receiver_claim_lot_debits = (
        _debit_funding_closeout_receiver_claim_lots(market, receiver_recoveries)
    )
    if lot_debit_error is not None:
        return lot_debit_error
    next_receiver_claim_balances = (
        funding_closeout_receiver_claim_balances_from_lots(next_receiver_claim_lots)
        if next_receiver_claim_lots
        else ()
    )

    sink_recovery = int(sink_distribution_certificate.total_sink_recovery_quote)
    sink_recoveries_by_claimant: Dict[str, int] = {}
    sink_recovery_rows = []
    for row in sink_distribution_certificate.sink_rows:
        claimant = str(row.claimant)
        recovery_quote = int(row.recovery_quote)
        sink_recoveries_by_claimant[claimant] = (
            int(sink_recoveries_by_claimant.get(claimant, 0)) + recovery_quote
        )
        sink_recovery_rows.append(
            {
                "account_pubkey": str(row.account_pubkey),
                "claimant": claimant,
                "subrogated_claim_quote": int(row.subrogated_claim_quote),
                "recovery_quote": recovery_quote,
            }
        )
    max_fee_pool = int(perp_epoch_isolated_default_fee_pool_max_quote())
    next_global = dict(market.global_state)
    for key in ("fee_pool_quote", "fee_income", "insurance_balance"):
        next_value = int(next_global.get(key, 0)) + sink_recovery
        if next_value < 0 or next_value > max_fee_pool:
            return (
                "funding closeout recovery would violate funding sink bounds "
                f"(sink_recovery={sink_recovery})"
            )
        next_global[key] = int(next_value)

    sink_claimant_balances = {
        str(claimant): int(balance_quote)
        for claimant, balance_quote in tuple(
            getattr(market, "funding_closeout_sink_claimant_balances_quote", ())
        )
    }
    for claimant, recovery_quote in sink_recoveries_by_claimant.items():
        if recovery_quote == 0:
            continue
        next_value = int(sink_claimant_balances.get(claimant, 0)) + int(
            recovery_quote
        )
        if next_value <= 0 or next_value > max_fee_pool:
            return (
                "funding closeout recovery would violate sink claimant bounds "
                f"(claimant={claimant})"
            )
        sink_claimant_balances[claimant] = int(next_value)
    next_sink_claimant_balances = tuple(sorted(sink_claimant_balances.items()))
    total_sink_claimant_balance = sum(
        int(balance_quote) for _, balance_quote in next_sink_claimant_balances
    )
    for key in ("fee_pool_quote", "fee_income", "insurance_balance"):
        if total_sink_claimant_balance > int(next_global[key]):
            return (
                "funding closeout recovery would violate sink claimant conservation"
            )

    remaining_policy_roots = _remove_funding_closeout_policy_ledger_hash(
        market,
        policy_hash,
    )
    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=next_global,
        accounts=accounts,
        funding_closeout_policy_ledger_hashes=remaining_policy_roots,
        funding_closeout_sink_claimant_balances_quote=next_sink_claimant_balances,
        funding_closeout_receiver_claim_balances_quote=next_receiver_claim_balances,
        funding_closeout_receiver_claim_lots_quote=next_receiver_claim_lots,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "funding_closeout_policy_ledger_hash_consumed": policy_hash,
            "funding_closeout_recovery_priority_certificate_hash": (
                funding_closeout_recovery_priority_certificate_hash(
                    priority_certificate
                )
            ),
            "funding_closeout_recovery_collection_receipt_hash": (
                funding_closeout_recovery_collection_receipt_hash(collection_receipt)
            ),
            "funding_closeout_recovery_source_authority_hash": (
                funding_closeout_recovery_source_authority_hash(
                    recovery_source_authority
                )
            ),
            "funding_closeout_recovery_source_authority_binding_hash": (
                funding_closeout_recovery_source_authority_binding_hash(
                    recovery_source_authority_binding
                )
            ),
            "funding_closeout_receiver_recovery_distribution_hash": (
                funding_closeout_receiver_recovery_distribution_certificate_hash(
                    distribution_certificate
                )
            ),
            "funding_closeout_sink_recovery_distribution_hash": (
                funding_closeout_sink_recovery_distribution_certificate_hash(
                    sink_distribution_certificate
                )
            ),
            "funding_closeout_collected_source_quote": int(
                collection_receipt.collected_source_quote
            ),
            "funding_closeout_recovery_collection_source_id": str(
                collection_receipt.source_id
            ),
            "funding_closeout_recovery_collection_nonce": int(
                collection_receipt.collection_nonce
            ),
            "funding_closeout_receiver_recovery_quote": int(
                total_receiver_recovery
            ),
            "funding_closeout_receiver_recoveries_quote_by_account": dict(
                sorted(receiver_recoveries.items())
            ),
            "funding_closeout_sink_recovery_quote": int(sink_recovery),
            "funding_closeout_sink_recoveries_quote_by_claimant": dict(
                sorted(sink_recoveries_by_claimant.items())
            ),
            "funding_closeout_sink_recovery_rows": sink_recovery_rows,
            "funding_closeout_sink_claimant_balances_quote": dict(
                next_sink_claimant_balances
            ),
            "funding_closeout_receiver_claim_balances_quote": dict(
                next_receiver_claim_balances
            ),
            "funding_closeout_receiver_claim_lot_debits_quote": (
                receiver_claim_lot_debits
            ),
            "funding_closeout_receiver_claim_lots_quote": [
                {
                    "account_pubkey": account_pubkey,
                    "lot_id": lot_id,
                    "balance_quote": int(balance_quote),
                    "expires_at_epoch": int(expires_at_epoch),
                }
                for account_pubkey, lot_id, balance_quote, expires_at_epoch in (
                    next_receiver_claim_lots
                )
            ],
            "funding_closeout_source_capacity_quote": int(
                priority_certificate.source_capacity_quote
            ),
            "fee_pool_after_quote": int(next_global["fee_pool_quote"]),
            "fee_income_after_quote": int(next_global["fee_income"]),
            "insurance_after_quote": int(next_global["insurance_balance"]),
        }
    )
    return None


def _isolated_settle_authorization_error(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    market: PerpMarketState,
) -> Optional[str]:
    data = op.data
    allowed = {"module", "version", "market_id", "action", "oracle_authorization", "oracle_adapter_bridge"}
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_SETTLE_EPOCH,
        action=op.action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
    )
    if gate_error is not None:
        return gate_error

    err = _require_oracle_adapter_bridge(
        _OracleAdapterBridgeRequirement(
            config=ctx.config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=_perps_runtime_oracle_action_id(
                ctx.config,
                market_id=op.market_id,
                action_kind="settle_epoch",
                market=market,
            ),
            required=ctx.config.require_oracle_adapter_for_isolated_settle_epoch,
        )
    )
    if err is not None:
        return err
    return _check_isolated_settle_oracle_authorization(ctx=ctx, op=op, market=market)


def _isolated_settle_pre_accounting(market: PerpMarketState) -> _IsolatedSettleAccounting:
    return _IsolatedSettleAccounting(
        fee_pool_quote=int(market.global_state.get("fee_pool_quote", 0)),
        fee_income_quote=int(market.global_state.get("fee_income", 0)),
        initial_insurance_quote=int(market.global_state.get("initial_insurance", 0)),
        claims_paid_quote=int(market.global_state.get("claims_paid", 0)),
        insurance_balance_quote=int(market.global_state.get("insurance_balance", 0)),
    )


def _derive_isolated_settle_global_step(
    market: PerpMarketState,
) -> tuple[Optional[str], Optional[_IsolatedSettleGlobalStep]]:
    # This dummy-account step computes the global epoch update once. Account-local
    # liquidation effects are checked later against this same global result.
    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="settle_epoch",
        params={},
    )
    if not res.ok or res.state is None:
        return res.error or "settle_epoch rejected", None

    base_global, new_dummy = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=base_global)
    if new_dummy != dummy:
        return "internal error: settle_epoch mutated dummy account state", None
    return None, _IsolatedSettleGlobalStep(global_state=base_global, effects=dict(res.effects or {}))


def _global_without_isolated_settle_accumulators(
    global_state: Mapping[str, Any],
    *,
    accounting: _IsolatedSettleAccounting,
) -> Dict[str, Any]:
    out = dict(global_state)
    out["fee_pool_quote"] = int(accounting.fee_pool_quote)
    out["fee_income"] = int(accounting.fee_income_quote)
    out["insurance_balance"] = int(accounting.insurance_balance_quote)
    return out


def _is_stable_flat_isolated_account(acct: PerpAccountState) -> bool:
    return (
        int(acct.position_base) == 0
        and int(acct.entry_price_e8) == 0
        and not bool(acct.liquidated_this_step)
        and 0 <= int(acct.collateral_quote) <= MAX_COLLATERAL
    )


def _apply_isolated_settle_account(
    market: PerpMarketState,
    *,
    account_pubkey: str,
    account: PerpAccountState,
    expected_global_no_accum: Mapping[str, Any],
    accounting: _IsolatedSettleAccounting,
) -> tuple[Optional[str], Optional[_IsolatedSettleAccountStep]]:
    # Flat accounts that are already in the kernel's stable post-step shape cannot
    # change under settle_epoch. Other accounts still execute the kernel.
    if _is_stable_flat_isolated_account(account):
        return None, _IsolatedSettleAccountStep(
            account=account,
            fee_pool_delta_quote=0,
            raw_liquidation_penalty_quote=0,
        )

    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(account),
        action="settle_epoch",
        params={},
    )
    if not res.ok or res.state is None:
        return f"settle_epoch rejected for account {account_pubkey}: {res.error or ''}".strip(), None

    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    post_global_no_accum = _global_without_isolated_settle_accumulators(post_global, accounting=accounting)
    if post_global_no_accum != dict(expected_global_no_accum):
        return "internal error: global settle depended on account state", None

    fee_pool_delta = int(post_global.get("fee_pool_quote", 0)) - int(accounting.fee_pool_quote)
    fee_income_delta = int(post_global.get("fee_income", 0)) - int(accounting.fee_income_quote)
    insurance_delta = int(post_global.get("insurance_balance", 0)) - int(accounting.insurance_balance_quote)
    if fee_pool_delta < 0 or fee_income_delta < 0 or insurance_delta < 0:
        return "internal error: fee pool decreased during settle_epoch", None
    if fee_pool_delta != fee_income_delta or fee_pool_delta != insurance_delta:
        return "internal error: fee/insurance deltas inconsistent", None

    raw_liquidation_penalty = 0
    if bool(post_acct.liquidated_this_step):
        raw_liquidation_penalty = _perp_v2_liq_penalty(
            int(account.position_base),
            int(post_global.get("index_price_e8", 0)),
            int(post_global.get("liquidation_penalty_bps", 0)),
            int(post_global.get("min_notional_for_bounty", 0)),
        )
    return None, _IsolatedSettleAccountStep(
        account=post_acct,
        fee_pool_delta_quote=int(fee_pool_delta),
        raw_liquidation_penalty_quote=int(raw_liquidation_penalty),
    )


def _settle_isolated_accounts(
    market: PerpMarketState,
    *,
    expected_global_no_accum: Mapping[str, Any],
    accounting: _IsolatedSettleAccounting,
) -> tuple[Optional[str], Optional[_IsolatedSettleTotals]]:
    accounts: Dict[str, PerpAccountState] = {}
    penalty_delta = 0
    raw_liquidation_penalty = 0
    penalty_shortfall = 0
    cap_bound_count = 0

    for pk, acct in tuple(sorted(market.accounts.items())):
        err, step = _apply_isolated_settle_account(
            market,
            account_pubkey=str(pk),
            account=acct,
            expected_global_no_accum=expected_global_no_accum,
            accounting=accounting,
        )
        if err is not None:
            return err, None
        if step is None:
            return "internal error: settle_epoch account step missing", None

        penalty_delta += int(step.fee_pool_delta_quote)
        raw_liquidation_penalty += int(step.raw_liquidation_penalty_quote)
        if int(step.raw_liquidation_penalty_quote) > int(step.fee_pool_delta_quote):
            cap_bound_count += 1
            penalty_shortfall += int(step.raw_liquidation_penalty_quote) - int(step.fee_pool_delta_quote)
        accounts[str(pk)] = step.account

    return None, _IsolatedSettleTotals(
        accounts=accounts,
        penalty_delta_quote=int(penalty_delta),
        raw_liquidation_penalty_quote=int(raw_liquidation_penalty),
        liquidation_penalty_shortfall_quote=int(penalty_shortfall),
        liquidation_penalty_cap_bound_count=int(cap_bound_count),
    )


def _build_isolated_settle_next_global(
    expected_global_no_accum: Mapping[str, Any],
    *,
    accounting: _IsolatedSettleAccounting,
    totals: _IsolatedSettleTotals,
) -> tuple[Optional[str], Optional[Dict[str, Any]]]:
    max_fee_pool = perp_epoch_isolated_default_fee_pool_max_quote()
    next_fee_pool = int(accounting.fee_pool_quote) + int(totals.penalty_delta_quote)
    next_fee_income = int(accounting.fee_income_quote) + int(totals.penalty_delta_quote)
    next_insurance = int(accounting.initial_insurance_quote) + next_fee_income - int(accounting.claims_paid_quote)
    if next_fee_pool > max_fee_pool or next_fee_income > max_fee_pool or next_insurance > max_fee_pool:
        return "fee/insurance overflow (post-settle)", None
    if next_insurance < 0:
        return "insurance negative (post-settle)", None

    next_global = dict(expected_global_no_accum)
    next_global["fee_pool_quote"] = int(next_fee_pool)
    next_global["fee_income"] = int(next_fee_income)
    next_global["insurance_balance"] = int(next_insurance)
    return None, next_global


def _commit_isolated_settle_epoch(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
    next_global: Mapping[str, Any],
    totals: _IsolatedSettleTotals,
    kernel_effects: Mapping[str, Any],
) -> None:
    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=next_global,
        accounts=totals.accounts,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "fee_pool_delta": int(totals.penalty_delta_quote),
            "liquidation_penalty_raw_quote": int(totals.raw_liquidation_penalty_quote),
            "liquidation_penalty_collected_quote": int(totals.penalty_delta_quote),
            "liquidation_penalty_shortfall_quote": int(totals.liquidation_penalty_shortfall_quote),
            "liquidation_penalty_cap_bound_count": int(totals.liquidation_penalty_cap_bound_count),
            "effects": dict(kernel_effects),
        }
    )


def _apply_isolated_settle_epoch(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    auth_error = _isolated_settle_authorization_error(ctx, op=op, market=market)
    if auth_error is not None:
        return auth_error
    pending_closeout_error = _isolated_pending_funding_closeout_boundary_error(
        op.action,
        market,
    )
    if pending_closeout_error is not None:
        return pending_closeout_error

    accounting = _isolated_settle_pre_accounting(market)
    err, global_step = _derive_isolated_settle_global_step(market)
    if err is not None:
        return err
    if global_step is None:
        return "internal error: settle_epoch global step missing"

    expected_global_no_accum = _global_without_isolated_settle_accumulators(
        global_step.global_state,
        accounting=accounting,
    )
    err, totals = _settle_isolated_accounts(
        market,
        expected_global_no_accum=expected_global_no_accum,
        accounting=accounting,
    )
    if err is not None:
        return err
    if totals is None:
        return "internal error: settle_epoch totals missing"

    err, next_global = _build_isolated_settle_next_global(
        expected_global_no_accum,
        accounting=accounting,
        totals=totals,
    )
    if err is not None:
        return err
    if next_global is None:
        return "internal error: settle_epoch next global missing"

    _commit_isolated_settle_epoch(
        ctx,
        i=i,
        op=op,
        market=market,
        next_global=next_global,
        totals=totals,
        kernel_effects=global_step.effects,
    )
    return None


def _apply_isolated_clear_breaker(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action"}
    gate_error = _operator_gate_error(
        action_kind=RUNTIME_ACTION_CLEAR_BREAKER,
        action=action,
        operator_err=_require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey),
        unknown_fields_ok=not (set(data.keys()) - allowed),
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

    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=new_global,
        accounts=market.accounts,
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
    old_funding_rate_bps = int(market.global_state.get("funding_rate_bps", 0))
    next_market = _apply_isolated_market_params(
        market,
        params=params,
        min_collectible_liquidation_penalty_quote=min_collectible_penalty,
    )
    new_funding_rate_bps = int(next_market.global_state.get("funding_rate_bps", 0))
    funding_rate_clamped = int(old_funding_rate_bps) != int(new_funding_rate_bps)
    ctx.markets[market_id] = next_market
    ctx.effects.append(
        {
            "i": i,
            "market_id": market_id,
            "action": action,
            "params": dict(params),
            "funding_rate_clamped": bool(funding_rate_clamped),
            "funding_rate_bps_before": int(old_funding_rate_bps),
            "funding_rate_bps_after": int(new_funding_rate_bps),
        }
    )
    return None


_ISOLATED_COLLATERAL_FIELDS = frozenset({"module", "version", "market_id", "action", "account_pubkey", "amount"})


def _read_isolated_collateral_command(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    action_kind: int,
) -> tuple[Optional[str], Optional[str], Optional[int]]:
    unknown_fields_ok = not (set(op.data.keys()) - _ISOLATED_COLLATERAL_FIELDS)
    gate_error = _sender_gate_error(
        action_kind=action_kind,
        action=op.action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error, None, None

    account_pubkey = _require_str(op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=action_kind,
        action=op.action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error, None, None

    amount = _require_int(op.data.get("amount"), name="amount", non_negative=True)
    return None, account_pubkey, amount


def _apply_isolated_deposit_collateral(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    action = op.action
    market_id = op.market_id

    err, account_pubkey, amount = _read_isolated_collateral_command(
        ctx,
        op=op,
        action_kind=RUNTIME_ACTION_DEPOSIT_COLLATERAL,
    )
    if err is not None:
        return err
    if account_pubkey is None or amount is None:
        return "internal error: deposit_collateral command missing"

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

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
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=market.global_state,
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

    err, account_pubkey, amount = _read_isolated_collateral_command(
        ctx,
        op=op,
        action_kind=RUNTIME_ACTION_WITHDRAW_COLLATERAL,
    )
    if err is not None:
        return err
    if account_pubkey is None or amount is None:
        return "internal error: withdraw_collateral command missing"

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

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
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=market.global_state,
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
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=post_global,
        accounts=market.accounts,
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


_ISOLATED_SET_POSITION_FIELDS = frozenset(
    {"module", "version", "market_id", "action", "account_pubkey", "new_position_base"}
)


def _read_isolated_set_position_command(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
) -> tuple[Optional[str], Optional[str], Optional[int]]:
    unknown_fields_ok = not (set(op.data.keys()) - _ISOLATED_SET_POSITION_FIELDS)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_SET_POSITION,
        action=op.action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error, None, None

    account_pubkey = _require_str(op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_SET_POSITION,
        action=op.action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error, None, None

    new_pos = _require_int(op.data.get("new_position_base"), name="new_position_base", non_negative=False)
    return None, account_pubkey, new_pos


def _apply_isolated_set_position(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id

    err, account_pubkey, new_pos = _read_isolated_set_position_command(ctx, op=op)
    if err is not None:
        return err
    if account_pubkey is None or new_pos is None:
        return "internal error: set_position command missing"

    accounts = dict(market.accounts)
    acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

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
    oi_error = _isolated_oi_liquidity_policy_error(
        ctx.config,
        market_id=market_id,
        market=market,
        accounts_after=accounts,
    )
    if oi_error is not None:
        return oi_error
    ctx.markets[market_id] = _isolated_market_with(
        market,
        global_state=market.global_state,
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


_ISOLATED_PARTIAL_LIQUIDATE_FIELDS = frozenset(
    {
        "module",
        "version",
        "market_id",
        "action",
        "account_pubkey",
        "fraction_bps",
        "oracle_adapter_bridge",
        "tau_source_binding",
        "tau_source_authority_policy_context",
        "tau_source_authority_policy_receipt",
    }
)


def _partial_liquidate_bound_account(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
) -> tuple[Optional[str], Optional[str]]:
    unknown_fields_ok = not (set(op.data.keys()) - _ISOLATED_PARTIAL_LIQUIDATE_FIELDS)
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_PARTIAL_LIQUIDATE,
        action=op.action,
        sender_err=None,
        unknown_fields_ok=unknown_fields_ok,
    )
    if gate_error is not None:
        return gate_error, None

    account_pubkey = _require_str(op.data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    gate_error = _sender_gate_error(
        action_kind=RUNTIME_ACTION_PARTIAL_LIQUIDATE,
        action=op.action,
        sender_err=sender_err,
        unknown_fields_ok=True,
    )
    if gate_error is not None:
        return gate_error, None
    return None, account_pubkey


def _partial_liquidate_oracle_bridge_result(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    market: PerpMarketState,
    account_pubkey: str,
    fraction_bps: int,
) -> tuple[Optional[str], Any | None]:
    return _check_oracle_adapter_bridge(
        _OracleAdapterBridgeRequirement(
            config=ctx.config,
            data=op.data,
            consumer_module="zenodex.perps",
            action_kind="liquidate_account",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
            expected_action_id=_perps_liquidate_account_runtime_oracle_action_id(
                _LiquidateAccountOracleRuntimeRequest(
                    config=ctx.config,
                    market_id=op.market_id,
                    market=market,
                    account_pubkey=account_pubkey,
                    fraction_bps=fraction_bps,
                )
            ),
            required=ctx.config.require_oracle_adapter_for_isolated_partial_liquidate,
        )
    )


def _partial_liquidate_tau_source_facts(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    market: PerpMarketState,
    account_pubkey: str,
    account: PerpAccountState,
    fraction_bps: int,
    binding: PerpLiquidationTauSourceBinding,
) -> PerpLiquidationTauSourceFacts:
    global_state = market.global_state
    return PerpLiquidationTauSourceFacts(
        request_id=_perps_liquidate_account_runtime_oracle_action_id(
            _LiquidateAccountOracleRuntimeRequest(
                config=ctx.config,
                market_id=op.market_id,
                market=market,
                account_pubkey=account_pubkey,
                fraction_bps=fraction_bps,
            )
        ),
        market_id=op.market_id,
        account_id=account_pubkey,
        action=TAU_PARTIAL_LIQUIDATE_ACTION,
        fraction_bps=fraction_bps,
        now_epoch=int(global_state.get("now_epoch", 0)),
        position_base=int(account.position_base),
        collateral_quote=int(account.collateral_quote),
        index_price_e8=int(global_state.get("index_price_e8", 0)),
        maintenance_margin_bps=int(global_state.get("maintenance_margin_bps", 0)),
        depeg_buffer_bps=int(global_state.get("depeg_buffer_bps", 0)),
        oracle_seen=bool(global_state.get("oracle_seen", False)),
        oracle_last_update_epoch=int(global_state.get("oracle_last_update_epoch", 0)),
        max_oracle_staleness_epochs=int(
            global_state.get("max_oracle_staleness_epochs", 0)
        ),
        clearing_price_e8=int(global_state.get("clearing_price_e8", 0)),
        max_oracle_move_bps=int(global_state.get("max_oracle_move_bps", 0)),
        breaker_active=bool(global_state.get("breaker_active", False)),
        proof_result_ok=bool(binding.facts.proof_result_ok),
        proof_receipt_hash=str(binding.facts.proof_receipt_hash),
    )


def _partial_liquidate_authority_policy_receipt_error(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    raw_binding: Mapping[str, Any],
    binding: PerpLiquidationTauSourceBinding,
    oracle_adapter_bridge_result: Any | None,
) -> Optional[str]:
    context_supplied = "tau_source_authority_policy_context" in op.data
    receipt_supplied = "tau_source_authority_policy_receipt" in op.data
    receipt_required = (
        ctx.config.require_tau_source_authority_policy_receipt_for_isolated_partial_liquidate
    )
    if not (receipt_required or context_supplied or receipt_supplied):
        return None
    if binding.source_admission_envelope is None:
        return "tau_source_binding rejects: missing_source_admission_envelope"

    context = op.data.get("tau_source_authority_policy_context")
    if not isinstance(context, Mapping):
        return "tau_source_binding rejects: source_admission_envelope_missing_authority_policy_context"
    receipt = op.data.get("tau_source_authority_policy_receipt")
    if not isinstance(receipt, Mapping):
        return "tau_source_binding rejects: source_admission_envelope_missing_authority_policy_receipt"

    verifier = ctx.config.tau_source_authority_policy_receipt_verifier
    if verifier is None:
        return "tau_source_binding authority policy receipt verifier not configured"

    oracle_adapter_proof_receipt_hash = None
    if oracle_adapter_bridge_result is not None:
        oracle_adapter_proof_receipt_hash = _oracle_adapter_result_get(
            oracle_adapter_bridge_result,
            "proof_receipt_hash",
        )
    verifier_input = {
        "schema": "zenodex.perp_liquidation_tau_source_authority_policy_runtime_check.v1",
        "tau_source_binding": raw_binding,
        "oracle_adapter_proof_receipt_hash": oracle_adapter_proof_receipt_hash,
        "authority_policy_context": context,
        "authority_policy_receipt": receipt,
    }
    try:
        result = verifier(verifier_input)
    except (TypeError, ValueError, RuntimeError) as exc:
        return f"tau_source_binding authority policy receipt verifier error: {_safe_error_str(exc)}"

    if _oracle_adapter_result_get(result, "status") != "accepted":
        return (
            "tau_source_binding rejects: "
            f"{_oracle_adapter_error_summary(result)}"
        )
    if _oracle_adapter_result_get(result, "authority_policy_verified") is not True:
        return "tau_source_binding rejects: source_admission_envelope_authority_policy_not_verified"
    if _oracle_adapter_result_get(result, "authority_policy_receipt_verified") is not True:
        return "tau_source_binding rejects: source_admission_envelope_authority_policy_receipt_not_verified"
    return None


def _partial_liquidate_tau_source_binding_error(
    ctx: _PerpApplyCtx,
    *,
    op: PerpOp,
    market: PerpMarketState,
    account_pubkey: str,
    account: PerpAccountState,
    fraction_bps: int,
    oracle_adapter_bridge_result: Any | None = None,
) -> Optional[str]:
    raw_binding = op.data.get("tau_source_binding")
    if raw_binding is None:
        if ctx.config.require_tau_source_binding_for_isolated_partial_liquidate:
            return "partial_liquidate requires tau_source_binding"
        return None
    if not isinstance(raw_binding, Mapping):
        return "tau_source_binding must be an object"
    try:
        binding = perp_liquidation_tau_source_binding_from_payload(raw_binding)
    except (TypeError, ValueError) as exc:
        return f"tau_source_binding invalid: {_safe_error_str(exc)}"

    expected_facts = _partial_liquidate_tau_source_facts(
        ctx,
        op=op,
        market=market,
        account_pubkey=account_pubkey,
        account=account,
        fraction_bps=fraction_bps,
        binding=binding,
    )
    if binding.facts != expected_facts:
        return "tau_source_binding source facts mismatch"

    expected_hash = perp_liquidation_tau_source_facts_hash(expected_facts)
    if (
        binding.expected_source_facts_hash != expected_hash
        or binding.proof_source_facts_hash != expected_hash
    ):
        return "tau_source_binding source hash mismatch"

    flags = derive_perp_liquidation_flags_from_source_binding(binding)
    if expected_perp_liquidation_o4(flags) != 1:
        reasons = ",".join(source_binding_reject_reasons(binding))
        if not reasons:
            reasons = "tau_guard_rejected"
        return f"tau_source_binding rejects: {reasons}"
    root_expected = (
        ctx.config.isolated_partial_liquidate_tau_source_state_root_hash is not None
        or ctx.config.isolated_partial_liquidate_tau_source_state_root_kind is not None
    )
    membership_required = (
        ctx.config.require_tau_source_membership_proof_for_isolated_partial_liquidate
    )
    root_required = (
        ctx.config.require_tau_source_state_root_binding_for_isolated_partial_liquidate
        or root_expected
        or membership_required
    )
    root_binding = binding.source_state_root_binding
    root_supplied = root_binding is not None
    membership_supplied = (
        root_binding is not None
        and root_binding.source_membership_proof is not None
    )
    authority_supplied = (
        root_binding is not None
        and (
            root_binding.source_root_authority is not None
            or root_binding.source_root_authority_binding is not None
        )
    )
    envelope_supplied = binding.source_admission_envelope is not None
    if (
        root_supplied
        and ctx.config.isolated_partial_liquidate_tau_source_state_root_hash is None
        and not authority_supplied
        and not envelope_supplied
    ):
        return "tau_source_binding source state root anchor expected but not configured"
    if (
        ctx.config.require_tau_source_state_root_binding_for_isolated_partial_liquidate
        and ctx.config.isolated_partial_liquidate_tau_source_state_root_hash is None
    ):
        return "tau_source_binding source state root expected but not configured"
    if (
        membership_required
        and ctx.config.isolated_partial_liquidate_tau_source_state_root_hash is None
    ):
        return "tau_source_binding source membership root expected but not configured"
    root_reason = source_state_root_binding_reject_reason(
        binding,
        expected_source_state_root_hash=(
            ctx.config.isolated_partial_liquidate_tau_source_state_root_hash
        ),
        expected_state_root_kind=(
            ctx.config.isolated_partial_liquidate_tau_source_state_root_kind
        ),
    )
    if root_reason is not None:
        if (
            root_reason == "missing_source_state_root_binding"
            and not root_required
        ):
            return None
        if root_supplied or root_required:
            return f"tau_source_binding rejects: {root_reason}"
    if membership_required or membership_supplied:
        membership_reason = source_membership_proof_reject_reason(binding)
        if membership_reason is not None:
            return f"tau_source_binding rejects: {membership_reason}"
    authority_required = (
        ctx.config.require_tau_source_root_authority_for_isolated_partial_liquidate
    )
    if authority_required or authority_supplied:
        if (
            ctx.config.isolated_partial_liquidate_tau_source_root_authority_state_root_hash
            is None
        ):
            return "tau_source_binding source root authority state root expected but not configured"
        if (
            ctx.config.isolated_partial_liquidate_tau_source_root_authority_policy_hash
            is None
        ):
            return "tau_source_binding source root authority policy expected but not configured"
        if not ctx.config.isolated_partial_liquidate_tau_source_root_authority_signer_pubkeys:
            return "tau_source_binding source root authority signer set expected but not configured"
        authority_reason = source_root_authority_reject_reason(
            binding,
            now_epoch=int(market.global_state.get("now_epoch", 0)),
            expected_authority_state_root_hash=(
                ctx.config.isolated_partial_liquidate_tau_source_root_authority_state_root_hash
            ),
            expected_policy_hash=(
                ctx.config.isolated_partial_liquidate_tau_source_root_authority_policy_hash
            ),
            allowed_signer_pubkeys=(
                ctx.config.isolated_partial_liquidate_tau_source_root_authority_signer_pubkeys
            ),
        )
        if authority_reason is not None:
            return f"tau_source_binding rejects: {authority_reason}"
    envelope_required = (
        ctx.config.require_tau_source_admission_envelope_for_isolated_partial_liquidate
    )
    if envelope_required or envelope_supplied:
        oracle_adapter_proof_receipt_hash = None
        if oracle_adapter_bridge_result is not None:
            oracle_adapter_proof_receipt_hash = _oracle_adapter_result_get(
                oracle_adapter_bridge_result,
                "proof_receipt_hash",
            )
        try:
            envelope_reason = source_admission_envelope_reject_reason(
                binding,
                oracle_adapter_proof_receipt_hash=(
                    None
                    if oracle_adapter_proof_receipt_hash is None
                    else str(oracle_adapter_proof_receipt_hash)
                ),
            )
        except (TypeError, ValueError) as exc:
            envelope_reason = (
                f"source_admission_envelope_invalid: {_safe_error_str(exc)}"
            )
        if envelope_reason is not None:
            return f"tau_source_binding rejects: {envelope_reason}"
    authority_policy_receipt_error = _partial_liquidate_authority_policy_receipt_error(
        ctx,
        op=op,
        raw_binding=raw_binding,
        binding=binding,
        oracle_adapter_bridge_result=oracle_adapter_bridge_result,
    )
    if authority_policy_receipt_error is not None:
        return authority_policy_receipt_error
    return None


def _run_isolated_partial_liquidate(
    market: PerpMarketState,
    *,
    account: PerpAccountState,
    fraction_bps: int,
) -> tuple[Optional[str], Optional[_IsolatedPartialLiquidateResult]]:
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(account),
        action="partial_liquidate",
        params={"fraction_bps": fraction_bps, "auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "partial_liquidate rejected", None
    post_global, post_acct = _split_kernel_state(res.state)
    _preserve_isolated_shell_global_fields(pre_global=market.global_state, post_global=post_global)
    return None, _IsolatedPartialLiquidateResult(
        global_state=post_global,
        account=post_acct,
        effects=dict(res.effects or {}),
    )


def _commit_isolated_partial_liquidate(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    market: PerpMarketState,
    account_pubkey: str,
    result: _IsolatedPartialLiquidateResult,
) -> None:
    accounts = dict(market.accounts)
    pre_account = accounts.get(account_pubkey) or _kernel_initial_account_state()
    accounts[account_pubkey] = result.account
    emitted_root: str | None = None
    emitted_source_hash: str | None = None
    emitted_source_rows: tuple[ClosedFundingSourceRow, ...] = ()
    pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
    pending_source_roots = tuple(
        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
    )
    if int(pre_account.position_base) != 0 and int(result.account.position_base) == 0:
        pre_accounts = _isolated_open_position_accounts(market.accounts)
        if pre_accounts:
            emitted_root = pre_close_position_snapshot_hash(
                pre_accounts,
                market_id=op.market_id,
                epoch=int(market.global_state.get("now_epoch", 0)),
            )
            pending_roots = _append_pending_funding_closeout_root(market, emitted_root)
            emitted_source_rows = (
                _funding_closeout_source_availability_row_for_closeout(
                    account_pubkey=account_pubkey,
                    epoch=int(market.global_state.get("now_epoch", 0)),
                    result=result,
                ),
            )
            emitted_source_hash = funding_closeout_source_availability_hash(
                emitted_source_rows
            )
            pending_source_roots = _append_pending_funding_closeout_source_availability_hash(
                market,
                emitted_source_hash,
            )

    ctx.markets[op.market_id] = _isolated_market_with(
        market,
        global_state=result.global_state,
        accounts=accounts,
        pending_funding_closeout_root_hashes=pending_roots,
        pending_funding_closeout_source_availability_hashes=pending_source_roots,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "account_pubkey": account_pubkey,
            "funding_closeout_pre_close_position_root_hash": emitted_root,
            "funding_closeout_source_availability_hash": emitted_source_hash,
            "funding_closeout_source_availability_rows": [
                asdict(row) for row in emitted_source_rows
            ],
            "effects": dict(result.effects),
        }
    )


def _apply_isolated_partial_liquidate(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState
) -> Optional[str]:
    err, account_pubkey = _partial_liquidate_bound_account(ctx, op=op)
    if err is not None:
        return err
    if account_pubkey is None:
        return "internal error: partial_liquidate account missing"

    fraction_bps = _require_int(op.data.get("fraction_bps", 0), name="fraction_bps", non_negative=True)
    acct = market.accounts.get(account_pubkey) or _kernel_initial_account_state()
    err, oracle_adapter_bridge_result = _partial_liquidate_oracle_bridge_result(
        ctx,
        op=op,
        market=market,
        account_pubkey=account_pubkey,
        fraction_bps=fraction_bps,
    )
    if err is not None:
        return err

    err = _partial_liquidate_tau_source_binding_error(
        ctx,
        op=op,
        market=market,
        account_pubkey=account_pubkey,
        account=acct,
        fraction_bps=fraction_bps,
        oracle_adapter_bridge_result=oracle_adapter_bridge_result,
    )
    if err is not None:
        return err

    err, result = _run_isolated_partial_liquidate(
        market,
        account=acct,
        fraction_bps=fraction_bps,
    )
    if err is not None:
        return err
    if result is None:
        return "internal error: partial_liquidate result missing"

    _commit_isolated_partial_liquidate(
        ctx,
        i=i,
        op=op,
        market=market,
        account_pubkey=account_pubkey,
        result=result,
    )
    return None


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
    "carry_funding_closeout_liability": _apply_isolated_carry_funding_closeout_liability,
    "settle_funding_closeout_carried_liability": (
        _apply_isolated_settle_funding_closeout_carried_liability
    ),
    "settle_funding_closeout_recovery": (
        _apply_isolated_settle_funding_closeout_recovery
    ),
}


def _apply_isolated_op(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    handler = _ISOLATED_ACTION_HANDLERS.get(op.action)
    if handler is None:
        return f"unknown perps action: {op.action}"
    return handler(ctx, i=i, op=op, market=market)


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
        _ClearinghouseOracleRuntimeRequest(
            config=config,
            market_id=market_id,
            action_kind="settle_epoch",
            market_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
            quote_asset=market.quote_asset,
            state=state_for_oracle,
            participant_pubkeys=participant_pubkeys,
        )
    )
    err = _require_oracle_adapter_bridge(
        _OracleAdapterBridgeRequirement(
            config=config,
            data=data,
            consumer_module="zenodex.perps",
            action_kind="settle_epoch",
            expected_query_id=_ORACLE_PERPS_INDEX_QUERY_ID,
            expected_profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            expected_action_id=expected_action_id,
            required=config.require_oracle_adapter_for_clearinghouse_settle_epoch,
        )
    )
    if err is not None:
        return err
    return _check_clearinghouse_settle_oracle_authorization(
        _ClearinghouseSettleOracleAuthorizationRequest(
            config=config,
            data=data,
            market_id=market_id,
            market_kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
            quote_asset=market.quote_asset,
            state=state_for_oracle,
            participant_pubkeys=participant_pubkeys,
        )
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


def _apply_chnp_join_market(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
    allowed = {"module", "version", "market_id", "action", "account_pubkey"}
    unknown = _reject_unknown_fields(data, allowed, error="join_market has unknown fields")
    if unknown is not None:
        return unknown
    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
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


def _apply_chnp_collateral(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
    allowed = {"module", "version", "market_id", "action", "account_pubkey", "amount"}
    unknown = _reject_unknown_fields(data, allowed, error=f"{action} has unknown fields")
    if unknown is not None:
        return unknown
    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    sender_err = _require_sender_bound_account_pubkey(
        account_pubkey=account_pubkey,
        tx_sender_pubkey=ctx.tx_sender_pubkey,
    )
    if sender_err is not None:
        return sender_err
    amount = _require_int(data.get("amount"), name="amount", non_negative=True)
    amount_e8 = int(amount) * _E8_SCALE
    if amount_e8 > _np_core.I128_MAX:
        return f"{action} amount exceeds clearinghouse_np ledger bound"
    ms = _chnp_market_to_core(chnp_market)
    if action == "deposit_collateral":
        if ctx.balances.get(account_pubkey, chnp_market.quote_asset) < amount:
            return "insufficient balance for deposit"
        try:
            ms2 = _np_core.deposit(ms, account_pubkey, amount_e8)
        except Exception as exc:
            return _safe_error_str(exc)
        ctx.balances.subtract(account_pubkey, chnp_market.quote_asset, amount)
    else:
        if chnp_market.role_for_pubkey(account_pubkey) is None:
            return "unknown account_pubkey for this clearinghouse_np market"
        try:
            ms2 = _np_core.withdraw(ms, account_pubkey, amount_e8)
        except Exception as exc:
            return _safe_error_str(exc)
        ctx.balances.add(account_pubkey, chnp_market.quote_asset, amount)
    ctx.markets[market_id] = _chnp_core_to_market(
        chnp_market.quote_asset,
        ms2,
        pending_intents=chnp_market.pending_intents,
        pending_price_fields=_chnp_pending_price_fields(chnp_market),
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey})
    return None


def _apply_chnp_submit_intent(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
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
        tx_sender_pubkey=ctx.tx_sender_pubkey,
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


def _apply_chnp_publish_clearing_price(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState
) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
    oracle_pubkey = (ctx.config.oracle_pubkey or "").strip()
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
        _PerpSignatureVerificationRequest(
            config=ctx.config,
            signer_pubkey=oracle_pubkey,
            nonce=oracle_nonce,
            signature=oracle_sig,
            op=data,
            nonces=ctx.nonces,
            block_timestamp=ctx.block_timestamp,
        )
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


def _apply_chnp_run_or_settle_epoch(
    ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState
) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
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
    op_err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
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
        ctx.config,
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


def _apply_chnp_advance_epoch(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, chnp_market: _NpMarketState) -> str | None:
    action = op.action
    market_id = op.market_id
    data = op.data
    allowed = {"module", "version", "market_id", "action"}
    unknown = _reject_unknown_fields(data, allowed, error="advance_epoch has unknown fields")
    if unknown is not None:
        return unknown
    op_err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
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


def _apply_chnp_op(
    ctx: _PerpApplyCtx,
    *,
    i: int,
    op: PerpOp,
    chnp_market: _NpMarketState,
) -> str | None:
    action = op.action

    if action == "join_market":
        return _apply_chnp_join_market(ctx, i=i, op=op, chnp_market=chnp_market)

    if action in ("deposit_collateral", "withdraw_collateral"):
        return _apply_chnp_collateral(ctx, i=i, op=op, chnp_market=chnp_market)

    if action == "submit_intent":
        return _apply_chnp_submit_intent(ctx, i=i, op=op, chnp_market=chnp_market)

    if action == "match_intents":
        return "match_intents disabled for clearinghouse_np_v1; use run_epoch"

    if action == "publish_clearing_price":
        return _apply_chnp_publish_clearing_price(ctx, i=i, op=op, chnp_market=chnp_market)

    if action in ("run_epoch", "settle_epoch"):
        return _apply_chnp_run_or_settle_epoch(ctx, i=i, op=op, chnp_market=chnp_market)

    if action == "advance_epoch":
        return _apply_chnp_advance_epoch(ctx, i=i, op=op, chnp_market=chnp_market)

    return f"unknown perps action: {action}"


_PERP_INIT_ACTIONS = frozenset({"init_market", "init_market_2p", "init_market_3p", "init_market_np"})
_CLEARINGHOUSE_VERSIONS = frozenset(
    {
        PERP_OP_VERSION_CH2P_V0_2,
        PERP_OP_VERSION_CH2P_V1_0,
        PERP_OP_VERSION_CH3P_V1_1,
        PERP_OP_VERSION_CHNP_V1_2,
    }
)


def _is_clearinghouse_version(version: str) -> bool:
    return version in _CLEARINGHOUSE_VERSIONS


def _apply_init_market(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    action = op.action
    market_id = op.market_id
    version = op.version
    data = op.data
    if version != PERP_OP_VERSION_V0_1:
        return "init_market requires perps.version=0.1"
    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    if market_id in ctx.markets:
        return "market already exists"

    quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
    allowed = {"module", "version", "market_id", "action", "quote_asset"}
    extra = set(data.keys()) - allowed
    if extra:
        return "init_market has unknown fields"

    ctx.markets[market_id] = PerpMarketState(
        quote_asset=quote_asset,
        global_state=_kernel_initial_global_state(),
        accounts={},
    )
    ctx.effects.append({"i": i, "market_id": market_id, "action": action})
    return None


_INIT_MARKET_2P_FIELDS = frozenset(
    {
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
)


def _init_market_2p_version_error(action: str, *, version_ok: bool) -> Optional[str]:
    if version_ok:
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_INIT_MARKET_2P,
        action=action,
        version_ok=False,
        unknown_fields_ok=True,
    )
    return surface_err or "init_market_2p requires perps.version=0.2 or 1.0"


def _init_market_2p_distinct_accounts_ok(accounts: _Ch2pPositionAccounts) -> bool:
    distinct_accounts_ok = accounts.account_a_pubkey != accounts.account_b_pubkey
    try:
        a_b = _hex_to_bytes_allow_0x(accounts.account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
        b_b = _hex_to_bytes_allow_0x(accounts.account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
    except (TypeError, ValueError):
        return bool(distinct_accounts_ok)
    return bool(distinct_accounts_ok and a_b != b_b)


def _init_market_2p_surface_error(
    action: str,
    *,
    data: Mapping[str, Any],
    version_ok: bool,
    distinct_accounts_ok: bool,
) -> Optional[str]:
    return _evaluate_signed_surface(
        action_kind=ACTION_INIT_MARKET_2P,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=not (set(data.keys()) - _INIT_MARKET_2P_FIELDS),
        distinct_accounts_ok=distinct_accounts_ok,
    )


def _commit_init_market_2p(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, spec: _InitMarket2pSpec) -> str | None:
    ctx.perps_version = max(ctx.perps_version, PERPS_STATE_VERSION_V5)
    try:
        init_state = _ch2p_init_state_dict()
    except ValueError as exc:
        return str(exc)
    ctx.markets[op.market_id] = PerpClearinghouse2pMarketState(
        quote_asset=spec.quote_asset,
        account_a_pubkey=spec.accounts.account_a_pubkey,
        account_b_pubkey=spec.accounts.account_b_pubkey,
        state=init_state,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "account_a_pubkey": spec.accounts.account_a_pubkey,
            "account_b_pubkey": spec.accounts.account_b_pubkey,
        }
    )
    return None


def _apply_init_market_2p(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    action = op.action
    market_id = op.market_id
    version = op.version
    data = op.data
    version_ok = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
    version_err = _init_market_2p_version_error(action, version_ok=version_ok)
    if version_err is not None:
        return version_err
    if market_id in ctx.markets:
        return "market already exists"

    quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
    accounts = _read_ch2p_position_accounts(data)
    distinct_accounts_ok = _init_market_2p_distinct_accounts_ok(accounts)
    auth = _read_ch2p_position_auth(data)

    surface_err = _init_market_2p_surface_error(
        action=action,
        data=data,
        version_ok=version_ok,
        distinct_accounts_ok=distinct_accounts_ok,
    )
    if surface_err is not None:
        return surface_err

    sig_err = _verify_ch2p_position_signatures(ctx, data=data, accounts=accounts, auth=auth)
    if sig_err is not None:
        return sig_err

    return _commit_init_market_2p(
        ctx,
        i=i,
        op=op,
        spec=_InitMarket2pSpec(quote_asset=quote_asset, accounts=accounts),
    )


_INIT_MARKET_3P_FIELDS = frozenset(
    {
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
)


def _init_market_3p_version_error(action: str, *, version_ok: bool) -> Optional[str]:
    if version_ok:
        return None
    surface_err = _evaluate_signed_surface(
        action_kind=ACTION_INIT_MARKET_3P,
        action=action,
        version_ok=False,
        unknown_fields_ok=True,
    )
    return surface_err or "init_market_3p requires perps.version=1.1"


def _init_market_3p_distinct_accounts_ok(accounts: _Ch3pPositionAccounts) -> bool:
    distinct_accounts_ok = len(
        {
            accounts.account_a_pubkey,
            accounts.account_b_pubkey,
            accounts.account_c_pubkey,
        }
    ) == 3
    try:
        a_b = _hex_to_bytes_allow_0x(accounts.account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
        b_b = _hex_to_bytes_allow_0x(accounts.account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
        c_b = _hex_to_bytes_allow_0x(accounts.account_c_pubkey, name="account_c_pubkey", expected_nbytes=48)
    except (TypeError, ValueError):
        return bool(distinct_accounts_ok)
    return bool(distinct_accounts_ok and len({a_b, b_b, c_b}) == 3)


def _init_market_3p_surface_error(
    action: str,
    *,
    data: Mapping[str, Any],
    version_ok: bool,
    distinct_accounts_ok: bool,
) -> Optional[str]:
    return _evaluate_signed_surface(
        action_kind=ACTION_INIT_MARKET_3P,
        action=action,
        version_ok=version_ok,
        unknown_fields_ok=not (set(data.keys()) - _INIT_MARKET_3P_FIELDS),
        distinct_accounts_ok=distinct_accounts_ok,
    )


def _commit_init_market_3p(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, spec: _InitMarket3pSpec) -> str | None:
    ctx.perps_version = max(ctx.perps_version, PERPS_STATE_VERSION_V5)
    try:
        init_state = _ch3p_init_state_dict()
    except ValueError as exc:
        return str(exc)
    ctx.markets[op.market_id] = PerpClearinghouse3pTransferMarketState(
        quote_asset=spec.quote_asset,
        account_a_pubkey=spec.accounts.account_a_pubkey,
        account_b_pubkey=spec.accounts.account_b_pubkey,
        account_c_pubkey=spec.accounts.account_c_pubkey,
        state=init_state,
    )
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "account_a_pubkey": spec.accounts.account_a_pubkey,
            "account_b_pubkey": spec.accounts.account_b_pubkey,
            "account_c_pubkey": spec.accounts.account_c_pubkey,
        }
    )
    return None


def _apply_init_market_3p(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    action = op.action
    market_id = op.market_id
    version = op.version
    data = op.data
    version_ok = version == PERP_OP_VERSION_CH3P_V1_1
    version_err = _init_market_3p_version_error(action, version_ok=version_ok)
    if version_err is not None:
        return version_err
    if market_id in ctx.markets:
        return "market already exists"

    quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
    accounts = _read_ch3p_position_accounts(data)
    distinct_accounts_ok = _init_market_3p_distinct_accounts_ok(accounts)
    auth = _read_ch3p_position_auth(data)

    surface_err = _init_market_3p_surface_error(
        action=action,
        data=data,
        version_ok=version_ok,
        distinct_accounts_ok=distinct_accounts_ok,
    )
    if surface_err is not None:
        return surface_err

    sig_err = _verify_ch3p_position_signatures(ctx, data=data, accounts=accounts, auth=auth)
    if sig_err is not None:
        return sig_err

    return _commit_init_market_3p(
        ctx,
        i=i,
        op=op,
        spec=_InitMarket3pSpec(quote_asset=quote_asset, accounts=accounts),
    )


_INIT_MARKET_NP_FIELDS = frozenset(
    {
        "module",
        "version",
        "market_id",
        "action",
        "quote_asset",
        "index_price_e8",
        "insurance_seed_e8",
        "params",
    }
)


def _init_market_np_header_error(ctx: _PerpApplyCtx, *, op: PerpOp) -> str | None:
    if op.version != PERP_OP_VERSION_CHNP_V1_2:
        return "init_market_np requires perps.version=1.2"
    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    if op.market_id in ctx.markets:
        return "market already exists"
    if not op.market_id.startswith(PERP_CHNP_MARKET_PREFIX):
        return "clearinghouse_np market_id must start with perp:chnp:"
    return None


def _read_init_market_np_inputs(ctx: _PerpApplyCtx, *, op: PerpOp) -> tuple[str | None, _InitMarketNpInputs | None]:
    data = op.data
    quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
    index_price_e8 = _require_int(data.get("index_price_e8"), name="index_price_e8", non_negative=True)
    if index_price_e8 <= 0:
        return "index_price_e8 must be positive", None
    if set(data.keys()) - _INIT_MARKET_NP_FIELDS:
        return "init_market_np has unknown fields", None

    insurance_seed_e8 = _require_int(
        data.get("insurance_seed_e8", 0),
        name="insurance_seed_e8",
        non_negative=True,
    )
    insurance_seed_quote = 0
    if insurance_seed_e8:
        if insurance_seed_e8 % _E8_SCALE != 0:
            return "insurance_seed_e8 must be quote-unit aligned", None
        insurance_seed_quote = insurance_seed_e8 // _E8_SCALE
        if ctx.balances.get(ctx.tx_sender_pubkey, quote_asset) < insurance_seed_quote:
            return "insufficient balance for insurance seed", None

    params_obj = data.get("params", {})
    if not isinstance(params_obj, Mapping):
        return "params must be an object", None
    return None, _InitMarketNpInputs(
        quote_asset=quote_asset,
        index_price_e8=index_price_e8,
        insurance_seed_e8=insurance_seed_e8,
        insurance_seed_quote=insurance_seed_quote,
        params_obj=params_obj,
    )


def _build_init_market_np_market(inputs: _InitMarketNpInputs) -> tuple[str | None, _NpMarketState | None]:
    try:
        param_overrides = _validated_control_params(
            inputs.params_obj,
            bounds=_CLEARINGHOUSE_NP_CONTROL_PARAM_BOUNDS,
            name="params",
        )
        init_ms = _np_core.init_market(
            inputs.index_price_e8,
            params=_np_core.MarketParams(**param_overrides),
            insurance_seed_e8=inputs.insurance_seed_e8,
        )
        return None, _chnp_core_to_market(inputs.quote_asset, init_ms, pending_intents=())
    except Exception as exc:
        return _safe_error_str(exc), None


def _apply_init_market_np(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    err = _init_market_np_header_error(ctx, op=op)
    if err is not None:
        return err

    err, inputs = _read_init_market_np_inputs(ctx, op=op)
    if err is not None:
        return err
    if inputs is None:
        return "internal error: init_market_np inputs missing"

    ctx.perps_version = max(ctx.perps_version, PERPS_STATE_VERSION_V5)
    err, next_market = _build_init_market_np_market(inputs)
    if err is not None:
        return err
    if next_market is None:
        return "internal error: init_market_np market missing"

    if inputs.insurance_seed_quote:
        ctx.balances.subtract(ctx.tx_sender_pubkey, inputs.quote_asset, inputs.insurance_seed_quote)
    ctx.markets[op.market_id] = next_market
    ctx.effects.append(
        {
            "i": i,
            "market_id": op.market_id,
            "action": op.action,
            "quote_asset": inputs.quote_asset,
            "insurance_seed_e8": int(inputs.insurance_seed_e8),
        }
    )
    return None


def _apply_perp_init_op(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    if op.action == "init_market":
        return _apply_init_market(ctx, i=i, op=op)
    if op.action == "init_market_2p":
        return _apply_init_market_2p(ctx, i=i, op=op)
    if op.action == "init_market_3p":
        return _apply_init_market_3p(ctx, i=i, op=op)
    if op.action == "init_market_np":
        return _apply_init_market_np(ctx, i=i, op=op)
    return f"unknown perps action: {op.action}"


def _apply_existing_perp_market_op(ctx: _PerpApplyCtx, *, i: int, op: PerpOp) -> str | None:
    market_any = ctx.markets.get(op.market_id)
    if market_any is None:
        return "unknown market_id"

    is_ch2p = op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
    is_ch3p = op.version == PERP_OP_VERSION_CH3P_V1_1
    is_chnp = op.version == PERP_OP_VERSION_CHNP_V1_2
    if is_ch2p:
        if not isinstance(market_any, PerpClearinghouse2pMarketState):
            return "market kind mismatch for clearinghouse_2p operation"
        return _apply_ch2p_op(ctx, i=i, op=op, ch2p_market=market_any)
    if is_ch3p:
        if not isinstance(market_any, PerpClearinghouse3pTransferMarketState):
            return "market kind mismatch for clearinghouse_3p operation"
        return _apply_ch3p_op(ctx, i=i, op=op, ch3p_market=market_any)
    if is_chnp:
        if not isinstance(market_any, _NpMarketState):
            return "market kind mismatch for clearinghouse_np operation"
        return _apply_chnp_op(ctx, i=i, op=op, chnp_market=market_any)
    if not isinstance(market_any, PerpMarketState):
        return "market kind mismatch for isolated operation"
    return _apply_isolated_op(ctx, i=i, op=op, market=market_any)


def _fixed_position_precedes_publish_error(ops: List[PerpOp]) -> str | None:
    future_ch2p_publishes: set[str] = set()
    future_ch3p_publishes: set[str] = set()
    earliest_error: str | None = None
    for op in reversed(ops):
        is_ch2p = op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        is_ch3p = op.version == PERP_OP_VERSION_CH3P_V1_1
        if op.action == "publish_clearing_price":
            if is_ch2p:
                future_ch2p_publishes.add(op.market_id)
            elif is_ch3p:
                future_ch3p_publishes.add(op.market_id)
            continue
        if (
            op.action == "set_position_pair"
            and is_ch2p
            and op.market_id in future_ch2p_publishes
        ):
            earliest_error = (
                "set_position_pair cannot precede publish_clearing_price for the same market "
                "in one transaction"
            )
        elif (
            op.action == "set_position_triplet"
            and is_ch3p
            and op.market_id in future_ch3p_publishes
        ):
            earliest_error = (
                "set_position_triplet cannot precede publish_clearing_price for the same market "
                "in one transaction"
            )
    return earliest_error


def _perp_ops_batch_posture_error(config: PerpEngineConfig, ops: List[PerpOp]) -> str | None:
    if any(op.action == "publish_clearing_price" for op in ops):
        posture_err = _oracle_reward_posture_error(config)
        if posture_err is not None:
            return posture_err

    chronology_err = _fixed_position_precedes_publish_error(ops)
    if chronology_err is not None:
        return chronology_err

    has_isolated = any(op.version == PERP_OP_VERSION_V0_1 for op in ops)
    has_clearinghouse = any(_is_clearinghouse_version(op.version) for op in ops)
    if has_isolated and has_clearinghouse:
        return "cannot mix isolated and clearinghouse perps ops in one tx"
    if has_isolated and not config.allow_isolated_markets:
        return "isolated perps disabled by config (enable allow_isolated_markets)"
    return None


def _build_perp_apply_ctx(
    *,
    config: PerpEngineConfig,
    state: DexState,
    ops: List[PerpOp],
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> _PerpApplyCtx:
    balances = _copy_balance_table(state.balances)
    nonces = _copy_nonce_table(state.nonces)

    perps = state.perps
    perps_version = PERPS_STATE_VERSION
    if perps is None:
        perps = PerpsState(version=PERPS_STATE_VERSION, markets={})
    else:
        perps_version = int(perps.version)

    markets = dict(perps.markets)
    # Perps state v5 is a strict superset of v4 (adds per-market kind tags).
    if any(_is_clearinghouse_version(op.version) for op in ops):
        perps_version = max(perps_version, PERPS_STATE_VERSION_V5)

    return _PerpApplyCtx(
        config=config,
        balances=balances,
        nonces=nonces,
        markets=markets,
        effects=[],
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=block_timestamp,
        perps_version=perps_version,
    )


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

        posture_err = _perp_ops_batch_posture_error(config, ops)
        if posture_err is not None:
            return PerpTxResult(ok=False, error=posture_err)

        ctx = _build_perp_apply_ctx(
            config=config,
            state=state,
            ops=ops,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=block_timestamp,
        )

        for i, op in enumerate(ops):
            if op.action in _PERP_INIT_ACTIONS:
                err = _apply_perp_init_op(ctx, i=i, op=op)
            else:
                err = _apply_existing_perp_market_op(ctx, i=i, op=op)
            if err is not None:
                return PerpTxResult(ok=False, error=err)

        next_perps = PerpsState(version=ctx.perps_version, markets=ctx.markets) if ctx.markets else None
        next_state = replace(state, balances=ctx.balances, nonces=ctx.nonces, perps=next_perps)
        return PerpTxResult(ok=True, state=next_state, effects=ctx.effects)

    except Exception as exc:
        return PerpTxResult(ok=False, error=_safe_error_str(exc))
