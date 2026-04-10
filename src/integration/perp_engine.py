"""
Perpetuals execution adapter for Tau Net-style transactions.

This module applies operation group "5" (perps) to `DexState` in a deterministic,
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
import hashlib
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import re
import sys
from typing import Any, Dict, List, Mapping, Optional

from ..core.dex import DexState
from ..core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perp_v2.funding_rule import compute_funding_rate_bps
from ..core.perp_v2.math import MAX_COLLATERAL
from ..core.perp_v2.math import funding_payment as _perp_v2_funding_payment
from ..core.perp_v2.math import is_oracle_fresh as _perp_v2_is_oracle_fresh
from ..core.perp_v2.math import maint_margin_req as _perp_v2_maint_margin_req
from ..core.perp_v2.math import settle_price as _perp_v2_settle_price
from ..core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS,
    PERP_GLOBAL_KEYS,
    PERPS_STATE_VERSION,
    PERPS_STATE_VERSION_V5,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from ..state.balances import BalanceTable
from ..state.canonical import bounded_json_utf8_size, canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes
from ..state.nonces import NonceTable


PERP_OP_MODULE = "TauPerp"
PERP_OP_VERSION_V0_1 = "0.1"
# Clearinghouse (2-party) posture versions:
# - 0.2: initial rollout (kept for compatibility)
# - 1.0: "production" tag for the same semantics
PERP_OP_VERSION_CH2P_V0_2 = "0.2"
PERP_OP_VERSION_CH2P_V1_0 = "1.0"
PERP_OP_VERSION_CH3P_V1_1 = "1.1"

# v0.2 markets are explicitly namespaced to avoid mixing semantics without a snapshot schema change.
# This is a fail-closed API convention, not a security boundary.
PERP_CH2P_MARKET_PREFIX = "perp:ch2p:"
PERP_CH3P_MARKET_PREFIX = "perp:ch3p:"

_E8_SCALE = 100_000_000

try:
    from py_ecc.bls import G2Basic  # type: ignore

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None  # type: ignore[assignment]
    _BLS_AVAILABLE = False

_HEX_CHARS_RE = re.compile(r"^[0-9a-fA-F]+$")
_U32_MAX = 0xFFFFFFFF
_BPS_SCALE = 10_000


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

    # Anti-farming hardening:
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

    # Anti-farming guard:
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
) -> Dict[str, Any]:
    updates = _validated_control_params(params, bounds=_CLEARINGHOUSE_CONTROL_PARAM_BOUNDS, name="params")
    if not updates:
        return dict(state)

    new_state = dict(state)
    for k, v in updates.items():
        new_state[k] = int(v)

    old_liquidation_penalty_bps = int(state.get("liquidation_penalty_bps", 0))
    new_liquidation_penalty_bps = int(new_state.get("liquidation_penalty_bps", 0))
    if new_liquidation_penalty_bps > old_liquidation_penalty_bps:
        if kind == "ch2p":
            has_open_positions = bool(int(state.get("position_base_a", 0)) != 0 or int(state.get("position_base_b", 0)) != 0)
        elif kind == "ch3p":
            has_open_positions = bool(
                int(state.get("position_base_a", 0)) != 0
                or int(state.get("position_base_b", 0)) != 0
                or int(state.get("position_base_c", 0)) != 0
            )
        else:  # pragma: no cover
            has_open_positions = False
        if has_open_positions:
            raise ValueError("invalid params: cannot increase liquidation_penalty_bps while positions are open")

    # Additional policy guard (stricter than some specs): liquidation penalty should be below maintenance.
    if int(new_state["liquidation_penalty_bps"]) >= int(new_state["maintenance_margin_bps"]):
        raise ValueError("invalid params: require liquidation_penalty_bps < maintenance_margin_bps")

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
    # Oracle-manipulation posture guard:
    # require reward subsidy + safety margin to stay below fee friction.
    oracle_spot_fee_bps: int = 30
    oracle_spot_reward_bps: int = 0
    oracle_spot_reward_safety_margin_bps: int = 1
    # Anti-bounty-farming posture guard:
    # require a non-trivial minimum collectible liquidation penalty for bounty-eligible notional.
    min_collectible_liquidation_penalty_quote: int = 1_000


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

    raw = operations.get("5")
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError("operations['5'] must be a list")
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
        if is_ch2p and not market_id.startswith(PERP_CH2P_MARKET_PREFIX):
            raise ValueError(f"clearinghouse markets must start with {PERP_CH2P_MARKET_PREFIX!r}")
        if is_ch3p and not market_id.startswith(PERP_CH3P_MARKET_PREFIX):
            raise ValueError(f"clearinghouse markets must start with {PERP_CH3P_MARKET_PREFIX!r}")
        if not (is_ch2p or is_ch3p) and (
            market_id.startswith(PERP_CH2P_MARKET_PREFIX) or market_id.startswith(PERP_CH3P_MARKET_PREFIX)
        ):
            raise ValueError("isolated markets cannot start with clearinghouse prefixes")

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
    return {k: st[k] for k in sorted(PERP_GLOBAL_KEYS)}


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
    global_state = {k: state[k] for k in sorted(PERP_GLOBAL_KEYS)}
    acct = PerpAccountState(
        position_base=int(state.get("position_base", 0)),
        entry_price_e8=int(state.get("entry_price_e8", 0)),
        collateral_quote=int(state.get("collateral_quote", 0)),
        funding_paid_cumulative=int(state.get("funding_paid_cumulative", 0)),
        funding_last_applied_epoch=int(state.get("funding_last_applied_epoch", 0)),
        liquidated_this_step=bool(state.get("liquidated_this_step", False)),
    )
    return global_state, acct


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


_SIGNED_FIELD_KEYS: dict[str, tuple[str, ...]] = {
    # Clearinghouse market formation / matched updates (P2P posture).
    "init_market_2p": ("quote_asset", "account_a_pubkey", "account_b_pubkey", "deadline"),
    "init_market_3p": ("quote_asset", "account_a_pubkey", "account_b_pubkey", "account_c_pubkey", "deadline"),
    "set_position_pair": (
        "account_a_pubkey",
        "account_b_pubkey",
        "new_position_base_a",
        "new_position_base_b",
        "deadline",
    ),
    "set_position_triplet": (
        "account_a_pubkey",
        "account_b_pubkey",
        "account_c_pubkey",
        "new_position_base_a",
        "new_position_base_b",
        "new_position_base_c",
        "deadline",
    ),
    # Clearing price publication (oracle-signed by default for clearinghouse markets).
    "publish_clearing_price": ("price_e8", "deadline"),
}


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
    module = op.get("module")
    version = op.get("version")
    market_id = op.get("market_id")
    action = op.get("action")
    if not isinstance(module, str) or not module:
        raise ValueError("signing dict missing module")
    if not isinstance(version, str) or not version:
        raise ValueError("signing dict missing version")
    if not isinstance(market_id, str) or not market_id:
        raise ValueError("signing dict missing market_id")
    if not isinstance(action, str) or not action:
        raise ValueError("signing dict missing action")

    keys = _SIGNED_FIELD_KEYS.get(action)
    if keys is None:
        raise ValueError(f"unsupported signed action: {action}")

    fields: Dict[str, Any] = {}
    for k in keys:
        if k not in op:
            raise ValueError(f"signing dict missing field: {k}")
        fields[k] = op[k]

    return {
        "module": module,
        "version": version,
        "market_id": market_id,
        "action": action,
        "signer_pubkey": str(signer_pubkey),
        "nonce": int(nonce),
        "fields": fields,
    }


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
    if int(block_timestamp) > int(deadline):
        return "signature expired (deadline)"

    # Nonce policy (cheap). We only commit after signature verification, but we
    # validate expected value here to fail quickly.
    expected = int(nonces.get_last(signer_nonce_key)) + 1
    if int(nonce) != expected:
        return "nonce invalid"

    try:
        pubkey_bytes = _hex_to_bytes_allow_0x(signer_pubkey, name="signer_pubkey", expected_nbytes=48)
        sig_bytes = _hex_to_bytes_allow_0x(signature, name="signature", expected_nbytes=96)
    except Exception as exc:
        return str(exc)

    try:
        signing_dict = _perp_op_signing_dict(op, signer_pubkey=signer_pubkey, nonce=int(nonce))
        signing_payload = canonical_json_bytes(signing_dict)
        msg = domain_sep_bytes(f"perp_op_sig:{config.chain_id}", version=1) + signing_payload
        msg_hash = hashlib.sha256(msg).digest()
        ok = bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))  # type: ignore[attr-defined]
    except Exception as exc:
        return f"signature verification error: {_safe_error_str(exc)}"
    if not ok:
        return "invalid signature"

    # Commit nonce consumption after signature verification.
    nonces.set_last(signer_nonce_key, int(nonce))
    return None


@dataclass
class _PerpApplyCtx:
    config: PerpEngineConfig
    balances: BalanceTable
    nonces: NonceTable
    markets: Dict[str, PerpAnyMarketState]
    effects: List[Dict[str, Any]]
    tx_sender_pubkey: str
    block_timestamp: int


def _reject_unknown_fields(data: Mapping[str, Any], allowed: set[str], *, error: str) -> Optional[str]:
    if set(data.keys()) - allowed:
        return error
    return None


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

        oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
        oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)

        allowed = {"module", "version", "market_id", "action", "price_e8", "deadline", "oracle_nonce", "oracle_sig"}
        unknown = _reject_unknown_fields(data, allowed, error="publish_clearing_price has unknown fields")
        if unknown is not None:
            return unknown

        # Cheap validation before signature verification (DoS resistance).
        price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
        if price_e8 <= 0:
            return "publish_clearing_price requires price_e8 > 0"

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
        allowed = {"module", "version", "market_id", "action"}
        unknown = _reject_unknown_fields(data, allowed, error="settle_epoch has unknown fields")
        if unknown is not None:
            return unknown
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
        err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
        if err is not None:
            return err
        allowed = {"module", "version", "market_id", "action", "params"}
        unknown = _reject_unknown_fields(data, allowed, error="set_market_params has unknown fields")
        if unknown is not None:
            return unknown
        if int(ch2p_market.state.get("oracle_last_update_epoch", 0)) != int(ch2p_market.state.get("now_epoch", 0)):
            return "cannot update market params mid-epoch"

        params = data.get("params")
        if not isinstance(params, Mapping):
            return "params must be an object"
        try:
            next_state = _apply_clearinghouse_market_params(ch2p_market.state, params=params, kind="ch2p")
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
        try:
            acct_b = _hex_to_bytes_allow_0x(account_pubkey, name="account_pubkey", expected_nbytes=48)
            sender_b = _hex_to_bytes_allow_0x(tx_sender_pubkey, name="tx_sender_pubkey", expected_nbytes=48)
        except Exception as exc:
            return str(exc)
        if acct_b != sender_b:
            return "account_pubkey must match tx sender"

        role = ch2p_market.role_for_pubkey(account_pubkey)
        if role is None:
            return "unknown account_pubkey for this clearinghouse_2p market"

        amount = _require_int(data.get("amount"), name="amount", non_negative=True)
        # Protocol balances are in quote units; the clearinghouse kernel tracks quote-e8 for exact PnL.
        amount_e8 = int(amount) * _E8_SCALE

        if action == "deposit_collateral":
            if balances.get(tx_sender_pubkey, ch2p_market.quote_asset) < amount:
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
            balances.subtract(tx_sender_pubkey, ch2p_market.quote_asset, amount)
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
            balances.add(tx_sender_pubkey, ch2p_market.quote_asset, amount)

        ctx.markets[market_id] = _ch2p_market_with_state(ch2p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff})
        return None

    if action == "set_position_pair":
        if version not in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
            return "set_position_pair requires perps.version=0.2 or 1.0"

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
        unknown = _reject_unknown_fields(data, allowed, error="set_position_pair has unknown fields")
        if unknown is not None:
            return unknown

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
        if a_b != ma_b or b_b != mb_b:
            return "accounts do not match this market"

        new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
        new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
        if new_b != -new_a:
            return "clearinghouse_2p requires net position == 0"

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

        oracle_nonce = _require_int_u32_pos(data.get("oracle_nonce"), name="oracle_nonce")
        oracle_sig = _require_str(data.get("oracle_sig"), name="oracle_sig", non_empty=True, max_len=4096)

        allowed = {"module", "version", "market_id", "action", "price_e8", "deadline", "oracle_nonce", "oracle_sig"}
        unknown = _reject_unknown_fields(data, allowed, error="publish_clearing_price has unknown fields")
        if unknown is not None:
            return unknown

        # Cheap validation before signature verification (DoS resistance).
        price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
        if price_e8 <= 0:
            return "publish_clearing_price requires price_e8 > 0"

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
        allowed = {"module", "version", "market_id", "action"}
        unknown = _reject_unknown_fields(data, allowed, error="settle_epoch has unknown fields")
        if unknown is not None:
            return unknown
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
        err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
        if err is not None:
            return err
        allowed = {"module", "version", "market_id", "action", "params"}
        unknown = _reject_unknown_fields(data, allowed, error="set_market_params has unknown fields")
        if unknown is not None:
            return unknown
        if int(ch3p_market.state.get("oracle_last_update_epoch", 0)) != int(ch3p_market.state.get("now_epoch", 0)):
            return "cannot update market params mid-epoch"

        params = data.get("params")
        if not isinstance(params, Mapping):
            return "params must be an object"
        try:
            next_state = _apply_clearinghouse_market_params(ch3p_market.state, params=params, kind="ch3p")
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
        try:
            acct_b = _hex_to_bytes_allow_0x(account_pubkey, name="account_pubkey", expected_nbytes=48)
            sender_b = _hex_to_bytes_allow_0x(tx_sender_pubkey, name="tx_sender_pubkey", expected_nbytes=48)
        except Exception as exc:
            return str(exc)
        if acct_b != sender_b:
            return "account_pubkey must match tx sender"

        role = ch3p_market.role_for_pubkey(account_pubkey)
        if role is None:
            return "unknown account_pubkey for this clearinghouse_3p market"

        amount = _require_int(data.get("amount"), name="amount", non_negative=True)
        amount_e8 = int(amount) * _E8_SCALE

        if action == "deposit_collateral":
            if balances.get(tx_sender_pubkey, ch3p_market.quote_asset) < amount:
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
            balances.subtract(tx_sender_pubkey, ch3p_market.quote_asset, amount)
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
            balances.add(tx_sender_pubkey, ch3p_market.quote_asset, amount)

        ctx.markets[market_id] = _ch3p_market_with_state(ch3p_market, state=next_state)
        ctx.effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff})
        return None

    if action == "set_position_triplet":
        if version != PERP_OP_VERSION_CH3P_V1_1:
            return "set_position_triplet requires perps.version=1.1"

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
        unknown = _reject_unknown_fields(data, allowed, error="set_position_triplet has unknown fields")
        if unknown is not None:
            return unknown

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
        if a_b != ma_b or b_b != mb_b or c_b != mc_b:
            return "accounts do not match this market"

        new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
        new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
        new_c = _require_int(data.get("new_position_base_c"), name="new_position_base_c", non_negative=False)
        if new_a + new_b + new_c != 0:
            return "clearinghouse_3p requires net position == 0"
        if not (new_a == 0 or new_b == 0 or new_c == 0):
            return "clearinghouse_3p requires at least one flat position"

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

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action", "delta"}
    unknown = _reject_unknown_fields(data, allowed, error="advance_epoch has unknown fields")
    if unknown is not None:
        return unknown
    if int(market.global_state.get("oracle_last_update_epoch", 0)) != int(market.global_state.get("now_epoch", 0)):
        return "cannot advance epoch before settling current epoch"
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

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action", "price_e8"}
    unknown = _reject_unknown_fields(data, allowed, error="publish_clearing_price has unknown fields")
    if unknown is not None:
        return unknown
    price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
    if price_e8 <= 0:
        return "publish_clearing_price requires price_e8 > 0"

    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="publish_clearing_price",
        params={"price_e8": price_e8},
    )
    if not res.ok or res.state is None:
        return res.error or "publish_clearing_price rejected"
    new_global, new_dummy = _split_kernel_state(res.state)
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

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action"}
    unknown = _reject_unknown_fields(data, allowed, error="apply_funding_auto has unknown fields")
    if unknown is not None:
        return unknown

    now_epoch = int(market.global_state.get("now_epoch", 0))
    if not bool(market.global_state.get("clearing_price_seen", False)):
        return "cannot apply funding before clearing price is published"
    if int(market.global_state.get("clearing_price_epoch", 0)) != now_epoch:
        return "cannot apply funding: clearing price is not for current epoch"
    if int(market.global_state.get("oracle_last_update_epoch", 0)) >= now_epoch:
        return "cannot apply funding after settlement"
    if not bool(market.global_state.get("oracle_seen", False)):
        return "cannot apply funding before oracle is established"

    index_price_e8 = int(market.global_state.get("index_price_e8", 0))
    if index_price_e8 <= 0:
        return "cannot apply funding: index_price_e8 must be positive"
    oracle_last_update_epoch = int(market.global_state.get("oracle_last_update_epoch", 0))
    max_oracle_staleness_epochs = int(market.global_state.get("max_oracle_staleness_epochs", 0))
    if max_oracle_staleness_epochs <= 0:
        return "cannot apply funding: invalid max_oracle_staleness_epochs"
    if not _perp_v2_is_oracle_fresh(
        now_epoch,
        oracle_last_update_epoch,
        max_oracle_staleness_epochs,
        oracle_seen=True,
    ):
        return "cannot apply funding: oracle is stale"

    clearing_price_e8 = int(market.global_state.get("clearing_price_e8", 0))
    if clearing_price_e8 <= 0:
        return "cannot apply funding: clearing_price_e8 must be positive"
    max_oracle_move_bps = int(market.global_state.get("max_oracle_move_bps", 0))
    if max_oracle_move_bps < 0 or max_oracle_move_bps > _BPS_SCALE:
        return "cannot apply funding: invalid max_oracle_move_bps"
    funding_cap_bps = int(market.global_state.get("funding_cap_bps", 0))
    if funding_cap_bps <= 0 or funding_cap_bps > _BPS_SCALE:
        return "cannot apply funding: invalid funding_cap_bps"
    mark_price_e8 = _perp_v2_settle_price(clearing_price_e8, index_price_e8, max_oracle_move_bps, oracle_seen=True)
    new_rate_bps = compute_funding_rate_bps(
        index_price_e8=index_price_e8,
        mark_price_e8=mark_price_e8,
        funding_cap_bps=funding_cap_bps,
    )

    sorted_accounts = tuple(sorted(market.accounts.items()))
    open_accounts = tuple((pk, acct) for pk, acct in sorted_accounts if int(acct.position_base) != 0)

    # Anti-gaming guard:
    # funding updates must remain budget-balanced across all open positions.
    projected_net_funding = 0
    for _, acct in open_accounts:
        projected_net_funding += _perp_v2_funding_payment(acct.position_base, index_price_e8, int(new_rate_bps))
    if projected_net_funding != 0:
        return f"apply_funding_auto would violate funding budget balance (net={projected_net_funding})"

    # Fail-closed: prevent mixed funding states within the epoch (no partial application).
    for _, acct in open_accounts:
        if int(acct.funding_last_applied_epoch) >= now_epoch:
            return "funding already applied this epoch"

    pre_global = dict(market.global_state)
    expected_global = dict(pre_global)
    expected_global["funding_rate_bps"] = int(new_rate_bps)

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
        if post_global != expected_global:
            return "internal error: apply_funding mutated unexpected global fields"
        new_accounts[str(pk)] = post_acct
        applied_accounts += 1

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
            "mark_price_e8": int(mark_price_e8),
            "accounts_applied": int(applied_accounts),
        }
    )
    return None


def _apply_isolated_settle_epoch(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action"}
    unknown = _reject_unknown_fields(data, allowed, error="settle_epoch has unknown fields")
    if unknown is not None:
        return unknown

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

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action"}
    unknown = _reject_unknown_fields(data, allowed, error="clear_breaker has unknown fields")
    if unknown is not None:
        return unknown
    if any(int(acct.position_base) != 0 for acct in market.accounts.values()):
        return "cannot clear breaker while positions are open"

    dummy = _kernel_initial_account_state()
    res = perp_epoch_isolated_default_apply(
        state=market.kernel_state_for_account(dummy),
        action="clear_breaker",
        params={"auth_ok": True},
    )
    if not res.ok or res.state is None:
        return res.error or "clear_breaker rejected"
    new_global, new_dummy = _split_kernel_state(res.state)
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

    err = _require_operator(ctx.config, tx_sender_pubkey=ctx.tx_sender_pubkey)
    if err is not None:
        return err
    allowed = {"module", "version", "market_id", "action", "params"}
    unknown = _reject_unknown_fields(data, allowed, error="set_market_params has unknown fields")
    if unknown is not None:
        return unknown
    if int(market.global_state.get("oracle_last_update_epoch", 0)) != int(market.global_state.get("now_epoch", 0)):
        return "cannot update market params mid-epoch"

    params = data.get("params")
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
    unknown = _reject_unknown_fields(data, allowed, error="deposit_collateral has unknown fields")
    if unknown is not None:
        return unknown

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    if account_pubkey != ctx.tx_sender_pubkey:
        return "account_pubkey must match tx sender"

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
    unknown = _reject_unknown_fields(data, allowed, error="withdraw_collateral has unknown fields")
    if unknown is not None:
        return unknown

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    if account_pubkey != ctx.tx_sender_pubkey:
        return "account_pubkey must match tx sender"

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


def _apply_isolated_set_position(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    action = op.action
    market_id = op.market_id
    data = op.data

    allowed = {"module", "version", "market_id", "action", "account_pubkey", "new_position_base"}
    unknown = _reject_unknown_fields(data, allowed, error="set_position has unknown fields")
    if unknown is not None:
        return unknown

    account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
    if account_pubkey != ctx.tx_sender_pubkey:
        return "account_pubkey must match tx sender"

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


_ISOLATED_ACTION_HANDLERS = {
    "advance_epoch": _apply_isolated_advance_epoch,
    "publish_clearing_price": _apply_isolated_publish_clearing_price,
    "apply_funding_auto": _apply_isolated_apply_funding_auto,
    "settle_epoch": _apply_isolated_settle_epoch,
    "clear_breaker": _apply_isolated_clear_breaker,
    "set_market_params": _apply_isolated_set_market_params,
    "deposit_collateral": _apply_isolated_deposit_collateral,
    "withdraw_collateral": _apply_isolated_withdraw_collateral,
    "set_position": _apply_isolated_set_position,
}


def _apply_isolated_op(ctx: _PerpApplyCtx, *, i: int, op: PerpOp, market: PerpMarketState) -> Optional[str]:
    handler = _ISOLATED_ACTION_HANDLERS.get(op.action)
    if handler is None:
        return f"unknown perps action: {op.action}"
    return handler(ctx, i=i, op=op, market=market)


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
            op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0, PERP_OP_VERSION_CH3P_V1_1) for op in ops
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
        if any(op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0, PERP_OP_VERSION_CH3P_V1_1) for op in ops):
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
                if version not in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
                    return PerpTxResult(ok=False, error="init_market_2p requires perps.version=0.2 or 1.0")
                if market_id in markets:
                    return PerpTxResult(ok=False, error="market already exists")

                quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
                account_a_pubkey = _require_str(
                    data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
                )
                account_b_pubkey = _require_str(
                    data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
                )
                if account_a_pubkey == account_b_pubkey:
                    return PerpTxResult(ok=False, error="accounts must be distinct")

                # Distinctness must be enforced by pubkey bytes (not string representation).
                try:
                    a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
                    b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
                    if a_b == b_b:
                        return PerpTxResult(ok=False, error="accounts must be distinct")
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
                extra = set(data.keys()) - allowed
                if extra:
                    return PerpTxResult(ok=False, error="init_market_2p has unknown fields")

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
                if version != PERP_OP_VERSION_CH3P_V1_1:
                    return PerpTxResult(ok=False, error="init_market_3p requires perps.version=1.1")
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
                if len({account_a_pubkey, account_b_pubkey, account_c_pubkey}) != 3:
                    return PerpTxResult(ok=False, error="accounts must be distinct")

                # Distinctness must be enforced by pubkey bytes (not string representation).
                try:
                    a_b = _hex_to_bytes_allow_0x(account_a_pubkey, name="account_a_pubkey", expected_nbytes=48)
                    b_b = _hex_to_bytes_allow_0x(account_b_pubkey, name="account_b_pubkey", expected_nbytes=48)
                    c_b = _hex_to_bytes_allow_0x(account_c_pubkey, name="account_c_pubkey", expected_nbytes=48)
                    if len({a_b, b_b, c_b}) != 3:
                        return PerpTxResult(ok=False, error="accounts must be distinct")
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
                extra = set(data.keys()) - allowed
                if extra:
                    return PerpTxResult(ok=False, error="init_market_3p has unknown fields")

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

            market_any = markets.get(market_id)
            if market_any is None:
                return PerpTxResult(ok=False, error="unknown market_id")

            is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
            is_ch3p = version == PERP_OP_VERSION_CH3P_V1_1
            if is_ch2p:
                if not isinstance(market_any, PerpClearinghouse2pMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse_2p operation")
                ch2p_market = market_any
            elif is_ch3p:
                if not isinstance(market_any, PerpClearinghouse3pTransferMarketState):
                    return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse_3p operation")
                ch3p_market = market_any
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

            err = _apply_isolated_op(ctx, i=i, op=op, market=market)
            if err is not None:
                return PerpTxResult(ok=False, error=err)
            continue

        next_perps = PerpsState(version=perps_version, markets=markets) if markets else None
        next_state = replace(state, balances=balances, nonces=nonces, perps=next_perps)
        return PerpTxResult(ok=True, state=next_state, effects=effects)

    except Exception as exc:
        return PerpTxResult(ok=False, error=_safe_error_str(exc))
