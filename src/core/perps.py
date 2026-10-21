"""
Perpetuals module state (protocol-level, snapshot-friendly).

This file defines the *persistent* perps state that lives inside `DexState` and is
encoded/decoded by `src/integration/dex_snapshot.py`.

The actual risk-engine step logic is implemented separately (see
`src/core/perp_epoch.py` + `src/kernels/dex/perp_epoch_isolated_v3.yaml`).

Units note:
- Isolated markets (`kind="isolated_v2"`) track collateral in *quote units* (`collateral_quote`).
- Clearinghouse markets (`kind="clearinghouse_2p_v1"`) track quote amounts in *quote-e8*
  (`collateral_e8_*`, `fee_pool_e8`, `net_deposited_e8`) so epoch PnL updates are exact integers
  (no division / rounding dust).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Literal, Mapping, Tuple

from ..state.canonical import canonical_hex_fixed_allow_0x
from .perp_apply_funding_auto_gate import (
    MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
    is_derivatives_safe_mark_price_source,
)

# Kernel value domain (mirrors the YAML spec / generated refs): bool | int | str
Value = bool | int | str


PERPS_STATE_VERSION_V4 = 4
PERPS_STATE_VERSION_V5 = 5
PERPS_STATE_VERSION = PERPS_STATE_VERSION_V5


def _pubkey_bytes48(pubkey: str, *, name: str) -> bytes:
    canon = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name=name)
    return bytes.fromhex(canon[2:])


def _pubkey_bytes48_or_none(pubkey: str) -> bytes | None:
    try:
        return _pubkey_bytes48(pubkey, name="pubkey")
    except Exception:
        return None


def _infer_epoch_phase(gs: dict) -> int:
    """Infer epoch_phase from existing global_state fields for legacy snapshots.

    Epoch lifecycle: advance_epoch→Open, publish_clearing_price→PricePublished,
    settle_epoch→Settled. We detect the phase from the side-effects each
    transition leaves:
      - PricePublished: clearing_price_seen=True, clearing_price_epoch==now_epoch
      - Settled: additionally oracle_last_update_epoch==now_epoch, oracle_seen=True
      - Open: otherwise (no clearing price published in the current epoch)
    """
    now = int(gs.get("now_epoch", 0))
    cp_seen = bool(gs.get("clearing_price_seen", False))
    cp_epoch = int(gs.get("clearing_price_epoch", -1))
    o_seen = bool(gs.get("oracle_seen", False))
    o_epoch = int(gs.get("oracle_last_update_epoch", -1))

    # Canonical kernel encoding: Open=0, PricePublished=1, Settled=2.
    if cp_seen and cp_epoch == now:
        if o_seen and o_epoch == now:
            return 2
        return 1
    return 0


_EPOCH_PHASE_STR_TO_INT: dict[str, int] = {"Open": 0, "PricePublished": 1, "Settled": 2}
_EPOCH_PHASE_INT_TO_STR: dict[int, str] = {0: "Open", 1: "PricePublished", 2: "Settled"}
_BPS_SCALE = 10_000


def _funded_liquidation_params_ok(
    *,
    maintenance_margin_bps: int,
    depeg_buffer_bps: int,
    max_oracle_move_bps: int,
    liquidation_penalty_bps: int,
) -> bool:
    effective_maintenance_bps = int(maintenance_margin_bps) + int(depeg_buffer_bps)
    return int(liquidation_penalty_bps) * (
        _BPS_SCALE + int(max_oracle_move_bps)
    ) <= _BPS_SCALE * (effective_maintenance_bps - int(max_oracle_move_bps))

PERP_MARKET_KIND_ISOLATED_V2: Literal["isolated_v2"] = "isolated_v2"
PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1: Literal["clearinghouse_2p_v1"] = "clearinghouse_2p_v1"
PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1: Literal["clearinghouse_3p_transfer_v1"] = "clearinghouse_3p_transfer_v1"
# Open, dynamic-membership N-party net-zero clearinghouse (3+ independent wallets).
# Unlike the fixed-slot 2p/3p kernels this market has no a/b/c slots. It holds a
# dynamic account set and delegates transition semantics to
# `src/core/perp_np_clearinghouse.py`.
PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1: Literal["clearinghouse_np_v1"] = "clearinghouse_np_v1"

# Per `src/kernels/dex/perp_epoch_isolated_v3.yaml` (default posture).
PERP_ACCOUNT_KEYS: set[str] = {
    "position_base",
    "entry_price_e8",
    "collateral_quote",
    "funding_paid_cumulative",
    "funding_last_applied_epoch",
    "liquidated_this_step",
}
PERP_ISOLATED_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "epoch_phase",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "mark_price_source_kind",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_quote",
    "funding_rate_bps",
    "funding_cap_bps",
    "insurance_balance",
    "initial_insurance",
    "fee_income",
    "claims_paid",
    "min_notional_for_bounty",
}

# JSON compatibility: allow legacy 0/1 encodings for bools and normalize them.
_PERP_ISOLATED_GLOBAL_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
}

# Backwards-compatible alias (older modules import PERP_GLOBAL_KEYS).
PERP_GLOBAL_KEYS: set[str] = PERP_ISOLATED_GLOBAL_KEYS

# Per `src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml`.
PERP_CLEARINGHOUSE_2P_STATE_KEYS: set[str] = {
    "now_epoch",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_e8",
    "liquidated_this_step",
    "net_deposited_e8",
    "position_base_a",
    "entry_price_e8_a",
    "collateral_e8_a",
    "position_base_b",
    "entry_price_e8_b",
    "collateral_e8_b",
}

PERP_CLEARINGHOUSE_2P_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
    "liquidated_this_step",
}

PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS: set[str] = {
    "now_epoch",
    "breaker_active",
    "breaker_last_trigger_epoch",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "oracle_seen",
    "oracle_last_update_epoch",
    "index_price_e8",
    "max_oracle_staleness_epochs",
    "max_oracle_move_bps",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "liquidation_penalty_bps",
    "max_position_abs",
    "fee_pool_e8",
    "liquidated_this_step",
    "net_deposited_e8",
    "position_base_a",
    "entry_price_e8_a",
    "collateral_e8_a",
    "position_base_b",
    "entry_price_e8_b",
    "collateral_e8_b",
    "position_base_c",
    "entry_price_e8_c",
    "collateral_e8_c",
}

PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS: set[str] = {
    "breaker_active",
    "clearing_price_seen",
    "oracle_seen",
    "liquidated_this_step",
}


@dataclass(frozen=True, slots=True)
class PerpAccountState:
    """Per-account isolated margin state for the epoch-perp kernel (v2 default)."""

    position_base: int
    entry_price_e8: int
    collateral_quote: int
    funding_paid_cumulative: int
    funding_last_applied_epoch: int
    liquidated_this_step: bool

    def __post_init__(self) -> None:
        if not isinstance(self.position_base, int) or isinstance(self.position_base, bool):
            raise TypeError("position_base must be an int")
        if not isinstance(self.entry_price_e8, int) or isinstance(self.entry_price_e8, bool):
            raise TypeError("entry_price_e8 must be an int")
        if not isinstance(self.collateral_quote, int) or isinstance(self.collateral_quote, bool):
            raise TypeError("collateral_quote must be an int")
        if not isinstance(self.funding_paid_cumulative, int) or isinstance(self.funding_paid_cumulative, bool):
            raise TypeError("funding_paid_cumulative must be an int")
        if not isinstance(self.funding_last_applied_epoch, int) or isinstance(self.funding_last_applied_epoch, bool):
            raise TypeError("funding_last_applied_epoch must be an int")
        if not isinstance(self.liquidated_this_step, bool):
            raise TypeError("liquidated_this_step must be a bool")
        if self.entry_price_e8 < 0:
            raise ValueError("entry_price_e8 must be non-negative")
        if self.collateral_quote < 0:
            raise ValueError("collateral_quote must be non-negative")
        if self.funding_last_applied_epoch < 0:
            raise ValueError("funding_last_applied_epoch must be non-negative")

    def to_kernel_state(self) -> dict[str, Value]:
        return {
            "position_base": int(self.position_base),
            "entry_price_e8": int(self.entry_price_e8),
            "collateral_quote": int(self.collateral_quote),
            "funding_paid_cumulative": int(self.funding_paid_cumulative),
            "funding_last_applied_epoch": int(self.funding_last_applied_epoch),
            "liquidated_this_step": bool(self.liquidated_this_step),
        }


@dataclass(frozen=True, slots=True)
class PerpMarketState:
    """Single-market state: global epoch/oracle + account table."""

    quote_asset: str
    global_state: Dict[str, Value]
    accounts: Dict[str, PerpAccountState]
    kind: Literal["isolated_v2"] = PERP_MARKET_KIND_ISOLATED_V2

    def __post_init__(self) -> None:
        if self.kind != PERP_MARKET_KIND_ISOLATED_V2:
            raise ValueError(f"unsupported perps market kind: {self.kind}")
        if not isinstance(self.quote_asset, str) or not self.quote_asset:
            raise TypeError("quote_asset must be a non-empty string")
        if not isinstance(self.global_state, dict):
            raise TypeError("global_state must be a dict")
        if not isinstance(self.accounts, dict):
            raise TypeError("accounts must be a dict")

        # Fail-closed: validate global_state shape and types (no unknown keys).
        # Backward compat: infer epoch_phase from existing state for legacy snapshots.
        if "epoch_phase" not in self.global_state:
            # frozen=True prevents direct assignment; use dict mutation.
            self.global_state["epoch_phase"] = _infer_epoch_phase(self.global_state)
        if "mark_price_source_kind" not in self.global_state:
            self.global_state["mark_price_source_kind"] = MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
        keys = set(self.global_state.keys())
        extra = keys - PERP_ISOLATED_GLOBAL_KEYS
        missing = PERP_ISOLATED_GLOBAL_KEYS - keys
        if extra:
            raise ValueError(f"global_state has unknown keys: {sorted(extra)[:8]}")
        if missing:
            raise ValueError(f"global_state missing required keys: {sorted(missing)[:8]}")

        # Normalize epoch_phase encoding to the canonical kernel representation:
        # Open=0, PricePublished=1, Settled=2.
        ep = self.global_state.get("epoch_phase")
        if isinstance(ep, str):
            if ep not in _EPOCH_PHASE_STR_TO_INT:
                raise ValueError(f"global_state['epoch_phase'] invalid: {ep!r}")
            self.global_state["epoch_phase"] = _EPOCH_PHASE_STR_TO_INT[ep]
        elif isinstance(ep, int) and not isinstance(ep, bool):
            if ep not in _EPOCH_PHASE_INT_TO_STR:
                raise ValueError(f"global_state['epoch_phase'] int value {ep} out of range [0,2]")
        else:
            raise TypeError("global_state['epoch_phase'] must be a str or int")
        for k, v in list(self.global_state.items()):
            # epoch_phase must be the canonical int encoding (never bool/str after normalization).
            if k == "epoch_phase":
                if not isinstance(v, int) or isinstance(v, bool) or v not in _EPOCH_PHASE_INT_TO_STR:
                    raise ValueError(f"global_state['epoch_phase'] invalid: {v!r}")
                continue

            # Some upstreams historically used 0/1 ints for booleans; normalize.
            if k in _PERP_ISOLATED_GLOBAL_BOOL_KEYS:
                if isinstance(v, bool):
                    continue
                if isinstance(v, int) and not isinstance(v, bool):
                    if v in (0, 1):
                        self.global_state[k] = bool(v)
                        continue
                raise TypeError(f"global_state[{k!r}] must be a bool (or 0/1 int)")

            if isinstance(v, int) and not isinstance(v, bool):
                continue
            raise TypeError(f"global_state[{k!r}] must be an int")

        self._validate_isolated_state_consistency()

    def _validate_isolated_state_consistency(self) -> None:
        """Validate consensus-critical invariants on the persistent isolated-market state.

        This prevents malformed snapshots from bypassing phase gates or corrupting
        derived accounting.
        """
        gs = self.global_state

        now_epoch = int(gs["now_epoch"])
        epoch_phase = int(gs["epoch_phase"])
        epoch_phase_str = _EPOCH_PHASE_INT_TO_STR.get(epoch_phase, str(epoch_phase))

        breaker_active = bool(gs["breaker_active"])
        breaker_last_trigger_epoch = int(gs["breaker_last_trigger_epoch"])

        clearing_price_seen = bool(gs["clearing_price_seen"])
        clearing_price_epoch = int(gs["clearing_price_epoch"])
        clearing_price_e8 = int(gs["clearing_price_e8"])
        mark_price_source_kind = int(gs["mark_price_source_kind"])

        oracle_seen = bool(gs["oracle_seen"])
        oracle_last_update_epoch = int(gs["oracle_last_update_epoch"])
        index_price_e8 = int(gs["index_price_e8"])

        max_oracle_move_bps = int(gs["max_oracle_move_bps"])
        initial_margin_bps = int(gs["initial_margin_bps"])
        maintenance_margin_bps = int(gs["maintenance_margin_bps"])
        depeg_buffer_bps = int(gs["depeg_buffer_bps"])
        liquidation_penalty_bps = int(gs["liquidation_penalty_bps"])

        fee_pool_quote = int(gs["fee_pool_quote"])
        funding_rate_bps = int(gs["funding_rate_bps"])
        funding_cap_bps = int(gs["funding_cap_bps"])

        insurance_balance = int(gs["insurance_balance"])
        initial_insurance = int(gs["initial_insurance"])
        fee_income = int(gs["fee_income"])
        claims_paid = int(gs["claims_paid"])

        # Basic temporal sanity: "from future" fields are invalid.
        if breaker_last_trigger_epoch > now_epoch:
            raise ValueError("breaker_last_trigger_epoch must be <= now_epoch")
        if clearing_price_epoch > now_epoch:
            raise ValueError("clearing_price_epoch must be <= now_epoch")
        if oracle_last_update_epoch > now_epoch:
            raise ValueError("oracle_last_update_epoch must be <= now_epoch")

        # Zeroing invariants (fail-closed on partial fields).
        if not breaker_active and breaker_last_trigger_epoch != 0:
            raise ValueError("breaker_last_trigger_epoch must be 0 when breaker_active is false")
        if not clearing_price_seen and (clearing_price_epoch != 0 or clearing_price_e8 != 0):
            raise ValueError("clearing_price fields must be 0 when clearing_price_seen is false")
        if clearing_price_seen and not is_derivatives_safe_mark_price_source(mark_price_source_kind):
            raise ValueError("mark_price_source_kind must be derivatives-safe when clearing_price_seen is true")
        if not oracle_seen and (oracle_last_update_epoch != 0 or index_price_e8 != 0):
            raise ValueError("oracle fields must be 0 when oracle_seen is false")
        if oracle_seen and index_price_e8 <= 0:
            raise ValueError("index_price_e8 must be positive when oracle_seen is true")

        # Parameter ordering invariants.
        eff_maint = maintenance_margin_bps + depeg_buffer_bps
        if not (max_oracle_move_bps <= eff_maint <= initial_margin_bps):
            raise ValueError("invalid margin params ordering (max_move <= maint+depeg <= initial)")
        if liquidation_penalty_bps >= eff_maint:
            raise ValueError("invalid liquidation_penalty_bps (must be < maintenance_margin_bps + depeg_buffer_bps)")
        if not _funded_liquidation_params_ok(
            maintenance_margin_bps=maintenance_margin_bps,
            depeg_buffer_bps=depeg_buffer_bps,
            max_oracle_move_bps=max_oracle_move_bps,
            liquidation_penalty_bps=liquidation_penalty_bps,
        ):
            raise ValueError(
                "invalid liquidation params (require funded liquidation after max_oracle_move_bps)"
            )

        # Funding bounds + gate.
        if abs(funding_rate_bps) > funding_cap_bps:
            raise ValueError("funding_rate_bps must be within [-funding_cap_bps, funding_cap_bps]")

        # Insurance accounting + nonneg.
        if insurance_balance < 0:
            raise ValueError("insurance_balance must be non-negative")
        if insurance_balance != initial_insurance + fee_income - claims_paid:
            raise ValueError("insurance_balance must equal initial_insurance + fee_income - claims_paid")

        # Fee pool accounting identity.
        if fee_pool_quote != fee_income:
            raise ValueError("fee_pool_quote must equal fee_income")

        # Epoch phase consistency (prevents bypassing phase gating via malformed snapshots).
        if epoch_phase == 0:
            if clearing_price_seen and clearing_price_epoch == now_epoch:
                raise ValueError("epoch_phase Open inconsistent with clearing_price for current epoch")
            if now_epoch > 0 and oracle_seen and oracle_last_update_epoch == now_epoch:
                raise ValueError("epoch_phase Open inconsistent with oracle_last_update_epoch == now_epoch")
        elif epoch_phase == 1:
            if not (clearing_price_seen and clearing_price_epoch == now_epoch):
                raise ValueError("epoch_phase PricePublished requires clearing_price for current epoch")
            if oracle_seen and oracle_last_update_epoch == now_epoch:
                raise ValueError("epoch_phase PricePublished requires oracle_last_update_epoch < now_epoch")
        elif epoch_phase == 2:
            if not (clearing_price_seen and clearing_price_epoch == now_epoch):
                raise ValueError("epoch_phase Settled requires clearing_price for current epoch")
            if not (oracle_seen and oracle_last_update_epoch == now_epoch):
                raise ValueError("epoch_phase Settled requires oracle_last_update_epoch == now_epoch")
        else:  # pragma: no cover - guarded earlier
            raise ValueError(f"invalid epoch_phase: {epoch_phase_str!r}")

        # Account-level invariants that are cheap to enforce at snapshot boundaries.
        for pk, acct in self.accounts.items():
            if not isinstance(pk, str) or not pk:
                raise TypeError("accounts keys must be non-empty strings")
            pos = int(acct.position_base)
            entry = int(acct.entry_price_e8)
            if int(acct.funding_last_applied_epoch) > now_epoch:
                raise ValueError("account funding_last_applied_epoch must be <= now_epoch")
            if pos == 0 and entry != 0:
                raise ValueError("entry_price_e8 must be 0 when position_base is 0")
            if pos != 0 and entry != index_price_e8:
                raise ValueError("entry_price_e8 must equal index_price_e8 when position_base is non-zero")

    def kernel_state_for_account(self, account: PerpAccountState) -> dict[str, Value]:
        # Merge global + account state into a single kernel state dict.
        return {**dict(self.global_state), **account.to_kernel_state()}


# Settable margin/control param bounds for the 2p/3p clearinghouse kernels. These
# mirror perp_engine._CLEARINGHOUSE_CONTROL_PARAM_BOUNDS (the engine validates them at
# set-time); a drift-guard test pins equality. The snapshot validators below check both
# the RANGES and the margin-tier ORDERING so a forged/corrupt snapshot fails closed at
# the boundary rather than reaching settlement math. The ordering mirrors the kernel
# ref model's `inv_margin_params_ordered` invariant (max_oracle_move <= maintenance <=
# initial; the 2p/3p kernels have no depeg buffer), which the engine enforces at
# set-time via `_ch2p/_ch3p_state_from_dict` -- so this rejects only already-invalid
# snapshots, never an engine-accepted config.
PERP_CLEARINGHOUSE_PARAM_BOUNDS: Dict[str, Tuple[int, int]] = {
    "max_oracle_staleness_epochs": (1, 1_000_000),
    "max_oracle_move_bps": (0, 10_000),
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_position_abs": (1, 1_000_000),
}


def _check_clearinghouse_params(state: Mapping[str, Any]) -> None:
    """Fail-closed range + margin-ordering check for the clearinghouse control params
    (forged-snapshot hardening). Run only after the state's keys + int types are
    validated. Mirrors the kernel ref model: per-key ranges and `inv_margin_params_
    ordered` (max_oracle_move <= maintenance <= initial)."""
    for key, (lo, hi) in PERP_CLEARINGHOUSE_PARAM_BOUNDS.items():
        value = int(state[key])
        if value < lo or value > hi:
            raise ValueError(f"state[{key!r}] out of range: {value} not in [{lo}, {hi}]")
    max_move = int(state["max_oracle_move_bps"])
    maint = int(state["maintenance_margin_bps"])
    initial = int(state["initial_margin_bps"])
    if not (max_move <= maint <= initial):
        raise ValueError(
            "clearinghouse invalid margin params ordering "
            "(max_oracle_move_bps <= maintenance_margin_bps <= initial_margin_bps)")


@dataclass(frozen=True, slots=True)
class PerpClearinghouse2pMarketState:
    """Two-party clearinghouse market state (spec-driven kernel state).

    The clearinghouse kernel does not store pubkeys; we bind two pubkeys to its
    A/B account roles at the protocol layer.

    All quote amounts inside `state` are quote-e8 integers. This keeps settlement
    exact and makes the closed-system invariant checkable:
      net_deposited_e8 = collateral_e8_a + collateral_e8_b + fee_pool_e8.
    """

    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    state: Dict[str, Value]
    kind: Literal["clearinghouse_2p_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1

    def __post_init__(self) -> None:
        if self.kind != PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1:
            raise ValueError(f"unsupported perps market kind: {self.kind}")
        if not isinstance(self.quote_asset, str) or not self.quote_asset:
            raise TypeError("quote_asset must be a non-empty string")
        if not isinstance(self.account_a_pubkey, str) or not self.account_a_pubkey:
            raise TypeError("account_a_pubkey must be a non-empty string")
        if not isinstance(self.account_b_pubkey, str) or not self.account_b_pubkey:
            raise TypeError("account_b_pubkey must be a non-empty string")
        a_b = _pubkey_bytes48(self.account_a_pubkey, name="account_a_pubkey")
        b_b = _pubkey_bytes48(self.account_b_pubkey, name="account_b_pubkey")
        if a_b == b_b:
            raise ValueError("clearinghouse accounts must be distinct")
        if not isinstance(self.state, dict):
            raise TypeError("state must be a dict")

        keys = set(self.state.keys())
        extra = keys - PERP_CLEARINGHOUSE_2P_STATE_KEYS
        missing = PERP_CLEARINGHOUSE_2P_STATE_KEYS - keys
        if extra:
            raise ValueError(f"state has unknown keys: {sorted(extra)[:8]}")
        if missing:
            raise ValueError(f"state missing required keys: {sorted(missing)[:8]}")
        for k, v in self.state.items():
            if k in PERP_CLEARINGHOUSE_2P_BOOL_KEYS:
                if not isinstance(v, bool):
                    raise TypeError(f"state[{k!r}] must be a bool")
                continue
            if isinstance(v, int) and not isinstance(v, bool):
                continue
            raise TypeError(f"state[{k!r}] must be an int")

        _check_clearinghouse_params(self.state)

        # Critical clearinghouse invariants (fail-closed on invalid snapshots):
        # - net exposure is structurally zero for the two-party market
        # - total quote-e8 is conserved across the two accounts + fee pool
        pos_a = int(self.state["position_base_a"])
        pos_b = int(self.state["position_base_b"])
        if pos_a + pos_b != 0:
            raise ValueError("clearinghouse state must satisfy position_base_a + position_base_b == 0")

        coll_a = int(self.state["collateral_e8_a"])
        coll_b = int(self.state["collateral_e8_b"])
        fee_pool = int(self.state["fee_pool_e8"])
        net_deposited = int(self.state["net_deposited_e8"])
        if net_deposited != coll_a + coll_b + fee_pool:
            raise ValueError(
                "clearinghouse state must satisfy "
                "net_deposited_e8 == collateral_e8_a + collateral_e8_b + fee_pool_e8"
            )

    def role_for_pubkey(self, pubkey: str) -> Literal["a", "b"] | None:
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        if pb == _pubkey_bytes48_or_none(self.account_a_pubkey):
            return "a"
        if pb == _pubkey_bytes48_or_none(self.account_b_pubkey):
            return "b"
        return None


@dataclass(frozen=True, slots=True)
class PerpClearinghouse3pTransferMarketState:
    """Three-party transfer clearinghouse market state (spec-driven kernel state).

    A/B are the active matched pair, and C is a standby account that can take over a distressed
    position if it meets initial margin.

    All quote amounts inside `state` are quote-e8 integers. This keeps settlement exact and makes
    the closed-system invariant checkable:
      net_deposited_e8 = collateral_e8_a + collateral_e8_b + collateral_e8_c + fee_pool_e8.
    """

    quote_asset: str
    account_a_pubkey: str
    account_b_pubkey: str
    account_c_pubkey: str
    state: Dict[str, Value]
    kind: Literal["clearinghouse_3p_transfer_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1

    def __post_init__(self) -> None:
        if self.kind != PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1:
            raise ValueError(f"unsupported perps market kind: {self.kind}")
        if not isinstance(self.quote_asset, str) or not self.quote_asset:
            raise TypeError("quote_asset must be a non-empty string")
        if not isinstance(self.account_a_pubkey, str) or not self.account_a_pubkey:
            raise TypeError("account_a_pubkey must be a non-empty string")
        if not isinstance(self.account_b_pubkey, str) or not self.account_b_pubkey:
            raise TypeError("account_b_pubkey must be a non-empty string")
        if not isinstance(self.account_c_pubkey, str) or not self.account_c_pubkey:
            raise TypeError("account_c_pubkey must be a non-empty string")
        a_b = _pubkey_bytes48(self.account_a_pubkey, name="account_a_pubkey")
        b_b = _pubkey_bytes48(self.account_b_pubkey, name="account_b_pubkey")
        c_b = _pubkey_bytes48(self.account_c_pubkey, name="account_c_pubkey")
        if len({a_b, b_b, c_b}) != 3:
            raise ValueError("clearinghouse accounts must be distinct")
        if not isinstance(self.state, dict):
            raise TypeError("state must be a dict")

        keys = set(self.state.keys())
        extra = keys - PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS
        missing = PERP_CLEARINGHOUSE_3P_TRANSFER_STATE_KEYS - keys
        if extra:
            raise ValueError(f"state has unknown keys: {sorted(extra)[:8]}")
        if missing:
            raise ValueError(f"state missing required keys: {sorted(missing)[:8]}")
        for k, v in self.state.items():
            if k in PERP_CLEARINGHOUSE_3P_TRANSFER_BOOL_KEYS:
                if not isinstance(v, bool):
                    raise TypeError(f"state[{k!r}] must be a bool")
                continue
            if isinstance(v, int) and not isinstance(v, bool):
                continue
            raise TypeError(f"state[{k!r}] must be an int")

        _check_clearinghouse_params(self.state)

        # Critical clearinghouse invariants (fail-closed on invalid snapshots):
        # - net exposure is structurally zero across the three accounts
        # - at least one account is flat (prevents 3-way open exposure)
        # - total quote-e8 is conserved across the three accounts + fee pool
        pos_a = int(self.state["position_base_a"])
        pos_b = int(self.state["position_base_b"])
        pos_c = int(self.state["position_base_c"])
        if pos_a + pos_b + pos_c != 0:
            raise ValueError("clearinghouse state must satisfy position_base_a + position_base_b + position_base_c == 0")
        if not (pos_a == 0 or pos_b == 0 or pos_c == 0):
            raise ValueError("clearinghouse state must satisfy at least one flat position")

        coll_a = int(self.state["collateral_e8_a"])
        coll_b = int(self.state["collateral_e8_b"])
        coll_c = int(self.state["collateral_e8_c"])
        fee_pool = int(self.state["fee_pool_e8"])
        net_deposited = int(self.state["net_deposited_e8"])
        if net_deposited != coll_a + coll_b + coll_c + fee_pool:
            raise ValueError(
                "clearinghouse state must satisfy "
                "net_deposited_e8 == collateral_e8_a + collateral_e8_b + collateral_e8_c + fee_pool_e8"
            )

    def role_for_pubkey(self, pubkey: str) -> Literal["a", "b", "c"] | None:
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        if pb == _pubkey_bytes48_or_none(self.account_a_pubkey):
            return "a"
        if pb == _pubkey_bytes48_or_none(self.account_b_pubkey):
            return "b"
        if pb == _pubkey_bytes48_or_none(self.account_c_pubkey):
            return "c"
        return None


# --- N-party net-zero clearinghouse (dynamic membership) ---------------------
# Global market state for the N-party market. Quote amounts are quote-e8
# integers, mirroring the 2p/3p convention. Params are flattened so the pure core
# can rehydrate MarketParams deterministically.
PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "index_price_e8",
    "clearing_price_seen",
    "clearing_price_epoch",
    "clearing_price_e8",
    "fee_pool_e8",
    "insurance_e8",
    "insurance_ext_e8",
    "claims_paid_e8",
    "net_deposited_e8",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
}

_PERP_CLEARINGHOUSE_NP_GLOBAL_DEFAULTS: dict[str, int] = {
    "clearing_price_seen": 0,
    "clearing_price_epoch": 0,
    "clearing_price_e8": 0,
}

_PERP_CLEARINGHOUSE_NP_NONNEGATIVE_GLOBAL_KEYS: set[str] = {
    "now_epoch",
    "clearing_price_epoch",
    "clearing_price_e8",
    "fee_pool_e8",
    "insurance_e8",
    "insurance_ext_e8",
    "claims_paid_e8",
    "initial_margin_bps",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "max_oracle_move_bps",
    "funding_cap_bps",
    "max_position_abs",
    "min_notional_for_bounty_e8",
}

_PERP_CLEARINGHOUSE_NP_PARAM_BOUNDS: dict[str, tuple[int, int]] = {
    "initial_margin_bps": (0, 10_000),
    "maintenance_margin_bps": (0, 10_000),
    "depeg_buffer_bps": (0, 5_000),
    "liquidation_penalty_bps": (0, 10_000),
    "max_oracle_move_bps": (0, 10_000),
    "funding_cap_bps": (1, 10_000),
    "max_position_abs": (1, 1_000_000),
    "min_notional_for_bounty_e8": (0, 1_000_000_000_000 * 100_000_000),
}

PERP_CLEARINGHOUSE_NP_ACCOUNT_KEYS: set[str] = {
    "pubkey",
    "position_base",
    "entry_price_e8",
    "collateral_e8",
    "funding_paid_cum_e8",
    "nonce",
}


@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpAccount:
    """One participant in an N-party clearinghouse market."""

    pubkey: str
    position_base: int = 0
    entry_price_e8: int = 0
    collateral_e8: int = 0
    funding_paid_cum_e8: int = 0
    nonce: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.pubkey, str) or not self.pubkey:
            raise TypeError("account pubkey must be a non-empty string")
        _pubkey_bytes48(self.pubkey, name="account pubkey")
        for field_name in (
            "position_base",
            "entry_price_e8",
            "collateral_e8",
            "funding_paid_cum_e8",
            "nonce",
        ):
            value = getattr(self, field_name)
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError(f"account {field_name} must be an int")
        if self.entry_price_e8 < 0:
            raise ValueError("account entry_price_e8 must be non-negative")
        if self.collateral_e8 < 0:
            raise ValueError("account collateral_e8 must be non-negative")
        if self.nonce < 0:
            raise ValueError("account nonce must be non-negative")


PERP_CLEARINGHOUSE_NP_PENDING_INTENT_KEYS: set[str] = {
    "pubkey",
    "target_base",
    "limit_price_e8",
    "min_fill_base",
    "expiry_epoch",
    "nonce",
}


@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpPendingIntent:
    """A single-signed position intent queued for the next batch match."""

    pubkey: str
    target_base: int
    nonce: int
    limit_price_e8: int = 0
    min_fill_base: int = 0
    expiry_epoch: int = 1 << 62

    def __post_init__(self) -> None:
        if not isinstance(self.pubkey, str) or not self.pubkey:
            raise TypeError("pending intent pubkey must be a non-empty string")
        _pubkey_bytes48(self.pubkey, name="pending intent pubkey")
        for field_name in ("target_base", "nonce", "limit_price_e8", "min_fill_base", "expiry_epoch"):
            value = getattr(self, field_name)
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError(f"pending intent {field_name} must be an int")
        if self.nonce <= 0:
            raise ValueError("pending intent nonce must be positive")
        if self.limit_price_e8 < 0:
            raise ValueError("pending intent limit_price_e8 must be non-negative")
        if self.min_fill_base < 0:
            raise ValueError("pending intent min_fill_base must be non-negative")
        if self.expiry_epoch < 0:
            raise ValueError("pending intent expiry_epoch must be non-negative")


@dataclass(frozen=True, slots=True)
class PerpClearinghouseNpMarketState:
    """Open N-party net-zero clearinghouse market state."""

    quote_asset: str
    global_state: Dict[str, int]
    accounts: tuple[PerpClearinghouseNpAccount, ...] = ()
    pending_intents: tuple[PerpClearinghouseNpPendingIntent, ...] = ()
    kind: Literal["clearinghouse_np_v1"] = PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1

    def __post_init__(self) -> None:
        if self.kind != PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1:
            raise ValueError(f"unsupported perps market kind: {self.kind}")
        if not isinstance(self.quote_asset, str) or not self.quote_asset:
            raise TypeError("quote_asset must be a non-empty string")
        if not isinstance(self.global_state, dict):
            raise TypeError("global_state must be a dict")
        for k, v in _PERP_CLEARINGHOUSE_NP_GLOBAL_DEFAULTS.items():
            self.global_state.setdefault(k, v)
        keys = set(self.global_state.keys())
        extra = keys - PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS
        missing = PERP_CLEARINGHOUSE_NP_GLOBAL_KEYS - keys
        if extra:
            raise ValueError(f"global_state has unknown keys: {sorted(extra)[:8]}")
        if missing:
            raise ValueError(f"global_state missing required keys: {sorted(missing)[:8]}")
        for k, v in self.global_state.items():
            if not isinstance(v, int) or isinstance(v, bool):
                raise TypeError(f"global_state[{k!r}] must be an int")
        for k in _PERP_CLEARINGHOUSE_NP_NONNEGATIVE_GLOBAL_KEYS:
            if int(self.global_state[k]) < 0:
                raise ValueError(f"global_state[{k!r}] must be non-negative")
        for k, (lo, hi) in _PERP_CLEARINGHOUSE_NP_PARAM_BOUNDS.items():
            value = int(self.global_state[k])
            if value < lo or value > hi:
                raise ValueError(f"global_state[{k!r}] out of range: {value} not in [{lo}, {hi}]")

        # Parameter ordering invariants (mirror the isolated_v2 market). The per-key
        # range bounds above do NOT constrain the RELATIONSHIP between the margin
        # tiers. This ordering is load-bearing: because a clamped oracle move can
        # never exceed the maintenance buffer (max_oracle_move <= maint+depeg), the
        # settlement's liquidation step always catches an account while its
        # collateral is still non-negative, so single-epoch bad debt is unreachable
        # on the valid-param transition path (the insurance-draw / winner-haircut
        # ADL branch is defense-in-depth). Fail-closed here rather than relying on
        # that downstream branch -- and reject forged/corrupt snapshots at the
        # boundary.
        eff_maint = (int(self.global_state["maintenance_margin_bps"])
                     + int(self.global_state["depeg_buffer_bps"]))
        if not (int(self.global_state["max_oracle_move_bps"])
                <= eff_maint <= int(self.global_state["initial_margin_bps"])):
            raise ValueError(
                "clearinghouse_np invalid margin params ordering "
                "(max_oracle_move_bps <= maintenance+depeg <= initial_margin_bps)")
        if int(self.global_state["liquidation_penalty_bps"]) >= eff_maint:
            raise ValueError(
                "clearinghouse_np invalid liquidation_penalty_bps "
                "(must be < maintenance_margin_bps + depeg_buffer_bps)")
        if not _funded_liquidation_params_ok(
            maintenance_margin_bps=int(self.global_state["maintenance_margin_bps"]),
            depeg_buffer_bps=int(self.global_state["depeg_buffer_bps"]),
            max_oracle_move_bps=int(self.global_state["max_oracle_move_bps"]),
            liquidation_penalty_bps=int(self.global_state["liquidation_penalty_bps"]),
        ):
            raise ValueError(
                "clearinghouse_np invalid liquidation params "
                "(require funded liquidation after max_oracle_move_bps)")

        if not isinstance(self.accounts, tuple):
            raise TypeError("accounts must be a tuple")
        for acct in self.accounts:
            if not isinstance(acct, PerpClearinghouseNpAccount):
                raise TypeError("accounts must be PerpClearinghouseNpAccount instances")
        pubkey_bytes = [_pubkey_bytes48(a.pubkey, name="account pubkey") for a in self.accounts]
        if len(set(pubkey_bytes)) != len(pubkey_bytes):
            raise ValueError("clearinghouse_np accounts must be distinct")

        if not isinstance(self.pending_intents, tuple):
            raise TypeError("pending_intents must be a tuple")
        member_bytes = set(pubkey_bytes)
        intent_bytes: list[bytes] = []
        for intent in self.pending_intents:
            if not isinstance(intent, PerpClearinghouseNpPendingIntent):
                raise TypeError("pending_intents must be PerpClearinghouseNpPendingIntent instances")
            ib = _pubkey_bytes48(intent.pubkey, name="pending intent pubkey")
            if ib not in member_bytes:
                raise ValueError("pending intent pubkey is not a market member")
            intent_bytes.append(ib)
        if len(set(intent_bytes)) != len(intent_bytes):
            raise ValueError("clearinghouse_np pending intents must be one-per-account")

        if int(self.global_state["index_price_e8"]) <= 0:
            raise ValueError("index_price_e8 must be positive")

        clearing_price_seen = int(self.global_state["clearing_price_seen"])
        clearing_price_epoch = int(self.global_state["clearing_price_epoch"])
        clearing_price_e8 = int(self.global_state["clearing_price_e8"])
        now_epoch = int(self.global_state["now_epoch"])
        if clearing_price_seen not in (0, 1):
            raise ValueError("clearinghouse_np clearing_price_seen must be 0 or 1")
        if clearing_price_seen == 0:
            if clearing_price_epoch != 0 or clearing_price_e8 != 0:
                raise ValueError("clearinghouse_np clearing_price fields must be 0 when not seen")
        else:
            if clearing_price_e8 <= 0:
                raise ValueError("clearinghouse_np clearing_price_e8 must be positive when seen")
            if clearing_price_epoch != now_epoch:
                raise ValueError("clearinghouse_np clearing_price_epoch must equal now_epoch when seen")

        if sum(a.position_base for a in self.accounts) != 0:
            raise ValueError("clearinghouse_np state must satisfy sum(position_base) == 0")

        total_coll = sum(a.collateral_e8 for a in self.accounts)
        gs = self.global_state
        lhs = int(gs["net_deposited_e8"]) + int(gs["insurance_ext_e8"])
        rhs = total_coll + int(gs["fee_pool_e8"]) + int(gs["insurance_e8"])
        if lhs != rhs:
            raise ValueError(
                "clearinghouse_np state must satisfy net_deposited_e8 + insurance_ext_e8 "
                "== sum(collateral_e8) + fee_pool_e8 + insurance_e8"
            )

        if int(gs["insurance_e8"]) != int(gs["insurance_ext_e8"]) - int(gs["claims_paid_e8"]):
            raise ValueError("clearinghouse_np state must satisfy insurance_e8 == insurance_ext_e8 - claims_paid_e8")
        if int(gs["insurance_e8"]) < 0:
            raise ValueError("clearinghouse_np insurance_e8 must be non-negative")
        if int(gs["fee_pool_e8"]) < 0:
            raise ValueError("clearinghouse_np fee_pool_e8 must be non-negative")

    def by_pubkey(self) -> dict[str, PerpClearinghouseNpAccount]:
        return {a.pubkey: a for a in self.accounts}

    def role_for_pubkey(self, pubkey: str) -> str | None:
        """Return the participant's own pubkey if it is a member."""
        pb = _pubkey_bytes48_or_none(pubkey)
        if pb is None:
            return None
        for account in self.accounts:
            if pb == _pubkey_bytes48_or_none(account.pubkey):
                return account.pubkey
        return None


PerpAnyMarketState = (
    PerpMarketState
    | PerpClearinghouse2pMarketState
    | PerpClearinghouse3pTransferMarketState
    | PerpClearinghouseNpMarketState
)


@dataclass(frozen=True, slots=True)
class PerpsState:
    """Top-level perps module state (can hold multiple markets)."""

    version: int
    markets: Dict[str, PerpAnyMarketState]

    def __post_init__(self) -> None:
        if not isinstance(self.version, int) or isinstance(self.version, bool) or self.version <= 0:
            raise TypeError("version must be a positive int")
        if self.version not in (PERPS_STATE_VERSION_V4, PERPS_STATE_VERSION_V5):
            raise ValueError(f"unsupported perps state version: {self.version}")
        if not isinstance(self.markets, dict):
            raise TypeError("markets must be a dict")
        if self.version == PERPS_STATE_VERSION_V4:
            for market_id, market in self.markets.items():
                if not isinstance(market_id, str):
                    raise TypeError("markets keys must be strings")
                if not isinstance(market, PerpMarketState):
                    raise TypeError("perps v4 supports isolated markets only")

    def get_market(self, market_id: str) -> PerpAnyMarketState | None:
        return self.markets.get(market_id)
