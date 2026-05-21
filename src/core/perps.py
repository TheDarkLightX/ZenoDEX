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
from typing import Dict, Literal

from ..state.canonical import canonical_hex_fixed_allow_0x


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

PERP_MARKET_KIND_ISOLATED_V2: Literal["isolated_v2"] = "isolated_v2"
PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1: Literal["clearinghouse_2p_v1"] = "clearinghouse_2p_v1"
PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1: Literal["clearinghouse_3p_transfer_v1"] = "clearinghouse_3p_transfer_v1"

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


@dataclass(frozen=True)
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


@dataclass(frozen=True)
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
            raise TypeError(f"global_state['epoch_phase'] must be a str or int")
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


@dataclass(frozen=True)
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


@dataclass(frozen=True)
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


PerpAnyMarketState = PerpMarketState | PerpClearinghouse2pMarketState | PerpClearinghouse3pTransferMarketState


@dataclass(frozen=True)
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
