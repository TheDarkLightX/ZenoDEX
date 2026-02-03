"""
Perpetuals module state (protocol-level, snapshot-friendly).

This file defines the *persistent* perps state that lives inside `DexState` and is
encoded/decoded by `src/integration/dex_snapshot.py`.

The actual risk-engine step logic is implemented separately (see
`src/core/perp_epoch.py` + `src/kernels/dex/perp_epoch_isolated_v2.yaml`).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Literal


# Kernel value domain (mirrors the YAML spec / generated refs): bool | int | str
Value = bool | int | str


PERPS_STATE_VERSION_V4 = 4
PERPS_STATE_VERSION_V5 = 5
PERPS_STATE_VERSION = PERPS_STATE_VERSION_V5

PERP_MARKET_KIND_ISOLATED_V2: Literal["isolated_v2"] = "isolated_v2"
PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1: Literal["clearinghouse_2p_v1"] = "clearinghouse_2p_v1"

# Per `src/kernels/dex/perp_epoch_isolated_v2.yaml` (default posture).
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
        keys = set(self.global_state.keys())
        extra = keys - PERP_ISOLATED_GLOBAL_KEYS
        missing = PERP_ISOLATED_GLOBAL_KEYS - keys
        if extra:
            raise ValueError(f"global_state has unknown keys: {sorted(extra)[:8]}")
        if missing:
            raise ValueError(f"global_state missing required keys: {sorted(missing)[:8]}")
        for k, v in self.global_state.items():
            if isinstance(v, bool):
                continue
            if isinstance(v, int) and not isinstance(v, bool):
                continue
            raise TypeError(f"global_state[{k!r}] must be bool|int")

    def kernel_state_for_account(self, account: PerpAccountState) -> dict[str, Value]:
        # Merge global + account state into a single kernel state dict.
        return {**dict(self.global_state), **account.to_kernel_state()}


@dataclass(frozen=True)
class PerpClearinghouse2pMarketState:
    """Two-party clearinghouse market state (spec-driven kernel state).

    The clearinghouse kernel does not store pubkeys; we bind two pubkeys to its
    A/B account roles at the protocol layer.
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
        if self.account_a_pubkey == self.account_b_pubkey:
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
            if isinstance(v, bool):
                continue
            if isinstance(v, int) and not isinstance(v, bool):
                continue
            raise TypeError(f"state[{k!r}] must be bool|int")

    def role_for_pubkey(self, pubkey: str) -> Literal["a", "b"] | None:
        if pubkey == self.account_a_pubkey:
            return "a"
        if pubkey == self.account_b_pubkey:
            return "b"
        return None


PerpAnyMarketState = PerpMarketState | PerpClearinghouse2pMarketState


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
