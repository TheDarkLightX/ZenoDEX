"""
Perpetuals module state (protocol-level, snapshot-friendly).

This file defines the *persistent* perps state that lives inside `DexState` and is
encoded/decoded by `src/integration/dex_snapshot.py`.

The actual risk-engine step logic is implemented separately (see
`src/core/perp_epoch.py` + `src/kernels/dex/perp_epoch_isolated_v2.yaml`).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict


# Kernel value domain (mirrors the YAML spec / generated refs): bool | int | str
Value = bool | int | str


PERPS_STATE_VERSION = 4

# Per `src/kernels/dex/perp_epoch_isolated_v2.yaml` (default posture).
PERP_ACCOUNT_KEYS: set[str] = {
    "position_base",
    "entry_price_e8",
    "collateral_quote",
    "funding_paid_cumulative",
    "funding_last_applied_epoch",
    "liquidated_this_step",
}
PERP_GLOBAL_KEYS: set[str] = {
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

    def __post_init__(self) -> None:
        if not isinstance(self.quote_asset, str) or not self.quote_asset:
            raise TypeError("quote_asset must be a non-empty string")
        if not isinstance(self.global_state, dict):
            raise TypeError("global_state must be a dict")
        if not isinstance(self.accounts, dict):
            raise TypeError("accounts must be a dict")

        # Fail-closed: validate global_state shape and types (no unknown keys).
        keys = set(self.global_state.keys())
        extra = keys - PERP_GLOBAL_KEYS
        missing = PERP_GLOBAL_KEYS - keys
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
class PerpsState:
    """Top-level perps module state (can hold multiple markets)."""

    version: int
    markets: Dict[str, PerpMarketState]

    def __post_init__(self) -> None:
        if not isinstance(self.version, int) or isinstance(self.version, bool) or self.version <= 0:
            raise TypeError("version must be a positive int")
        if self.version != PERPS_STATE_VERSION:
            raise ValueError(f"unsupported perps state version: {self.version}")
        if not isinstance(self.markets, dict):
            raise TypeError("markets must be a dict")

    def get_market(self, market_id: str) -> PerpMarketState | None:
        return self.markets.get(market_id)
