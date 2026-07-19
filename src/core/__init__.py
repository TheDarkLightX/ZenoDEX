"""
Core DEX algorithms
"""

from .batch_clearing import (
    apply_settlement,
    apply_settlement_pure,
    compute_settlement,
    validate_settlement,
)
from .cpmm import (
    compute_lp_burn,
    compute_lp_mint,
    swap_exact_in,
    swap_exact_out,
)
from .dex import DexConfig, DexEffects, DexState, DexStepResult
from .dex import step as dex_step
from .epoch_oracle_commitment import (
    EpochOracleCommitment,
    ModuleOracleView,
    OracleRegistry,
    create_module_views,
    estimate_cross_module_arbitrage_bps,
)
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .liquidity import (
    add_liquidity,
    create_pool,
    remove_liquidity,
)
from .oracle import OracleState, init_oracle_state, is_fresh, update_price_timestamp
from .price_impact_preview import (
    PriceImpactPreview,
    compute_isolated_output,
    compute_price_impact_bps,
    compute_spot_price_e8,
    price_impact_preview,
)
from .settlement import Fill, FillAction, Settlement
from .settlement_strong_validator import validate_settlement_strong
from .vault import VaultCommand, VaultState, VaultStepResult, init_vault_state
from .vault import step as vault_step
from .zusd import (
    ZUSDCommand,
    ZUSDState,
    ZUSDStepResult,
)
from .zusd import (
    init_state as init_zusd_state,
)
from .zusd import (
    step as zusd_step,
)

__all__ = [
    "swap_exact_in",
    "swap_exact_out",
    "compute_lp_mint",
    "compute_lp_burn",
    "compute_settlement",
    "validate_settlement",
    "validate_settlement_strong",
    "apply_settlement",
    "apply_settlement_pure",
    "create_pool",
    "add_liquidity",
    "remove_liquidity",
    "Settlement",
    "Fill",
    "FillAction",
    "DexConfig",
    "DexEffects",
    "DexState",
    "DexStepResult",
    "dex_step",
    "FeeAccumulatorState",
    "FeeSplitParams",
    "FeeSplitResult",
    "split_fee_with_dust_carry",
    "OracleState",
    "init_oracle_state",
    "is_fresh",
    "update_price_timestamp",
    "EpochOracleCommitment",
    "OracleRegistry",
    "ModuleOracleView",
    "create_module_views",
    "estimate_cross_module_arbitrage_bps",
    "PriceImpactPreview",
    "compute_spot_price_e8",
    "compute_isolated_output",
    "compute_price_impact_bps",
    "price_impact_preview",
    "VaultState",
    "VaultCommand",
    "VaultStepResult",
    "init_vault_state",
    "vault_step",
    "ZUSDState",
    "ZUSDCommand",
    "ZUSDStepResult",
    "init_zusd_state",
    "zusd_step",
]
