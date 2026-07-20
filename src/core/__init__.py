"""
Core DEX algorithms
"""

from .cpmm import (
    swap_exact_in,
    swap_exact_out,
    compute_lp_mint,
    compute_lp_burn,
)
from .batch_clearing import (
    compute_settlement,
    validate_settlement,
    apply_settlement,
    apply_settlement_pure,
)
from .settlement_strong_validator import validate_settlement_strong
from .liquidity import (
    create_pool,
    add_liquidity,
    remove_liquidity,
)
from .settlement import Settlement, Fill, FillAction
from .dex import DexConfig, DexEffects, DexState, DexStepResult
from .dex import step as dex_step
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .oracle import OracleState, init_oracle_state, is_fresh, update_price_timestamp
from .epoch_oracle_commitment import (
    EpochOracleCommitment,
    OracleRegistry,
    ModuleOracleView,
    create_module_views,
    estimate_cross_module_arbitrage_bps,
)
from .price_impact_preview import (
    PriceImpactPreview,
    compute_spot_price_e8,
    compute_isolated_output,
    compute_price_impact_bps,
    price_impact_preview,
)
from .vault import VaultState, VaultCommand, VaultStepResult
from .vault import init_vault_state, step as vault_step
from .zusd import (
    ZUSDState,
    ZUSDCommand,
    ZUSDStepResult,
    ZUSDMultiState,
    ZUSDMultiCommand,
    ZUSDMultiStepResult,
    init_state as init_zusd_state,
    init_multi_state as init_zusd_multi_state,
    step as zusd_step,
    step_multi as zusd_step_multi,
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
    "ZUSDMultiState",
    "ZUSDMultiCommand",
    "ZUSDMultiStepResult",
    "init_zusd_state",
    "init_zusd_multi_state",
    "zusd_step",
    "zusd_step_multi",
]
