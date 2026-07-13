mod bounded;
mod codec;
mod error;
mod hash;
mod plan;
mod records;
mod validate;

pub use codec::{decode_exact_settlement_effect_plan_v2, encode_settlement_effect_plan_v2};
pub use error::SettlementEffectErrorV2;
pub use plan::{SettlementEffectPlanInputV2, SettlementEffectPlanV2};
pub use records::{
    AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, CarryEffectInputV2, CarryEffectKindV2,
    CarryEffectV2, LedgerCellWriteInputV2, LedgerCellWriteV2, MessageEffectInputV2,
    MessageEffectKindV2, MessageEffectV2, RewardEffectInputV2, RewardEffectV2, ValueHashV2,
};

pub const SETTLEMENT_EFFECT_PLAN_VERSION_V2: u16 = 2;
pub const MAX_SETTLEMENT_EFFECT_ROWS_V2: usize = 8_192;
pub const MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2: usize = 8 * 1_024 * 1_024;
