//! Native counterpart of the pure joint Spot/asset/global successor.
//!
//! This crate mirrors `src/core/spot_swap_plan_v2.py`,
//! `src/core/spot_swap_state_v2.py` and `src/core/spot_swap_global_v2.py` for
//! the single-pool actual-`SwapIntent` transition. It reuses the
//! GlobalSettlementABI V2 asset, global-state, occurrence, effect and
//! refinement values; only the Spot frame, the owned swap intent, the v8
//! quote arithmetic and the joint transition are new.
//!
//! Every value is a public candidate. Nothing here authenticates a subject,
//! verifies a receipt, publishes state or grants any production authority.

#![forbid(unsafe_code)]

mod global;
mod intent;
mod plan;
mod quote;
mod state;

pub use global::{
    require_complete_asset_projection_v2, require_spot_swap_projection_v2,
    transition_spot_swap_global_v2, SpotSwapGlobalAcceptedV2, SpotSwapGlobalRejectCodeV2,
    SpotSwapGlobalRejectKindV2, SpotSwapGlobalRejectedV2, SpotSwapGlobalResultV2,
    SpotSwapInputErrorV2, ALL_SPOT_SWAP_GLOBAL_REJECT_KINDS_V2,
    SPOT_SWAP_GLOBAL_STATEMENT_DOMAIN_V2,
};
pub use intent::{
    SpotSwapCommandBodyV2, SpotSwapIntentPartsV2, SpotSwapIntentV2, SpotSwapKindV2,
    SwapAmountBoundV2, SwapIntentFieldProfileV2, SwapIntentFieldValueV2, SwapIntentIntegerV2,
    MAX_SWAP_INTENT_FIELDS_CANONICAL_BYTES_V2, MAX_SWAP_INTENT_FIELD_COUNT_V2,
    MAX_SWAP_INTENT_FIELD_TEXT_CHARS_V2, MAX_SWAP_INTENT_INTEGER_DIGITS_V2,
    MAX_SWAP_INTENT_NONCE_V2, MAX_SWAP_INTENT_SALT_CHARS_V2, MAX_SWAP_INTENT_TEXT_CHARS_V2,
    SWAP_INTENT_MODULE_V2, SWAP_INTENT_TRANSPORT_RESERVED_FIELDS_V2, SWAP_INTENT_VERSION_V2,
};
pub use plan::{
    plan_spot_swap_v2, SpotSwapContextV2, SpotSwapDirectionV2, SpotSwapPlanResultV2,
    SpotSwapPlanV2, SpotSwapRejectCodeV2, ALL_SPOT_SWAP_REJECT_CODES_V2,
};
pub use quote::{
    quote_cpmm_swap_exact_in_v2, quote_cpmm_swap_exact_out_v2, SpotQuoteErrorV2, SpotQuoteResultV2,
    SpotSwapModeV2, SpotSwapQuoteV2, BPS_DENOM_V2, CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_V2,
    DEX_POOL_RESERVE_MAX_V2, DEX_SWAP_AMOUNT_MAX_V2,
};
pub use state::{
    compute_pool_id_v2, is_canonical_pool_asset_id_v2, is_lp_lock_owner_v2, validate_spot_owner_v2,
    PoolStatusV2, SpotIntentNonceV2, SpotLPPositionV2, SpotPoolSnapshotV2, SpotSwapStateV2,
    CURVE_TAG_CPMM_V2, DEX_LP_SUPPLY_MAX_V2, LP_LOCK_PUBKEY_V2, MAX_SPOT_CURVE_PARAMS_CHARS_V2,
    MAX_SPOT_INTENT_NONCE_V2, MAX_SPOT_OWNER_ROWS_V2, MAX_SPOT_POOL_TEXT_CHARS_V2,
    MAX_SPOT_STATE_CANONICAL_BYTES_V2, MIN_LP_LOCK_V2, SPOT_OWNER_HEX_CHARS_V2,
    SPOT_POOL_CUSTODY_DOMAIN_V2, SPOT_SWAP_STATE_SCHEMA_V2,
};
