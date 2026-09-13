#![forbid(unsafe_code)]

mod claims;
mod global;
mod state;

pub use claims::{
    advance_margin_claims_v2, derive_terminal_plan_v2, require_margin_claim_projection_v2,
};
pub use global::{
    transition_perps_margin_global_v2, PerpsMarginGlobalAcceptedV2, PerpsMarginGlobalRejectCodeV2,
    PerpsMarginGlobalRejectKindV2, PerpsMarginGlobalRejectedV2, PerpsMarginGlobalResultV2,
    PerpsMarginOracleV2,
};
pub use state::{
    margin_claim_id_v2, PerpsMarginClaimBindingCanonicalV2, PerpsMarginClaimBindingV2,
    PerpsMarginStateCanonicalV2, PerpsMarginStateV2, MAX_PERPS_MARGIN_ACCOUNTS_V2,
    PERPS_MARGIN_MODULE_SCHEMA_V2, PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2,
    PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2,
};
