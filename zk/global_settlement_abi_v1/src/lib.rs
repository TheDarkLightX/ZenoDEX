//! Typed, deterministic Rust projection of `GlobalSettlementABI V1`.
//!
//! This crate validates canonical values and recomputes their roots. It exposes
//! a receipt-verifier port without a verifier implementation, ledger adapter,
//! writer capability, or production status.

mod asset_lane_coordinator;
mod asset_lane_projection;
mod asset_transfer;
mod asset_transfer_lane_module;
mod asset_transfer_policy_registry;
mod asset_transfer_receipt_admission;
mod asset_transfer_types;
mod bounded_vec;
mod canonical;
mod current_profile_lane_gate;
mod economic_command_authentication;
mod economic_command_authorization_registry;
mod economic_command_signature_verifier_deployment;
mod economic_command_signature_verifier_registry;
mod economic_effect_occurrence;
mod economic_epoch_receipt_verification;
mod economic_initial_state;
mod economic_initial_state_atom_coverage;
mod economic_initial_state_outbox_continuity;
mod economic_initial_state_replay_continuity;
mod economic_initial_state_terminal_continuity;
mod effects;
mod epoch_effect_composition;
mod external_custody_disabled_lane;
mod global_accounting_allocation_certificate;
mod global_accounting_lane_producers;
mod global_economic_replay_refinement;
mod global_economic_state_delta;
mod global_economic_state_effect_refinement;
mod global_oracle_occurrence_authority;
mod global_oracle_price_occurrence;
mod lane_capability_registry;
mod lane_composition_receipt_verification;
mod lane_module_receipt_verification;
mod lane_module_release_route_binding;
mod managed_asset_lifecycle;
mod managed_asset_lifecycle_lane_module;
mod managed_asset_lifecycle_types;
mod managed_asset_policy_registry;
mod migration;
mod perps_margin;
mod perps_margin_lane_coordinator;
mod perps_margin_lane_module;
mod perps_margin_types;
mod perps_market_policy;
mod proof;
mod proof_rewards_policy_blocked_lane;
mod receipt_backed_asset_lane_composition;
mod receipt_backed_perps_margin_lane_composition;
mod release;
mod route_composition_receipt_verification;
mod route_global_state_projection;
mod state;
mod zdex_atomic_buyback;
mod zdex_atomic_buyback_lane_ports;
pub mod zdex_atomic_buyback_quote_port_v2;
mod zdex_atomic_buyback_state;
mod zdex_buyback_price_authority;
mod zdex_buyback_price_safety;
// This replay scaffold has no mounted caller while Buyback V2 remains a
// SHADOW predicate. Its behavior is exercised by module-local counterexamples.
#[allow(dead_code)]
mod zdex_buyback_shadow_composer_v2;
mod zdex_buyback_spend;
mod zdex_current_authority;
mod zdex_fee_allocation;
mod zdex_fee_allocation_profile_binding;
mod zdex_fee_allocation_receipt_verification;
mod zdex_fee_allocation_types;
mod zdex_hyperdeflation;
mod zdex_hyperdeflation_decode;
mod zdex_hyperdeflation_results;
mod zdex_hyperdeflation_route_refinement;
mod zdex_hyperdeflation_types;
mod zdex_hyperdeflation_validation;
mod zdex_purchase_burn_effects;
mod zdex_purchase_burn_receipt_verification;
mod zdex_purchase_burn_route;
mod zdex_purchase_burn_types;
mod zdex_spot_buyback_transition;
mod zdex_spot_buyback_transition_v2;
mod zdex_tokenomics_buyback_transition;
mod zdex_tokenomics_buyback_transition_v2;
mod zdex_tokenomics_fee_lane_coordinator;
mod zdex_tokenomics_fee_lane_receipt_verification;
mod zdex_tokenomics_fee_lane_types;
mod zdex_tokenomics_lane_coordinator;
mod zdex_tokenomics_lane_receipt_common;
mod zdex_tokenomics_lane_receipt_verification;
mod zdex_tokenomics_lane_types;

pub use asset_lane_coordinator::*;
pub use asset_lane_projection::*;
pub use asset_transfer::*;
pub use asset_transfer_lane_module::*;
pub use asset_transfer_policy_registry::*;
pub use asset_transfer_receipt_admission::*;
pub use asset_transfer_types::*;
pub use canonical::{
    canonical_bytes_v1, canonical_economic_command_body_bytes_v1, hash_bytes_sha256_v1,
    hash_economic_command_body_bytes_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_ASSET_BALANCE_ROWS_V1, MAX_ASSET_CUSTODY_ROWS_V1,
    MAX_ASSET_POLICY_ROWS_V1, MAX_ATOMS_V1, MAX_CYCLE_BUDGET_V1,
    MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1, MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
    MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1, MAX_EFFECT_PLAN_LANE_WRITES_V1,
    MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1, MAX_EFFECT_PLAN_ROWS_V1, MAX_EPOCH_COMMANDS_V1,
    MAX_EPOCH_LEAF_OCCURRENCES_V1, MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, MAX_GLOBAL_ORACLE_ROWS_V1,
    MAX_GLOBAL_OUTBOX_ROWS_V1, MAX_GLOBAL_REPLAY_ROWS_V1, MAX_GLOBAL_SUPPLY_ROWS_V1,
    MAX_GLOBAL_TERMINAL_ROWS_V1, MAX_JOURNAL_BYTES_V1, MAX_LANE_MODULE_RECEIPT_BYTES_V1,
    MAX_POLICY_BINDINGS_V1, MAX_ROUTE_MODULES_V1, MAX_TOKEN_BYTES_V1, ZERO_ROOT_V1,
};
pub use current_profile_lane_gate::*;
pub use economic_command_authentication::*;
pub use economic_command_authorization_registry::*;
pub use economic_command_signature_verifier_deployment::*;
pub use economic_command_signature_verifier_registry::*;
pub use economic_effect_occurrence::*;
pub use economic_epoch_receipt_verification::*;
pub use economic_initial_state::*;
pub use economic_initial_state_atom_coverage::*;
pub use economic_initial_state_outbox_continuity::*;
pub use economic_initial_state_replay_continuity::*;
pub use economic_initial_state_terminal_continuity::*;
pub use effects::*;
pub use epoch_effect_composition::*;
pub use external_custody_disabled_lane::*;
pub use global_accounting_allocation_certificate::*;
pub use global_accounting_lane_producers::*;
pub use global_economic_state_effect_refinement::*;
pub use global_oracle_occurrence_authority::*;
pub use global_oracle_price_occurrence::*;
pub use lane_capability_registry::*;
pub use lane_composition_receipt_verification::*;
pub use lane_module_receipt_verification::*;
pub use lane_module_release_route_binding::*;
pub use managed_asset_lifecycle::*;
pub use managed_asset_lifecycle_lane_module::*;
pub use managed_asset_lifecycle_types::*;
pub use managed_asset_policy_registry::*;
pub use migration::*;
pub use perps_margin::*;
pub use perps_margin_lane_coordinator::*;
pub use perps_margin_lane_module::*;
pub use perps_margin_types::*;
pub use perps_market_policy::*;
pub use proof::*;
pub use proof_rewards_policy_blocked_lane::*;
pub use receipt_backed_asset_lane_composition::*;
pub use receipt_backed_perps_margin_lane_composition::*;
pub use release::*;
pub use route_composition_receipt_verification::*;
pub use route_global_state_projection::*;
pub use state::*;
pub use zdex_atomic_buyback::*;
pub use zdex_atomic_buyback_lane_ports::*;
pub use zdex_atomic_buyback_state::*;
pub use zdex_buyback_price_authority::*;
pub use zdex_buyback_price_safety::*;
pub use zdex_buyback_shadow_composer_v2::{
    validate_route_terminal_claims_v2, validate_shadow_composed_effect_plan_v2,
    ZDEXBuybackRouteReceiptClaimsV2, ZDEXBuybackRouteTerminalInputV2,
    ZDEXBuybackRouteTerminalRejectCodeV2, ZDEXBuybackShadowComposerRejectCodeV2,
};
pub use zdex_buyback_spend::*;
pub use zdex_current_authority::*;
pub use zdex_fee_allocation::*;
pub use zdex_fee_allocation_profile_binding::*;
pub use zdex_fee_allocation_receipt_verification::*;
pub use zdex_fee_allocation_types::*;
pub use zdex_hyperdeflation::*;
pub use zdex_hyperdeflation_results::*;
pub use zdex_hyperdeflation_route_refinement::*;
pub use zdex_hyperdeflation_types::*;
pub use zdex_purchase_burn_receipt_verification::*;
pub use zdex_purchase_burn_route::*;
pub use zdex_purchase_burn_types::*;
pub use zdex_spot_buyback_transition::*;
pub use zdex_spot_buyback_transition_v2::*;
pub use zdex_tokenomics_buyback_transition::*;
pub use zdex_tokenomics_buyback_transition_v2::*;
pub use zdex_tokenomics_fee_lane_coordinator::*;
pub use zdex_tokenomics_fee_lane_receipt_verification::*;
pub use zdex_tokenomics_fee_lane_types::*;
pub use zdex_tokenomics_lane_coordinator::*;
pub use zdex_tokenomics_lane_receipt_common::*;
pub use zdex_tokenomics_lane_receipt_verification::*;
pub use zdex_tokenomics_lane_types::*;
