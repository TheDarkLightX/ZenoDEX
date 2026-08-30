//! Bounded Rust refinement of the SHADOW Tokenomics buyback functional core.
//!
//! Phase A allocates the committed fee ingress, selects the capped reserve
//! spend, updates cadence, and emits the acyclic semantic quote port
//! `ZDEXAtomicBuybackQuotePortV2`.  Phase B re-derives phase A, binds the
//! Spot terminal obligation to that exact quote, and burns exactly the
//! purchased amount under the retained-supply and epoch-cap rules.
//!
//! The port omits journal and receipt-binding roots; the journal commits
//! `H(port)` and the discharged obligation id for an outer route composer to
//! pair.  Nothing here verifies a receipt, composes a route, publishes a
//! state, or grants value-moving authority.

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::{
    AssetConservationRowV1, EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1,
    LaneWriteV1,
};
use crate::release::LaneIdV1;
use crate::zdex_atomic_buyback_quote_port_v2::ZDEXAtomicBuybackQuotePortV2;
use crate::zdex_buyback_spend::{
    transition_zdex_buyback_spend_v1, ZDEXBuybackSpendAcceptedV1, ZDEXBuybackSpendContextV1,
    ZDEXBuybackSpendPolicyV1, ZDEXBuybackSpendRejectCodeV1, ZDEXBuybackSpendResultV1,
    ZDEXBuybackSpendStateV1, ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1,
};
use crate::zdex_fee_allocation_types::{
    ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1, ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1, ZDEXFeeStateV1, FEE_BUYBACK_PRINCIPAL_V1,
};
use crate::zdex_hyperdeflation::retained_supply_atoms_v1;
use crate::zdex_hyperdeflation_types::ZDEXHyperdeflationPolicyV1;
use crate::zdex_purchase_burn_types::{
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, ZDEXBuybackExecutionPolicyV1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1, PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
};
use crate::zdex_spot_buyback_transition::{
    ZDEXSpotFlowIdentityV1, ZDEXSpotFlowRoleV1, ZDEXSpotTerminalObligationV1,
};
use crate::zdex_tokenomics_lane_types::MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1;

pub const ZDEX_TOKENOMICS_BUYBACK_RELEASE_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-buyback-release/v1";
pub const ZDEX_TOKENOMICS_SUPPLY_CONTROL_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-supply-control/v1";
pub const ZDEX_TOKENOMICS_BUYBACK_LANE_STATE_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-buyback-lane-state/v1";
pub const ZDEX_TOKENOMICS_PROFILE_AUTHORIZATION_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-buyback-profile-authorization/v1";
pub const ZDEX_TOKENOMICS_SAFE_LIMIT_PORT_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-safe-limit-port/v1";
pub const ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-private-ports/v1";
pub const ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-buyback-transition-journal/v1";
pub const ZDEX_TOKENOMICS_FEE_ASSET_COUNT_CAP_V1: u64 = 64;
const _: () = assert!(MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1 == 64);

const MAX_DELTA_ATOMS_V1: u128 = i128::MAX.unsigned_abs();

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsBurnRejectCodeV1 {
    RETAINED_SUPPLY_FLOOR_REACHED,
    EPOCH_BURN_CAP_REACHED,
    BURN_EXCEEDS_CAPACITY,
}

/// Closed reject registry.  Kernel phases carry their exact inner code so an
/// invalid phase/code combination is unrepresentable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsBuybackRejectCodeV1 {
    AUTHORITY_MALFORMED,
    RELEASE_MISMATCH,
    PROFILE_MISMATCH,
    STATE_COMMITMENT_MISMATCH,
    SAFETY_LIMIT_MISMATCH,
    POLICY_MISMATCH,
    LANE_MALFORMED,
    SELECTION_MISMATCH,
    SPEND_REJECTED {
        spend_code: ZDEXBuybackSpendRejectCodeV1,
        fee_code: Option<ZDEXFeeAllocationRejectCodeV1>,
    },
    PURCHASE_PORT_MISMATCH,
    QUOTE_FLOW_MISMATCH,
    BURN_REJECTED(ZDEXTokenomicsBurnRejectCodeV1),
}

#[derive(Serialize)]
struct CanonicalSupplyControlV1<'a> {
    schema: &'static str,
    asset_id: &'a RootV1,
    policy_root: &'a RootV1,
    decimals: u64,
    precision_epoch: u64,
    live_supply_atoms: u128,
    burn_budget_epoch: u64,
    remaining_epoch_burn_cap_atoms: u128,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsSupplyControlStateV1 {
    pub asset_id: RootV1,
    pub policy_root: RootV1,
    pub decimals: u64,
    pub precision_epoch: u64,
    pub live_supply_atoms: u128,
    pub burn_budget_epoch: u64,
    pub remaining_epoch_burn_cap_atoms: u128,
}

impl ZDEXTokenomicsSupplyControlStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.asset_id
            .validate("Tokenomics supply asset id", false)?;
        self.policy_root
            .validate("Tokenomics supply policy root", false)?;
        if self.live_supply_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds("Tokenomics live supply"));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            "zdex-tokenomics-supply-control-v1",
            &canonical_supply_control_v1(self),
        )
    }
}

fn canonical_supply_control_v1(
    supply: &ZDEXTokenomicsSupplyControlStateV1,
) -> CanonicalSupplyControlV1<'_> {
    CanonicalSupplyControlV1 {
        schema: ZDEX_TOKENOMICS_SUPPLY_CONTROL_SCHEMA_V1,
        asset_id: &supply.asset_id,
        policy_root: &supply.policy_root,
        decimals: supply.decimals,
        precision_epoch: supply.precision_epoch,
        live_supply_atoms: supply.live_supply_atoms,
        burn_budget_epoch: supply.burn_budget_epoch,
        remaining_epoch_burn_cap_atoms: supply.remaining_epoch_burn_cap_atoms,
    }
}

/// One complete tokenomics state: supply control, fee states, cadence, and
/// the unrelated component roots.  No Spot pool reserve mirror exists.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackLaneStateV1 {
    pub supply: ZDEXTokenomicsSupplyControlStateV1,
    pub fee_allocation_states: Vec<ZDEXFeeStateV1>,
    pub buyback_cadence_states: Vec<ZDEXBuybackSpendStateV1>,
    pub staking_state_root: RootV1,
    pub host_claims_state_root: RootV1,
    pub treasury_claims_state_root: RootV1,
    pub proof_rewards_state_root: RootV1,
    pub cover_reserve_state_root: RootV1,
    pub lp_rebates_state_root: RootV1,
}

impl ZDEXTokenomicsBuybackLaneStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.supply.validate()?;
        if self.fee_allocation_states.is_empty()
            || self.fee_allocation_states.len() > MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1
        {
            return Err(AbiErrorV1::InvalidBounds(
                "Tokenomics lane fee-state registry width",
            ));
        }
        for state in &self.fee_allocation_states {
            state.validate()?;
            if state.fee_asset_id == self.supply.asset_id {
                return Err(AbiErrorV1::InvalidBinding(
                    "Tokenomics supply asset cannot also be a fee asset",
                ));
            }
        }
        if self
            .fee_allocation_states
            .windows(2)
            .any(|pair| pair[0].fee_asset_id >= pair[1].fee_asset_id)
        {
            return Err(AbiErrorV1::InvalidOrder("Tokenomics lane fee states"));
        }
        if self.buyback_cadence_states.len() != self.fee_allocation_states.len() {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics lane cadence registry width",
            ));
        }
        for (cadence, fee) in self
            .buyback_cadence_states
            .iter()
            .zip(&self.fee_allocation_states)
        {
            cadence.validate()?;
            if cadence.quote_asset_id != fee.fee_asset_id {
                return Err(AbiErrorV1::InvalidBinding(
                    "Tokenomics lane cadence asset registry",
                ));
            }
        }
        for root in [
            &self.staking_state_root,
            &self.host_claims_state_root,
            &self.treasury_claims_state_root,
            &self.proof_rewards_state_root,
            &self.cover_reserve_state_root,
            &self.lp_rebates_state_root,
        ] {
            root.validate("Tokenomics lane component root", false)?;
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            supply: CanonicalSupplyControlV1<'a>,
            fee_allocation_states: &'a [ZDEXFeeStateV1],
            buyback_cadence_states: &'a [ZDEXBuybackSpendStateV1],
            staking_state_root: &'a RootV1,
            host_claims_state_root: &'a RootV1,
            treasury_claims_state_root: &'a RootV1,
            proof_rewards_state_root: &'a RootV1,
            cover_reserve_state_root: &'a RootV1,
            lp_rebates_state_root: &'a RootV1,
        }
        hash_global_v1(
            "zdex-tokenomics-buyback-lane-state-v1",
            &Canonical {
                schema: ZDEX_TOKENOMICS_BUYBACK_LANE_STATE_SCHEMA_V1,
                supply: canonical_supply_control_v1(&self.supply),
                fee_allocation_states: &self.fee_allocation_states,
                buyback_cadence_states: &self.buyback_cadence_states,
                staking_state_root: &self.staking_state_root,
                host_claims_state_root: &self.host_claims_state_root,
                treasury_claims_state_root: &self.treasury_claims_state_root,
                proof_rewards_state_root: &self.proof_rewards_state_root,
                cover_reserve_state_root: &self.cover_reserve_state_root,
                lp_rebates_state_root: &self.lp_rebates_state_root,
            },
        )
    }

    fn with_quote_asset_states_v1(
        &self,
        fee_state: &ZDEXFeeStateV1,
        cadence: &ZDEXBuybackSpendStateV1,
    ) -> Self {
        let mut next = self.clone();
        for row in &mut next.fee_allocation_states {
            if row.fee_asset_id == fee_state.fee_asset_id {
                *row = fee_state.clone();
            }
        }
        for row in &mut next.buyback_cadence_states {
            if row.quote_asset_id == cadence.quote_asset_id {
                *row = cadence.clone();
            }
        }
        next
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackReleaseV1 {
    pub tokenomics_module_release_id: RootV1,
    pub spot_module_release_id: RootV1,
    pub route_release_id: RootV1,
    pub fee_asset_count_cap: u64,
}

impl ZDEXTokenomicsBuybackReleaseV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.tokenomics_module_release_id,
            &self.spot_module_release_id,
            &self.route_release_id,
        ] {
            root.validate("Tokenomics release root", false)?;
        }
        Ok(())
    }

    pub fn release_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            tokenomics_module_release_id: &'a RootV1,
            spot_module_release_id: &'a RootV1,
            route_release_id: &'a RootV1,
            fee_asset_count_cap: u64,
        }
        hash_global_v1(
            "zdex-tokenomics-buyback-release-v1",
            &Canonical {
                schema: ZDEX_TOKENOMICS_BUYBACK_RELEASE_SCHEMA_V1,
                tokenomics_module_release_id: &self.tokenomics_module_release_id,
                spot_module_release_id: &self.spot_module_release_id,
                route_release_id: &self.route_release_id,
                fee_asset_count_cap: self.fee_asset_count_cap,
            },
        )
    }

    fn is_bounded_v1(&self) -> bool {
        self.fee_asset_count_cap == ZDEX_TOKENOMICS_FEE_ASSET_COUNT_CAP_V1
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsProfileAuthorizationV1 {
    pub profile_root: RootV1,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub route_release_id: RootV1,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub release_root: RootV1,
    pub execution_policy_root: RootV1,
    pub fee_policy_root: RootV1,
    pub spend_policy_root: RootV1,
    pub hyperdeflation_policy_root: RootV1,
    pub price_policy_root: RootV1,
}

impl ZDEXTokenomicsProfileAuthorizationV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "Tokenomics profile chain id")?;
        for root in [
            &self.profile_root,
            &self.deployment_root,
            &self.route_release_id,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.release_root,
            &self.execution_policy_root,
            &self.fee_policy_root,
            &self.spend_policy_root,
            &self.hyperdeflation_policy_root,
            &self.price_policy_root,
        ] {
            root.validate("Tokenomics profile root", false)?;
        }
        Ok(())
    }

    pub fn authorization_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            profile_root: &'a RootV1,
            chain_id: &'a str,
            deployment_root: &'a RootV1,
            route_release_id: &'a RootV1,
            spot_module_release_id: &'a RootV1,
            tokenomics_module_release_id: &'a RootV1,
            release_root: &'a RootV1,
            execution_policy_root: &'a RootV1,
            fee_policy_root: &'a RootV1,
            spend_policy_root: &'a RootV1,
            hyperdeflation_policy_root: &'a RootV1,
            price_policy_root: &'a RootV1,
        }
        hash_global_v1(
            "zdex-tokenomics-buyback-profile-authorization-v1",
            &Canonical {
                schema: ZDEX_TOKENOMICS_PROFILE_AUTHORIZATION_SCHEMA_V1,
                profile_root: &self.profile_root,
                chain_id: &self.chain_id,
                deployment_root: &self.deployment_root,
                route_release_id: &self.route_release_id,
                spot_module_release_id: &self.spot_module_release_id,
                tokenomics_module_release_id: &self.tokenomics_module_release_id,
                release_root: &self.release_root,
                execution_policy_root: &self.execution_policy_root,
                fee_policy_root: &self.fee_policy_root,
                spend_policy_root: &self.spend_policy_root,
                hyperdeflation_policy_root: &self.hyperdeflation_policy_root,
                price_policy_root: &self.price_policy_root,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackAuthorityContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub profile_authorization_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub tokenomics_pre_state_root: RootV1,
    pub writer_epoch: u64,
    pub current_height: u64,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub price_policy_root: RootV1,
    pub release: ZDEXTokenomicsBuybackReleaseV1,
    pub execution_policy: ZDEXBuybackExecutionPolicyV1,
    pub fee_policy: ZDEXFeeAllocationPolicyV1,
    pub spend_policy: ZDEXBuybackSpendPolicyV1,
    pub hyperdeflation_policy: ZDEXHyperdeflationPolicyV1,
    pub profile_authorization: ZDEXTokenomicsProfileAuthorizationV1,
}

impl ZDEXTokenomicsBuybackAuthorityContextV1 {
    fn validate_wire(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "Tokenomics authority chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.profile_authorization_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.tokenomics_pre_state_root,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.price_policy_root,
        ] {
            root.validate("Tokenomics authority root", false)?;
        }
        self.release.validate()?;
        self.execution_policy.validate()?;
        self.fee_policy.validate()?;
        self.spend_policy.validate()?;
        self.hyperdeflation_policy.validate()?;
        self.profile_authorization.validate()
    }
}

/// `MALFORMED` is a no-authority test vector; it selects no accepted path.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value", deny_unknown_fields)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsBuybackAuthorityInputV1 {
    CONTEXT(Box<ZDEXTokenomicsBuybackAuthorityContextV1>),
    MALFORMED,
}

/// Spot/Oracle route-safe quote limit as caller-constructible typed provenance.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsSafeLimitPortV1 {
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub tokenomics_pre_state_root: RootV1,
    pub selected_pool_id: RootV1,
    pub quote_asset_id: RootV1,
    pub zdex_asset_id: RootV1,
    pub price_policy_root: RootV1,
    pub oracle_occurrence_id: RootV1,
    pub binding_root: RootV1,
    pub current_height: u64,
    pub route_safe_quote_limit_atoms: u128,
}

impl ZDEXTokenomicsSafeLimitPortV1 {
    fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.tokenomics_pre_state_root,
            &self.selected_pool_id,
            &self.quote_asset_id,
            &self.zdex_asset_id,
            &self.price_policy_root,
            &self.oracle_occurrence_id,
            &self.binding_root,
        ] {
            root.validate("Tokenomics safe limit root", false)?;
        }
        if self.route_safe_quote_limit_atoms > MAX_DELTA_ATOMS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "Tokenomics route safe quote limit",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackIntentInputV1 {
    pub authority: ZDEXTokenomicsBuybackAuthorityInputV1,
    pub pre_state: ZDEXTokenomicsBuybackLaneStateV1,
    pub safe_limit_port: ZDEXTokenomicsSafeLimitPortV1,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value", deny_unknown_fields)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsSpotObligationInputV1 {
    OBLIGATION(Box<ZDEXSpotTerminalObligationV1>),
    MALFORMED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackInputV1 {
    pub intent_input: ZDEXTokenomicsBuybackIntentInputV1,
    pub spot_obligation: ZDEXTokenomicsSpotObligationInputV1,
}

/// The produced quote port and the consumed Spot obligation, as one pair.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsPrivatePortsV1 {
    pub quote_output: ZDEXAtomicBuybackQuotePortV2,
    pub burn_input: ZDEXSpotTerminalObligationV1,
}

impl ZDEXTokenomicsPrivatePortsV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.quote_output.validate()?;
        self.burn_input.obligation_id()?;
        if self.quote_output.selected_pool_id != self.burn_input.selected_pool_id
            || self.quote_output.producer_module_release_id
                != self.burn_input.consumer_module_release_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics private ports exact role pair",
            ));
        }
        Ok(())
    }

    pub fn ports_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical {
            schema: &'static str,
            quote_port_root: RootV1,
            burn_input_obligation_id: RootV1,
            quote_amount_atoms: u128,
            burn_amount_atoms: u128,
        }
        hash_global_v1(
            "zdex-tokenomics-private-ports-v1",
            &Canonical {
                schema: ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V1,
                quote_port_root: self.quote_output.port_root()?,
                burn_input_obligation_id: self.burn_input.obligation_id()?,
                quote_amount_atoms: self.quote_output.amount_atoms,
                burn_amount_atoms: self.burn_input.purchased_atoms,
            },
        )
    }
}

/// Complete witness of the Lean accounting premises owned by this lane.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBuybackJournalV1 {
    pub context_root: RootV1,
    pub pre_state_root: RootV1,
    pub spend_post_state_root: RootV1,
    pub post_state_root: RootV1,
    pub spend_effect_plan_root: RootV1,
    pub effect_plan_root: RootV1,
    pub quote_port_root: RootV1,
    pub private_ports_root: RootV1,
    pub discharged_obligation_id: RootV1,
    pub fee_allocation_occurrence_root: RootV1,
    pub spend_intent_root: RootV1,
    pub safety_limit_binding_root: RootV1,
    pub selected_pool_id: RootV1,
    pub quote_asset_id: RootV1,
    pub zdex_asset_id: RootV1,
    pub current_height: u64,
    pub fee_charged_atoms: u128,
    pub buyback_allocation_atoms: u128,
    pub other_allocations_atoms: u128,
    pub carried_residue_atoms: u128,
    pub buyback_reserve_pre_atoms: u128,
    pub buyback_reserve_post_atoms: u128,
    pub quote_spend_atoms: u128,
    pub route_safe_quote_limit_atoms: u128,
    pub purchased_zdex_atoms: u128,
    pub burned_zdex_atoms: u128,
    pub live_supply_pre_atoms: u128,
    pub live_supply_post_atoms: u128,
    pub retained_supply_atoms: u128,
    pub remaining_epoch_burn_cap_pre_atoms: u128,
    pub remaining_epoch_burn_cap_post_atoms: u128,
}

impl ZDEXTokenomicsBuybackJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.context_root,
            &self.pre_state_root,
            &self.spend_post_state_root,
            &self.post_state_root,
            &self.spend_effect_plan_root,
            &self.effect_plan_root,
            &self.quote_port_root,
            &self.private_ports_root,
            &self.discharged_obligation_id,
            &self.fee_allocation_occurrence_root,
            &self.spend_intent_root,
            &self.safety_limit_binding_root,
            &self.selected_pool_id,
            &self.quote_asset_id,
            &self.zdex_asset_id,
        ] {
            root.validate("Tokenomics journal root", false)?;
        }
        let fee_total = self
            .buyback_allocation_atoms
            .checked_add(self.other_allocations_atoms)
            .and_then(|value| value.checked_add(self.carried_residue_atoms));
        let reserve_available = self
            .buyback_reserve_pre_atoms
            .checked_add(self.buyback_allocation_atoms);
        let spend_holds = self.quote_spend_atoms != 0
            && self.quote_spend_atoms <= self.route_safe_quote_limit_atoms
            && fee_total == Some(self.fee_charged_atoms)
            && self
                .buyback_reserve_post_atoms
                .checked_add(self.quote_spend_atoms)
                == reserve_available
            && self.pre_state_root != self.spend_post_state_root;
        let burn_holds = self.burned_zdex_atoms != 0
            && self.purchased_zdex_atoms == self.burned_zdex_atoms
            && self
                .live_supply_post_atoms
                .checked_add(self.burned_zdex_atoms)
                == Some(self.live_supply_pre_atoms)
            && self.retained_supply_atoms != 0
            && self.retained_supply_atoms <= self.live_supply_post_atoms
            && self
                .remaining_epoch_burn_cap_post_atoms
                .checked_add(self.burned_zdex_atoms)
                == Some(self.remaining_epoch_burn_cap_pre_atoms)
            && self.spend_post_state_root != self.post_state_root;
        if !(spend_holds && burn_holds) {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics journal accounting projection",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            #[serde(flatten)]
            journal: &'a ZDEXTokenomicsBuybackJournalV1,
        }
        hash_global_v1(
            "zdex-tokenomics-buyback-transition-journal-v1",
            &Canonical {
                schema: ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V1,
                journal: self,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackRejectedV1 {
    code: ZDEXTokenomicsBuybackRejectCodeV1,
    pre_state: ZDEXTokenomicsBuybackLaneStateV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXTokenomicsBuybackRejectedV1 {
    pub fn code(&self) -> ZDEXTokenomicsBuybackRejectCodeV1 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics buyback reject is exact no-op",
            ));
        }
        Ok(())
    }
}

/// Phase-A result with private fields; SHADOW data, not publication authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackIntentV1 {
    pre_state: ZDEXTokenomicsBuybackLaneStateV1,
    spend_post_state: ZDEXTokenomicsBuybackLaneStateV1,
    spend_effects: GlobalEconomicEffectPlanV1,
    spend: ZDEXBuybackSpendAcceptedV1,
    quote_output: ZDEXAtomicBuybackQuotePortV2,
    context_root: RootV1,
}

impl ZDEXTokenomicsBuybackIntentV1 {
    pub fn pre_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.pre_state
    }

    pub fn spend_post_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.spend_post_state
    }

    pub fn spend_effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.spend_effects
    }

    pub fn spend(&self) -> &ZDEXBuybackSpendAcceptedV1 {
        &self.spend
    }

    pub fn quote_output(&self) -> &ZDEXAtomicBuybackQuotePortV2 {
        &self.quote_output
    }

    pub fn context_root(&self) -> &RootV1 {
        &self.context_root
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.spend_post_state.validate()?;
        self.spend_effects.validate()?;
        self.spend.validate()?;
        self.quote_output.validate()?;
        self.context_root
            .validate("Tokenomics intent context root", false)?;
        let pre_root = self.pre_state.state_root()?;
        let spend_post_root = self.spend_post_state.state_root()?;
        let quote = &self.quote_output;
        if pre_root == spend_post_root
            || quote.producer_quote_pre_state_root != pre_root
            || quote.producer_quote_post_state_root != spend_post_root
            || quote.producer_quote_effect_plan_root != self.spend_effects.effect_plan_root()?
            || quote.amount_atoms != self.spend.intent().quote_spend_atoms
            || quote.source_principal() != FEE_BUYBACK_PRINCIPAL_V1
            || !self.spend_effects.lane_writes.is_empty()
            || self.spend_post_state.supply != self.pre_state.supply
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics intent projection binding",
            ));
        }
        Ok(())
    }
}

/// Accepted transition with private fields; SHADOW data, not a receipt.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsBuybackAcceptedV1 {
    intent: ZDEXTokenomicsBuybackIntentV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    ports: ZDEXTokenomicsPrivatePortsV1,
    journal: ZDEXTokenomicsBuybackJournalV1,
}

impl ZDEXTokenomicsBuybackAcceptedV1 {
    pub fn intent(&self) -> &ZDEXTokenomicsBuybackIntentV1 {
        &self.intent
    }

    pub fn pre_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.intent.pre_state
    }

    pub fn spend_post_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.intent.spend_post_state
    }

    pub fn post_state(&self) -> &ZDEXTokenomicsBuybackLaneStateV1 {
        &self.post_state
    }

    pub fn spend_effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.intent.spend_effects
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn quote_output(&self) -> &ZDEXAtomicBuybackQuotePortV2 {
        &self.intent.quote_output
    }

    pub fn ports(&self) -> &ZDEXTokenomicsPrivatePortsV1 {
        &self.ports
    }

    pub fn journal(&self) -> &ZDEXTokenomicsBuybackJournalV1 {
        &self.journal
    }

    pub fn discharged_obligation(&self) -> &ZDEXSpotTerminalObligationV1 {
        &self.ports.burn_input
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.intent.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.ports.validate()?;
        self.journal.validate()?;
        let pre_root = self.intent.pre_state.state_root()?;
        let spend_post_root = self.intent.spend_post_state.state_root()?;
        let post_root = self.post_state.state_root()?;
        let journal = &self.journal;
        let burn_delta = i128::try_from(journal.burned_zdex_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("Tokenomics burn effect width"))?;
        let spend_delta = i128::try_from(journal.quote_spend_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("Tokenomics spend effect width"))?;
        let lane_write_matches = self.effects.lane_writes.len() == 1
            && self.effects.lane_writes[0].lane_id == LaneIdV1::ZDEX_TOKENOMICS
            && self.effects.lane_writes[0].pre_root == pre_root
            && self.effects.lane_writes[0].post_root == post_root;
        let burn_row_matches = self.effects.rows.iter().any(|row| {
            row.kind == EconomicEffectKindV1::BURN
                && row.principal == ZDEX_SUPPLY_PRINCIPAL_V1
                && row.asset == journal.zdex_asset_id.to_string()
                && row.delta_atoms == -burn_delta
        });
        let reserve_row_matches = self.effects.rows.iter().any(|row| {
            row.kind == EconomicEffectKindV1::CUSTODY
                && row.principal == FEE_BUYBACK_PRINCIPAL_V1
                && row.asset == journal.quote_asset_id.to_string()
                && row.delta_atoms == -spend_delta
        });
        let spend_rows_included = self
            .intent
            .spend_effects
            .rows
            .iter()
            .all(|row| self.effects.rows.contains(row));
        if spend_post_root == post_root
            || !lane_write_matches
            || !burn_row_matches
            || !reserve_row_matches
            || !spend_rows_included
            || journal.context_root != self.intent.context_root
            || journal.pre_state_root != pre_root
            || journal.spend_post_state_root != spend_post_root
            || journal.post_state_root != post_root
            || journal.spend_effect_plan_root != self.intent.spend_effects.effect_plan_root()?
            || journal.effect_plan_root != self.effects.effect_plan_root()?
            || journal.quote_port_root != self.ports.quote_output.port_root()?
            || journal.private_ports_root != self.ports.ports_root()?
            || journal.discharged_obligation_id != self.ports.burn_input.obligation_id()?
            || journal.quote_spend_atoms != self.ports.quote_output.amount_atoms
            || journal.purchased_zdex_atoms != self.ports.burn_input.purchased_atoms
            || journal.live_supply_post_atoms != self.post_state.supply.live_supply_atoms
            || journal.remaining_epoch_burn_cap_post_atoms
                != self.post_state.supply.remaining_epoch_burn_cap_atoms
            || self.post_state.fee_allocation_states
                != self.intent.spend_post_state.fee_allocation_states
            || self.post_state.buyback_cadence_states
                != self.intent.spend_post_state.buyback_cadence_states
            || self.ports.quote_output != self.intent.quote_output
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Tokenomics buyback accepted projection binding",
            ));
        }
        Ok(())
    }
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsBuybackIntentResultV1 {
    Accepted(Box<ZDEXTokenomicsBuybackIntentV1>),
    Rejected(Box<ZDEXTokenomicsBuybackRejectedV1>),
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsBuybackResultV1 {
    Accepted(Box<ZDEXTokenomicsBuybackAcceptedV1>),
    Rejected(Box<ZDEXTokenomicsBuybackRejectedV1>),
}

struct BurnAmountsV1 {
    purchased: u128,
    retained: u128,
    live_pre: u128,
    live_post: u128,
    cap_pre: u128,
    cap_post: u128,
}

fn empty_effect_plan_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject_v1(
    code: ZDEXTokenomicsBuybackRejectCodeV1,
    state: &ZDEXTokenomicsBuybackLaneStateV1,
) -> ZDEXTokenomicsBuybackRejectedV1 {
    ZDEXTokenomicsBuybackRejectedV1 {
        code,
        pre_state: state.clone(),
        post_state: state.clone(),
        effects: empty_effect_plan_v1(),
    }
}

fn effect_kind_label_v1(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}

fn sort_effect_rows_v1(rows: &mut [EconomicEffectRowV1]) {
    rows.sort_by(|left, right| {
        (
            effect_kind_label_v1(left.kind),
            left.asset.as_str(),
            left.principal.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                effect_kind_label_v1(right.kind),
                right.asset.as_str(),
                right.principal.as_str(),
                right.custody_domain.as_str(),
            ))
    });
}

fn context_root_v1(
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
    port: &ZDEXTokenomicsSafeLimitPortV1,
) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Canonical<'a> {
        chain_id: &'a str,
        deployment_root: &'a RootV1,
        profile_root: &'a RootV1,
        profile_authorization_root: &'a RootV1,
        route_release_id: &'a RootV1,
        command_occurrence_id: &'a RootV1,
        global_pre_state_root: &'a RootV1,
        tokenomics_pre_state_root: &'a RootV1,
        writer_epoch: u64,
        current_height: u64,
        spot_module_release_id: &'a RootV1,
        tokenomics_module_release_id: &'a RootV1,
        release_root: RootV1,
        execution_policy_root: RootV1,
        fee_policy_root: RootV1,
        spend_policy_root: RootV1,
        hyperdeflation_policy_root: RootV1,
        price_policy_root: &'a RootV1,
        oracle_occurrence_id: &'a RootV1,
        safety_limit_binding_root: &'a RootV1,
        route_safe_quote_limit_atoms: u128,
    }
    hash_global_v1(
        "zdex-tokenomics-buyback-transition-context-v1",
        &Canonical {
            chain_id: &authority.chain_id,
            deployment_root: &authority.deployment_root,
            profile_root: &authority.profile_root,
            profile_authorization_root: &authority.profile_authorization_root,
            route_release_id: &authority.route_release_id,
            command_occurrence_id: &authority.command_occurrence_id,
            global_pre_state_root: &authority.global_pre_state_root,
            tokenomics_pre_state_root: &authority.tokenomics_pre_state_root,
            writer_epoch: authority.writer_epoch,
            current_height: authority.current_height,
            spot_module_release_id: &authority.spot_module_release_id,
            tokenomics_module_release_id: &authority.tokenomics_module_release_id,
            release_root: authority.release.release_root()?,
            execution_policy_root: authority.execution_policy.policy_root()?,
            fee_policy_root: authority.fee_policy.policy_root()?,
            spend_policy_root: authority.spend_policy.policy_root()?,
            hyperdeflation_policy_root: authority.hyperdeflation_policy.policy_root()?,
            price_policy_root: &authority.price_policy_root,
            oracle_occurrence_id: &port.oracle_occurrence_id,
            safety_limit_binding_root: &port.binding_root,
            route_safe_quote_limit_atoms: port.route_safe_quote_limit_atoms,
        },
    )
}

fn release_matches_v1(authority: &ZDEXTokenomicsBuybackAuthorityContextV1) -> bool {
    let release = &authority.release;
    release.is_bounded_v1()
        && authority.route_release_id == release.route_release_id
        && authority.spot_module_release_id == release.spot_module_release_id
        && authority.tokenomics_module_release_id == release.tokenomics_module_release_id
}

fn profile_matches_v1(authority: &ZDEXTokenomicsBuybackAuthorityContextV1) -> AbiResultV1<bool> {
    let profile = &authority.profile_authorization;
    Ok(
        authority.profile_authorization_root == profile.authorization_root()?
            && profile.profile_root == authority.profile_root
            && profile.chain_id == authority.chain_id
            && profile.deployment_root == authority.deployment_root
            && profile.route_release_id == authority.route_release_id
            && profile.spot_module_release_id == authority.spot_module_release_id
            && profile.tokenomics_module_release_id == authority.tokenomics_module_release_id
            && profile.release_root == authority.release.release_root()?
            && profile.execution_policy_root == authority.execution_policy.policy_root()?
            && profile.fee_policy_root == authority.fee_policy.policy_root()?
            && profile.spend_policy_root == authority.spend_policy.policy_root()?
            && profile.hyperdeflation_policy_root
                == authority.hyperdeflation_policy.policy_root()?
            && profile.price_policy_root == authority.price_policy_root,
    )
}

fn safe_limit_matches_v1(
    port: &ZDEXTokenomicsSafeLimitPortV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
) -> bool {
    let policy = &authority.execution_policy;
    port.validate().is_ok()
        && port.profile_root == authority.profile_root
        && port.route_release_id == authority.route_release_id
        && port.command_occurrence_id == authority.command_occurrence_id
        && port.global_pre_state_root == authority.global_pre_state_root
        && port.tokenomics_pre_state_root == authority.tokenomics_pre_state_root
        && port.selected_pool_id == policy.pool_id
        && port.quote_asset_id == policy.quote_asset_id
        && port.zdex_asset_id == policy.zdex_asset_id
        && port.price_policy_root == authority.price_policy_root
        && port.current_height == authority.current_height
}

fn policy_matches_v1(authority: &ZDEXTokenomicsBuybackAuthorityContextV1) -> bool {
    let policy = &authority.execution_policy;
    policy.quote_asset_id < policy.zdex_asset_id
        && authority.spend_policy.quote_asset_id == policy.quote_asset_id
        && authority.hyperdeflation_policy.asset_id == policy.zdex_asset_id
}

fn lane_well_formed_v1(
    state: &ZDEXTokenomicsBuybackLaneStateV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
) -> AbiResultV1<bool> {
    let policy = &authority.hyperdeflation_policy;
    let width_ok = u64::try_from(state.fee_allocation_states.len())
        .map(|width| width <= authority.release.fee_asset_count_cap)
        .unwrap_or(false);
    Ok(width_ok
        && state.supply.asset_id == policy.asset_id
        && state.supply.policy_root == policy.policy_root()?
        && state.supply.decimals <= policy.maximum_decimals)
}

fn select_quote_asset_v1<'a>(
    state: &'a ZDEXTokenomicsBuybackLaneStateV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
) -> AbiResultV1<Option<(&'a ZDEXFeeStateV1, &'a ZDEXBuybackSpendStateV1)>> {
    let quote_asset_id = &authority.execution_policy.quote_asset_id;
    let fee_rows = state
        .fee_allocation_states
        .iter()
        .filter(|row| &row.fee_asset_id == quote_asset_id)
        .collect::<Vec<_>>();
    let cadence_rows = state
        .buyback_cadence_states
        .iter()
        .filter(|row| &row.quote_asset_id == quote_asset_id)
        .collect::<Vec<_>>();
    if fee_rows.len() != 1 || cadence_rows.len() != 1 {
        return Ok(None);
    }
    let (fee_state, cadence) = (fee_rows[0], cadence_rows[0]);
    if fee_state.policy_root != authority.fee_policy.policy_root()?
        || cadence.policy_root != authority.spend_policy.policy_root()?
    {
        return Ok(None);
    }
    Ok(Some((fee_state, cadence)))
}

fn run_spend_kernel_v1(
    candidate: &ZDEXTokenomicsBuybackIntentInputV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
    fee_state: &ZDEXFeeStateV1,
    cadence: &ZDEXBuybackSpendStateV1,
) -> AbiResultV1<Result<ZDEXBuybackSpendAcceptedV1, ZDEXTokenomicsBuybackRejectCodeV1>> {
    let port = &candidate.safe_limit_port;
    let fee_context = ZDEXFeeAllocationContextV1 {
        chain_id: authority.chain_id.clone(),
        deployment_root: authority.deployment_root.clone(),
        profile_root: authority.profile_root.clone(),
        writer_epoch: authority.writer_epoch,
        allocation_route_release_id: authority.route_release_id.clone(),
        authorized_buyback_route_release_id: authority.route_release_id.clone(),
        tokenomics_module_release_id: authority.tokenomics_module_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        policy_root: authority.fee_policy.policy_root()?,
    };
    // The fee command is the committed ingress; no caller-selected fee budget exists.
    let fee_command = ZDEXFeeAllocationCommandV1 {
        fee_charged_atoms: fee_state.fee_ingress_atoms,
    };
    let spend_context = ZDEXBuybackSpendContextV1 {
        schema: ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1.to_owned(),
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        expected_fee_pre_state_root: fee_state.state_root()?,
        expected_cadence_pre_state_root: cadence.state_root()?,
        safety_limit_binding_root: port.binding_root.clone(),
        quote_asset_id: authority.execution_policy.quote_asset_id.clone(),
        current_height: authority.current_height,
        route_safe_quote_limit_atoms: port.route_safe_quote_limit_atoms,
    };
    let result = transition_zdex_buyback_spend_v1(
        &authority.spend_policy,
        cadence,
        &authority.fee_policy,
        fee_state,
        &fee_context,
        &fee_command,
        &spend_context,
    )?;
    Ok(match result {
        ZDEXBuybackSpendResultV1::Accepted(accepted) => Ok(*accepted),
        ZDEXBuybackSpendResultV1::Rejected(rejected) => {
            Err(ZDEXTokenomicsBuybackRejectCodeV1::SPEND_REJECTED {
                spend_code: rejected.code(),
                fee_code: rejected.fee_code(),
            })
        }
    })
}

fn spend_effects_v1(
    spend: &ZDEXBuybackSpendAcceptedV1,
    quote_asset_id: &RootV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let allocation = &spend.fee_allocation().effects;
    let spend_delta = i128::try_from(spend.intent().quote_spend_atoms)
        .map_err(|_| AbiErrorV1::InvalidBounds("Tokenomics reserve debit width"))?;
    let mut rows = allocation.rows.clone();
    rows.push(EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::CUSTODY,
        principal: FEE_BUYBACK_PRINCIPAL_V1.to_owned(),
        asset: quote_asset_id.to_string(),
        custody_domain: PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1.to_owned(),
        delta_atoms: -spend_delta,
    });
    sort_effect_rows_v1(&mut rows);
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation: allocation.asset_conservation.clone(),
        fee_conservation: allocation.fee_conservation.clone(),
        lane_writes: vec![],
        occurrence_consumptions: allocation.occurrence_consumptions.clone(),
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    Ok(effects)
}

fn quote_port_v2(
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
    spend: &ZDEXBuybackSpendAcceptedV1,
    pre_state_root: RootV1,
    spend_post_state_root: RootV1,
    spend_effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<ZDEXAtomicBuybackQuotePortV2> {
    let policy = &authority.execution_policy;
    let port = ZDEXAtomicBuybackQuotePortV2 {
        schema: crate::zdex_atomic_buyback_quote_port_v2::ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2
            .to_owned(),
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        global_pre_state_root: authority.global_pre_state_root.clone(),
        producer_module_release_id: authority.tokenomics_module_release_id.clone(),
        consumer_module_release_id: authority.spot_module_release_id.clone(),
        producer_quote_pre_state_root: pre_state_root,
        producer_quote_post_state_root: spend_post_state_root,
        producer_quote_effect_plan_root: spend_effects.effect_plan_root()?,
        selected_pool_id: policy.pool_id.clone(),
        quote_asset_id: policy.quote_asset_id.clone(),
        amount_atoms: spend.intent().quote_spend_atoms,
    };
    port.validate()?;
    Ok(port)
}

fn first_context_reject_v1(
    candidate: &ZDEXTokenomicsBuybackIntentInputV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
) -> AbiResultV1<Option<ZDEXTokenomicsBuybackRejectCodeV1>> {
    if !release_matches_v1(authority) {
        return Ok(Some(ZDEXTokenomicsBuybackRejectCodeV1::RELEASE_MISMATCH));
    }
    if !profile_matches_v1(authority)? {
        return Ok(Some(ZDEXTokenomicsBuybackRejectCodeV1::PROFILE_MISMATCH));
    }
    if authority.tokenomics_pre_state_root != candidate.pre_state.state_root()? {
        return Ok(Some(
            ZDEXTokenomicsBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH,
        ));
    }
    if !safe_limit_matches_v1(&candidate.safe_limit_port, authority) {
        return Ok(Some(
            ZDEXTokenomicsBuybackRejectCodeV1::SAFETY_LIMIT_MISMATCH,
        ));
    }
    if !policy_matches_v1(authority) {
        return Ok(Some(ZDEXTokenomicsBuybackRejectCodeV1::POLICY_MISMATCH));
    }
    if !lane_well_formed_v1(&candidate.pre_state, authority)? {
        return Ok(Some(ZDEXTokenomicsBuybackRejectCodeV1::LANE_MALFORMED));
    }
    Ok(None)
}

/// Phase A: allocate the committed ingress, select the capped reserve spend,
/// update cadence, and emit the acyclic governed quote port.
pub fn derive_zdex_tokenomics_buyback_intent_v1(
    candidate: &ZDEXTokenomicsBuybackIntentInputV1,
) -> AbiResultV1<ZDEXTokenomicsBuybackIntentResultV1> {
    let pre_state = &candidate.pre_state;
    let rejected = |code| {
        Ok(ZDEXTokenomicsBuybackIntentResultV1::Rejected(Box::new(
            reject_v1(code, pre_state),
        )))
    };
    let authority = match &candidate.authority {
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority)
            if authority.validate_wire().is_ok() =>
        {
            authority
        }
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(_)
        | ZDEXTokenomicsBuybackAuthorityInputV1::MALFORMED => {
            return rejected(ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED);
        }
    };
    if let Some(code) = first_context_reject_v1(candidate, authority)? {
        return rejected(code);
    }
    let Some((fee_state, cadence)) = select_quote_asset_v1(pre_state, authority)? else {
        return rejected(ZDEXTokenomicsBuybackRejectCodeV1::SELECTION_MISMATCH);
    };
    let spend = match run_spend_kernel_v1(candidate, authority, fee_state, cadence)? {
        Ok(spend) => spend,
        Err(code) => return rejected(code),
    };
    let spend_post_state =
        pre_state.with_quote_asset_states_v1(spend.fee_post_state(), spend.cadence_post_state());
    let spend_effects = spend_effects_v1(&spend, &authority.execution_policy.quote_asset_id)?;
    let quote_output = quote_port_v2(
        authority,
        &spend,
        pre_state.state_root()?,
        spend_post_state.state_root()?,
        &spend_effects,
    )?;
    let intent = ZDEXTokenomicsBuybackIntentV1 {
        pre_state: pre_state.clone(),
        spend_post_state,
        spend_effects,
        spend,
        quote_output,
        context_root: context_root_v1(authority, &candidate.safe_limit_port)?,
    };
    intent.validate()?;
    Ok(ZDEXTokenomicsBuybackIntentResultV1::Accepted(Box::new(
        intent,
    )))
}

fn spot_flow_id_v1(
    role: ZDEXSpotFlowRoleV1,
    obligation: &ZDEXSpotTerminalObligationV1,
    asset: &RootV1,
    source_principal: &str,
    destination_principal: &str,
    amount_atoms: u128,
) -> AbiResultV1<RootV1> {
    ZDEXSpotFlowIdentityV1 {
        role,
        context_root: obligation.context_root.clone(),
        selected_pool_id: obligation.selected_pool_id.clone(),
        asset: asset.clone(),
        source_principal: source_principal.to_owned(),
        destination_principal: destination_principal.to_owned(),
        amount_atoms,
    }
    .flow_id()
}

/// Bind the Spot obligation to the governed pool, assets, burn port, and exact q.
fn purchase_port_reject_v1<'a>(
    obligation_input: &'a ZDEXTokenomicsSpotObligationInputV1,
    authority: &ZDEXTokenomicsBuybackAuthorityContextV1,
    intent: &ZDEXTokenomicsBuybackIntentV1,
) -> AbiResultV1<Result<&'a ZDEXSpotTerminalObligationV1, ZDEXTokenomicsBuybackRejectCodeV1>> {
    let obligation = match obligation_input {
        ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(obligation)
            if obligation.obligation_id().is_ok() =>
        {
            obligation.as_ref()
        }
        _ => {
            return Ok(Err(
                ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH,
            ))
        }
    };
    let policy = &authority.execution_policy;
    let burn_principal = zdex_occurrence_burn_port_v1(
        &authority.profile_root,
        &authority.route_release_id,
        &authority.command_occurrence_id,
    )?;
    let zdex_pool = zdex_pool_reserve_principal_v1(&policy.pool_id, &policy.zdex_asset_id)?;
    let purchased_flow_id = spot_flow_id_v1(
        ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
        obligation,
        &policy.zdex_asset_id,
        &zdex_pool,
        &burn_principal,
        obligation.purchased_atoms,
    );
    if obligation.consumer_module_release_id != authority.tokenomics_module_release_id
        || obligation.burn_asset != policy.zdex_asset_id
        || obligation.burn_principal != burn_principal
        || obligation.selected_pool_id != policy.pool_id
        || purchased_flow_id.as_ref() != Ok(&obligation.purchased_output_flow_id)
    {
        return Ok(Err(
            ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH,
        ));
    }
    let quote_flow_id = spot_flow_id_v1(
        ZDEXSpotFlowRoleV1::QUOTE_INPUT,
        obligation,
        &policy.quote_asset_id,
        FEE_BUYBACK_PRINCIPAL_V1,
        &intent.quote_output.destination_principal()?,
        intent.quote_output.amount_atoms,
    )?;
    if quote_flow_id != obligation.quote_input_flow_id {
        return Ok(Err(ZDEXTokenomicsBuybackRejectCodeV1::QUOTE_FLOW_MISMATCH));
    }
    Ok(Ok(obligation))
}

/// Burn exactly the purchased amount under retained-supply and epoch caps.
fn burn_amounts_v1(
    supply: &ZDEXTokenomicsSupplyControlStateV1,
    policy: &ZDEXHyperdeflationPolicyV1,
    purchased: u128,
) -> AbiResultV1<Result<BurnAmountsV1, ZDEXTokenomicsBurnRejectCodeV1>> {
    let retained = retained_supply_atoms_v1(supply.live_supply_atoms, policy)?;
    let ratio_headroom = supply
        .live_supply_atoms
        .checked_sub(retained)
        .ok_or(AbiErrorV1::InvalidBounds("Tokenomics retained supply"))?;
    let epoch_headroom = supply.remaining_epoch_burn_cap_atoms;
    if ratio_headroom == 0 {
        return Ok(Err(
            ZDEXTokenomicsBurnRejectCodeV1::RETAINED_SUPPLY_FLOOR_REACHED,
        ));
    }
    if epoch_headroom == 0 {
        return Ok(Err(ZDEXTokenomicsBurnRejectCodeV1::EPOCH_BURN_CAP_REACHED));
    }
    if purchased > ratio_headroom.min(epoch_headroom) {
        return Ok(Err(ZDEXTokenomicsBurnRejectCodeV1::BURN_EXCEEDS_CAPACITY));
    }
    Ok(Ok(BurnAmountsV1 {
        purchased,
        retained,
        live_pre: supply.live_supply_atoms,
        live_post: supply.live_supply_atoms - purchased,
        cap_pre: epoch_headroom,
        cap_post: epoch_headroom - purchased,
    }))
}

fn build_effects_v1(
    intent: &ZDEXTokenomicsBuybackIntentV1,
    post_state: &ZDEXTokenomicsBuybackLaneStateV1,
    zdex_asset_id: &RootV1,
    amounts: &BurnAmountsV1,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let spend = &intent.spend_effects;
    let burn_delta = i128::try_from(amounts.purchased)
        .map_err(|_| AbiErrorV1::InvalidBounds("Tokenomics burn effect width"))?;
    let mut rows = spend.rows.clone();
    rows.push(EconomicEffectRowV1 {
        kind: EconomicEffectKindV1::BURN,
        principal: ZDEX_SUPPLY_PRINCIPAL_V1.to_owned(),
        asset: zdex_asset_id.to_string(),
        custody_domain: PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1.to_owned(),
        delta_atoms: -burn_delta,
    });
    sort_effect_rows_v1(&mut rows);
    let mut asset_conservation = spend.asset_conservation.clone();
    asset_conservation.push(AssetConservationRowV1 {
        asset: zdex_asset_id.to_string(),
        owned_and_custodied_pre_atoms: amounts.live_pre,
        owned_and_custodied_post_atoms: amounts.live_post,
        supply_pre_atoms: amounts.live_pre,
        supply_post_atoms: amounts.live_post,
        authorized_issue_atoms: 0,
        authorized_burn_atoms: amounts.purchased,
    });
    asset_conservation.sort_by(|left, right| left.asset.cmp(&right.asset));
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation,
        fee_conservation: spend.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: intent.pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: spend.occurrence_consumptions.clone(),
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    Ok(effects)
}

fn build_journal_v1(
    intent: &ZDEXTokenomicsBuybackIntentV1,
    port: &ZDEXTokenomicsSafeLimitPortV1,
    post_state: &ZDEXTokenomicsBuybackLaneStateV1,
    effects: &GlobalEconomicEffectPlanV1,
    ports: &ZDEXTokenomicsPrivatePortsV1,
    zdex_asset_id: &RootV1,
    amounts: &BurnAmountsV1,
) -> AbiResultV1<ZDEXTokenomicsBuybackJournalV1> {
    let occurrence = &intent.spend.fee_allocation().occurrence;
    let spend_intent = intent.spend.intent();
    let quote = &intent.quote_output;
    let other_allocations = occurrence
        .allocations
        .iter()
        .skip(1)
        .try_fold(0_u128, |total, row| total.checked_add(row.allocation_atoms))
        .ok_or(AbiErrorV1::Conservation("Tokenomics other allocations"))?;
    let reserve_post = intent
        .spend
        .fee_post_state()
        .destination_balances
        .first()
        .map(|row| row.allocation_atoms)
        .ok_or(AbiErrorV1::InvalidBinding("Tokenomics buyback reserve row"))?;
    let journal = ZDEXTokenomicsBuybackJournalV1 {
        context_root: intent.context_root.clone(),
        pre_state_root: quote.producer_quote_pre_state_root.clone(),
        spend_post_state_root: quote.producer_quote_post_state_root.clone(),
        post_state_root: post_state.state_root()?,
        spend_effect_plan_root: quote.producer_quote_effect_plan_root.clone(),
        effect_plan_root: effects.effect_plan_root()?,
        quote_port_root: quote.port_root()?,
        private_ports_root: ports.ports_root()?,
        discharged_obligation_id: ports.burn_input.obligation_id()?,
        fee_allocation_occurrence_root: occurrence.occurrence_root()?,
        spend_intent_root: spend_intent.intent_root()?,
        safety_limit_binding_root: port.binding_root.clone(),
        selected_pool_id: quote.selected_pool_id.clone(),
        quote_asset_id: quote.quote_asset_id.clone(),
        zdex_asset_id: zdex_asset_id.clone(),
        current_height: port.current_height,
        fee_charged_atoms: occurrence.fee_charged_atoms,
        buyback_allocation_atoms: occurrence.buyback_quote_atoms(),
        other_allocations_atoms: other_allocations,
        carried_residue_atoms: occurrence.carried_residue_atoms,
        buyback_reserve_pre_atoms: spend_intent.buyback_reserve_before_atoms,
        buyback_reserve_post_atoms: reserve_post,
        quote_spend_atoms: quote.amount_atoms,
        route_safe_quote_limit_atoms: port.route_safe_quote_limit_atoms,
        purchased_zdex_atoms: ports.burn_input.purchased_atoms,
        burned_zdex_atoms: amounts.purchased,
        live_supply_pre_atoms: amounts.live_pre,
        live_supply_post_atoms: amounts.live_post,
        retained_supply_atoms: amounts.retained,
        remaining_epoch_burn_cap_pre_atoms: amounts.cap_pre,
        remaining_epoch_burn_cap_post_atoms: amounts.cap_post,
    };
    journal.validate()?;
    Ok(journal)
}

/// Phase B: re-derive phase A, discharge the Spot obligation, and apply the
/// exact burn.  A rejection returns the exact pre-state plus empty effects.
pub fn transition_zdex_tokenomics_buyback_v1(
    candidate: &ZDEXTokenomicsBuybackInputV1,
) -> AbiResultV1<ZDEXTokenomicsBuybackResultV1> {
    let pre_state = &candidate.intent_input.pre_state;
    let rejected = |code| {
        Ok(ZDEXTokenomicsBuybackResultV1::Rejected(Box::new(
            reject_v1(code, pre_state),
        )))
    };
    let intent = match derive_zdex_tokenomics_buyback_intent_v1(&candidate.intent_input)? {
        ZDEXTokenomicsBuybackIntentResultV1::Accepted(intent) => *intent,
        ZDEXTokenomicsBuybackIntentResultV1::Rejected(rejected) => {
            return Ok(ZDEXTokenomicsBuybackResultV1::Rejected(rejected));
        }
    };
    let ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) =
        &candidate.intent_input.authority
    else {
        return rejected(ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED);
    };
    let obligation = match purchase_port_reject_v1(&candidate.spot_obligation, authority, &intent)?
    {
        Ok(obligation) => obligation,
        Err(code) => return rejected(code),
    };
    let zdex_asset_id = &authority.execution_policy.zdex_asset_id;
    let amounts = match burn_amounts_v1(
        &pre_state.supply,
        &authority.hyperdeflation_policy,
        obligation.purchased_atoms,
    )? {
        Ok(amounts) => amounts,
        Err(code) => return rejected(ZDEXTokenomicsBuybackRejectCodeV1::BURN_REJECTED(code)),
    };
    let mut post_state = intent.spend_post_state.clone();
    post_state.supply.live_supply_atoms = amounts.live_post;
    post_state.supply.remaining_epoch_burn_cap_atoms = amounts.cap_post;
    let effects = build_effects_v1(&intent, &post_state, zdex_asset_id, &amounts)?;
    let ports = ZDEXTokenomicsPrivatePortsV1 {
        quote_output: intent.quote_output.clone(),
        burn_input: obligation.clone(),
    };
    let journal = build_journal_v1(
        &intent,
        &candidate.intent_input.safe_limit_port,
        &post_state,
        &effects,
        &ports,
        zdex_asset_id,
        &amounts,
    )?;
    let accepted = ZDEXTokenomicsBuybackAcceptedV1 {
        intent,
        post_state,
        effects,
        ports,
        journal,
    };
    accepted.validate()?;
    Ok(ZDEXTokenomicsBuybackResultV1::Accepted(Box::new(accepted)))
}
