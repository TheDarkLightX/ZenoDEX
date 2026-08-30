//! Bounded Rust refinement of the SHADOW Spot buyback functional core.
//!
//! This module derives a governed CPMM purchase from immutable typed input. It
//! neither verifies receipt provenance nor publishes a state root. Its output
//! is therefore research-only SHADOW evidence: a later route/epoch verifier
//! must bind the terminal burn obligation and atomically publish all lane
//! effects before any value-moving authority exists.

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
};
use crate::effects::{
    EconomicEffectKindV1, EconomicEffectRowV1, GlobalEconomicEffectPlanV1, LaneWriteV1,
};
use crate::release::{LaneIdV1, ReleaseStatusV1};
use crate::zdex_buyback_price_safety::{
    verify_zdex_buyback_price_safety_v1, VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1, ZDEXBuybackPriceSafetyRejectCodeV1,
    ZDEXBuybackPriceSafetyResultV1, BASIS_POINTS_V1,
    ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1,
};
use crate::zdex_fee_allocation_types::FEE_BUYBACK_PRINCIPAL_V1;
use crate::zdex_purchase_burn_types::{
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, ZDEXBuybackExecutionPolicyV1,
    AMM_POOL_CUSTODY_DOMAIN_V1,
};

pub const ZDEX_SPOT_BUYBACK_RELEASE_SCHEMA_V1: &str = "zenodex/zdex-spot-buyback-release/v1";
pub const ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1: &str = "zenodex/zdex-spot-pool-definition/v1";
pub const ZDEX_SPOT_POOL_SCHEMA_V1: &str = "zenodex/zdex-spot-pool/v1";
pub const ZDEX_SPOT_LANE_STATE_SCHEMA_V1: &str = "zenodex/zdex-spot-lane-state/v1";
pub const ZDEX_SPOT_PROFILE_AUTHORIZATION_SCHEMA_V1: &str =
    "zenodex/zdex-spot-buyback-profile-authorization/v1";
pub const ZDEX_SPOT_ORACLE_REGISTRY_SCHEMA_V1: &str = "zenodex/zdex-spot-oracle-registry/v1";
pub const ZDEX_SPOT_QUOTE_INPUT_SCHEMA_V1: &str = "zenodex/zdex-spot-quote-input/v1";
pub const ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V1: &str = "zenodex/zdex-spot-price-envelope/v1";
pub const ZDEX_SPOT_FLOW_SCHEMA_V1: &str = "zenodex/zdex-spot-buyback-flow/v1";
pub const ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V1: &str = "zenodex/zdex-spot-private-ports/v1";
pub const ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V1: &str =
    "zenodex/zdex-spot-terminal-obligation/v1";
pub const ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V1: &str =
    "zenodex/zdex-spot-buyback-transition-journal/v1";

pub const ZDEX_SPOT_RESERVE_CAP_ATOMS_V1: u128 = 3_000_000_000;
pub const ZDEX_SPOT_SWAP_CAP_ATOMS_V1: u128 = 3_000_000_000;
pub const ZDEX_SPOT_POOL_COUNT_CAP_V1: u128 = 64;
pub const CPMM_V8_EXACT_IN_CURVE_V1: &str = "CPMM_V8_EXACT_IN";

const MAX_DELTA_ATOMS_V1: u128 = i128::MAX.unsigned_abs();

#[derive(Serialize)]
struct CanonicalPoolDefinitionV1<'a> {
    schema: &'static str,
    asset0: &'a RootV1,
    asset1: &'a RootV1,
    fee_bps: u128,
    curve_kind: ZDEXSpotCurveKindV1,
    curve_release_id: &'a RootV1,
    curve_params_root: &'a RootV1,
}

#[derive(Serialize)]
struct CanonicalPoolV1<'a> {
    schema: &'static str,
    pool_id: &'a RootV1,
    definition: CanonicalPoolDefinitionV1<'a>,
    reserve0_atoms: u128,
    reserve1_atoms: u128,
    lp_supply_atoms: u128,
    status: ZDEXSpotPoolStatusV1,
    creation_release_id: &'a RootV1,
    created_height: u64,
}

#[derive(Serialize)]
struct CanonicalFlowV1<'a> {
    schema: &'static str,
    role: ZDEXSpotFlowRoleV1,
    context_root: &'a RootV1,
    selected_pool_id: &'a RootV1,
    asset: &'a RootV1,
    source_principal: &'a str,
    destination_principal: &'a str,
    amount_atoms: u128,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotPoolStatusV1 {
    ACTIVE,
    FROZEN,
    DISABLED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotCurveKindV1 {
    CPMM_V8_EXACT_IN,
    REGISTERED_OTHER,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotOracleStatusV1 {
    PENDING,
    FINAL,
    DISPUTED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotFlowRoleV1 {
    QUOTE_INPUT,
    PURCHASED_ZDEX_OUTPUT,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotBuybackRejectCodeV1 {
    AUTHORITY_MALFORMED,
    RELEASE_MISMATCH,
    PROFILE_MISMATCH,
    STATE_COMMITMENT_MISMATCH,
    QUOTE_PORT_MISMATCH,
    ORACLE_MISMATCH,
    PRICE_SUBJECT_MISMATCH,
    POLICY_MISMATCH,
    LANE_MALFORMED,
    SELECTION_MISMATCH,
    POOL_INACTIVE,
    AMOUNT_OUT_OF_RANGE,
    ARITHMETIC_OUT_OF_RANGE,
    FEE_CONSUMES_INPUT,
    ZERO_OUTPUT,
    MINIMUM_OUTPUT_MISMATCH,
    PRICE_UNSAFE,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotRegisteredCurveReleaseV1 {
    pub release_id: RootV1,
    pub status: ReleaseStatusV1,
}

impl ZDEXSpotRegisteredCurveReleaseV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.release_id.validate("Spot curve release id", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotPoolCreationReleaseV1 {
    pub module_release_id: RootV1,
    pub status: ReleaseStatusV1,
}

impl ZDEXSpotPoolCreationReleaseV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.module_release_id
            .validate("Spot pool creation module release id", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotBuybackReleaseV1 {
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub route_release_id: RootV1,
    pub cpmm_curve_release_id: RootV1,
    pub protocol_fee_share_bps: u128,
    pub reserve_cap_atoms: u128,
    pub swap_cap_atoms: u128,
    pub pool_count_cap: u128,
    pub pool_creation_releases: Vec<ZDEXSpotPoolCreationReleaseV1>,
    pub registered_sibling_curve_releases: Vec<ZDEXSpotRegisteredCurveReleaseV1>,
}

impl ZDEXSpotBuybackReleaseV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.route_release_id,
            &self.cpmm_curve_release_id,
        ] {
            root.validate("Spot buyback release root", false)?;
        }
        if self.pool_creation_releases.is_empty()
            || self
                .pool_creation_releases
                .windows(2)
                .any(|pair| pair[0].module_release_id >= pair[1].module_release_id)
        {
            return Err(AbiErrorV1::InvalidOrder("Spot pool creation releases"));
        }
        for row in &self.pool_creation_releases {
            row.validate()?;
        }
        if self
            .registered_sibling_curve_releases
            .windows(2)
            .any(|pair| pair[0].release_id >= pair[1].release_id)
        {
            return Err(AbiErrorV1::InvalidOrder("Spot sibling curve releases"));
        }
        for row in &self.registered_sibling_curve_releases {
            row.validate()?;
        }
        Ok(())
    }

    pub fn release_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            spot_module_release_id: &'a RootV1,
            tokenomics_module_release_id: &'a RootV1,
            route_release_id: &'a RootV1,
            cpmm_curve_release_id: &'a RootV1,
            protocol_fee_share_bps: u128,
            reserve_cap_atoms: u128,
            swap_cap_atoms: u128,
            pool_count_cap: u128,
            pool_creation_releases: &'a [ZDEXSpotPoolCreationReleaseV1],
            registered_sibling_curve_releases: &'a [ZDEXSpotRegisteredCurveReleaseV1],
        }
        hash_global_v1(
            "zdex-spot-buyback-release-v1",
            &Canonical {
                schema: ZDEX_SPOT_BUYBACK_RELEASE_SCHEMA_V1,
                spot_module_release_id: &self.spot_module_release_id,
                tokenomics_module_release_id: &self.tokenomics_module_release_id,
                route_release_id: &self.route_release_id,
                cpmm_curve_release_id: &self.cpmm_curve_release_id,
                protocol_fee_share_bps: self.protocol_fee_share_bps,
                reserve_cap_atoms: self.reserve_cap_atoms,
                swap_cap_atoms: self.swap_cap_atoms,
                pool_count_cap: self.pool_count_cap,
                pool_creation_releases: &self.pool_creation_releases,
                registered_sibling_curve_releases: &self.registered_sibling_curve_releases,
            },
        )
    }

    fn is_bounded_v1(&self) -> bool {
        self.protocol_fee_share_bps == 0
            && self.reserve_cap_atoms == ZDEX_SPOT_RESERVE_CAP_ATOMS_V1
            && self.swap_cap_atoms == ZDEX_SPOT_SWAP_CAP_ATOMS_V1
            && self.pool_count_cap == ZDEX_SPOT_POOL_COUNT_CAP_V1
    }

    fn pool_count_cap(&self) -> Option<usize> {
        usize::try_from(self.pool_count_cap).ok()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotPoolDefinitionV1 {
    pub asset0: RootV1,
    pub asset1: RootV1,
    pub fee_bps: u128,
    pub curve_kind: ZDEXSpotCurveKindV1,
    pub curve_release_id: RootV1,
    pub curve_params_root: RootV1,
}

impl ZDEXSpotPoolDefinitionV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.asset0.validate("Spot pool asset0", false)?;
        self.asset1.validate("Spot pool asset1", false)?;
        self.curve_release_id
            .validate("Spot pool curve release id", false)?;
        self.curve_params_root
            .validate("Spot pool curve params", true)
    }

    pub fn definition_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            "zdex-spot-pool-definition-v1",
            &canonical_pool_definition_v1(self),
        )
    }

    pub fn pool_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            definition: CanonicalPoolDefinitionV1<'a>,
        }
        hash_global_v1(
            "zdex-spot-pool-id-v1",
            &Canonical {
                schema: ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1,
                definition: canonical_pool_definition_v1(self),
            },
        )
    }
}

fn canonical_pool_definition_v1(
    definition: &ZDEXSpotPoolDefinitionV1,
) -> CanonicalPoolDefinitionV1<'_> {
    CanonicalPoolDefinitionV1 {
        schema: ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1,
        asset0: &definition.asset0,
        asset1: &definition.asset1,
        fee_bps: definition.fee_bps,
        curve_kind: definition.curve_kind,
        curve_release_id: &definition.curve_release_id,
        curve_params_root: &definition.curve_params_root,
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotPoolV1 {
    pub pool_id: RootV1,
    pub definition: ZDEXSpotPoolDefinitionV1,
    pub reserve0_atoms: u128,
    pub reserve1_atoms: u128,
    pub lp_supply_atoms: u128,
    pub status: ZDEXSpotPoolStatusV1,
    pub creation_release_id: RootV1,
    pub created_height: u64,
}

impl ZDEXSpotPoolV1 {
    fn validate_wire(&self) -> AbiResultV1<()> {
        self.pool_id.validate("Spot pool id", false)?;
        self.definition.validate()?;
        self.creation_release_id
            .validate("Spot pool creation release", false)
    }
}

fn canonical_pool_v1(pool: &ZDEXSpotPoolV1) -> CanonicalPoolV1<'_> {
    CanonicalPoolV1 {
        schema: ZDEX_SPOT_POOL_SCHEMA_V1,
        pool_id: &pool.pool_id,
        definition: canonical_pool_definition_v1(&pool.definition),
        reserve0_atoms: pool.reserve0_atoms,
        reserve1_atoms: pool.reserve1_atoms,
        lp_supply_atoms: pool.lp_supply_atoms,
        status: pool.status,
        creation_release_id: &pool.creation_release_id,
        created_height: pool.created_height,
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotLaneStateV1 {
    pub pools: Vec<ZDEXSpotPoolV1>,
    pub lp_ownership_root: RootV1,
    pub route_batch_root: RootV1,
    pub fee_residue_root: RootV1,
    pub pool_terminal_obligations_root: RootV1,
}

impl ZDEXSpotLaneStateV1 {
    fn validate_wire(&self) -> AbiResultV1<()> {
        for root in [
            &self.lp_ownership_root,
            &self.route_batch_root,
            &self.fee_residue_root,
            &self.pool_terminal_obligations_root,
        ] {
            root.validate("Spot lane root", false)?;
        }
        for pool in &self.pools {
            pool.validate_wire()?;
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate_wire()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            pools: Vec<CanonicalPoolV1<'a>>,
            lp_ownership_root: &'a RootV1,
            route_batch_root: &'a RootV1,
            fee_residue_root: &'a RootV1,
            pool_terminal_obligations_root: &'a RootV1,
        }
        hash_global_v1(
            "zdex-spot-lane-state-v1",
            &Canonical {
                schema: ZDEX_SPOT_LANE_STATE_SCHEMA_V1,
                pools: self.pools.iter().map(canonical_pool_v1).collect(),
                lp_ownership_root: &self.lp_ownership_root,
                route_batch_root: &self.route_batch_root,
                fee_residue_root: &self.fee_residue_root,
                pool_terminal_obligations_root: &self.pool_terminal_obligations_root,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotProfileAuthorizationV1 {
    pub profile_root: RootV1,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub route_release_id: RootV1,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub oracle_id: String,
    pub release_root: RootV1,
    pub execution_policy_root: RootV1,
    pub price_policy_root: RootV1,
}

impl ZDEXSpotProfileAuthorizationV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "Spot profile chain id")?;
        validate_token_v1(&self.oracle_id, "Spot profile Oracle id")?;
        for root in [
            &self.profile_root,
            &self.deployment_root,
            &self.route_release_id,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.release_root,
            &self.execution_policy_root,
            &self.price_policy_root,
        ] {
            root.validate("Spot profile root", false)?;
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
            oracle_id: &'a str,
            release_root: &'a RootV1,
            execution_policy_root: &'a RootV1,
            price_policy_root: &'a RootV1,
        }
        hash_global_v1(
            "zdex-spot-buyback-profile-authorization-v1",
            &Canonical {
                schema: ZDEX_SPOT_PROFILE_AUTHORIZATION_SCHEMA_V1,
                profile_root: &self.profile_root,
                chain_id: &self.chain_id,
                deployment_root: &self.deployment_root,
                route_release_id: &self.route_release_id,
                spot_module_release_id: &self.spot_module_release_id,
                tokenomics_module_release_id: &self.tokenomics_module_release_id,
                oracle_id: &self.oracle_id,
                release_root: &self.release_root,
                execution_policy_root: &self.execution_policy_root,
                price_policy_root: &self.price_policy_root,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotOracleOccurrenceV1 {
    pub price: ZDEXBuybackOraclePriceOccurrenceV1,
    pub finality_root: RootV1,
    pub status: ZDEXSpotOracleStatusV1,
}

impl ZDEXSpotOracleOccurrenceV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.price.validate()?;
        self.finality_root
            .validate("Spot Oracle finality root", false)
    }

    pub fn occurrence_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-spot-oracle-occurrence-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotOracleRegistryV1 {
    pub occurrences: Vec<ZDEXSpotOracleOccurrenceV1>,
}

impl ZDEXSpotOracleRegistryV1 {
    fn validate_wire(&self) -> AbiResultV1<()> {
        for occurrence in &self.occurrences {
            occurrence.validate()?;
        }
        Ok(())
    }

    fn registry_root(&self) -> AbiResultV1<RootV1> {
        self.validate_wire()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            occurrences: &'a [ZDEXSpotOracleOccurrenceV1],
        }
        hash_global_v1(
            "zdex-spot-oracle-registry-v1",
            &Canonical {
                schema: ZDEX_SPOT_ORACLE_REGISTRY_SCHEMA_V1,
                occurrences: &self.occurrences,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotBuybackAuthorityContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub profile_authorization_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub spot_pre_state_root: RootV1,
    pub writer_epoch: u64,
    pub current_height: u64,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub release: ZDEXSpotBuybackReleaseV1,
    pub execution_policy: ZDEXBuybackExecutionPolicyV1,
    pub expected_pool_definition: ZDEXSpotPoolDefinitionV1,
    pub price_policy: ZDEXBuybackPriceSafetyPolicyV1,
    pub profile_authorization: ZDEXSpotProfileAuthorizationV1,
    pub oracle_registry: ZDEXSpotOracleRegistryV1,
    pub oracle_occurrence: ZDEXSpotOracleOccurrenceV1,
}

impl ZDEXSpotBuybackAuthorityContextV1 {
    fn validate_wire(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "Spot authority chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.profile_authorization_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.spot_pre_state_root,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
        ] {
            root.validate("Spot authority root", false)?;
        }
        self.release.validate()?;
        self.execution_policy.validate()?;
        self.expected_pool_definition.validate()?;
        self.price_policy.validate()?;
        self.profile_authorization.validate()?;
        self.oracle_registry.validate_wire()?;
        self.oracle_occurrence.validate()
    }
}

/// Closed typed wire representation of the admission result.
///
/// `MALFORMED` is deliberately a no-authority test vector. It cannot carry a
/// context or select an accepted path.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", content = "value", deny_unknown_fields)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotBuybackAuthorityInputV1 {
    CONTEXT(Box<ZDEXSpotBuybackAuthorityContextV1>),
    MALFORMED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotQuoteInputPortV1 {
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub spot_pre_state_root: RootV1,
    pub source_module_release_id: RootV1,
    pub destination_module_release_id: RootV1,
    pub source_pre_state_root: RootV1,
    pub source_post_state_root: RootV1,
    pub source_effect_plan_root: RootV1,
    pub source_journal_root: RootV1,
    pub source_receipt_binding_root: RootV1,
    pub amount_atoms: u128,
}

impl ZDEXSpotQuoteInputPortV1 {
    fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.spot_pre_state_root,
            &self.source_module_release_id,
            &self.destination_module_release_id,
            &self.source_pre_state_root,
            &self.source_post_state_root,
            &self.source_effect_plan_root,
            &self.source_journal_root,
            &self.source_receipt_binding_root,
        ] {
            root.validate("Spot quote port root", false)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotPriceEnvelopeV1 {
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub spot_pre_state_root: RootV1,
    pub selected_pool_id: RootV1,
    pub oracle_occurrence_id: RootV1,
    pub oracle_finality_root: RootV1,
    pub quote_amount_atoms: u128,
    pub current_height: u64,
    pub oracle_observed_height: u64,
    pub oracle_quote_numerator_atoms: u128,
    pub oracle_zdex_denominator_atoms: u128,
    pub claimed_route_safe_quote_limit_atoms: u128,
    pub minimum_output_atoms: u128,
}

impl ZDEXSpotPriceEnvelopeV1 {
    fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.spot_pre_state_root,
            &self.selected_pool_id,
            &self.oracle_occurrence_id,
            &self.oracle_finality_root,
        ] {
            root.validate("Spot price envelope root", false)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotBuybackInputV1 {
    pub authority: ZDEXSpotBuybackAuthorityInputV1,
    pub pre_state: ZDEXSpotLaneStateV1,
    pub quote_port: ZDEXSpotQuoteInputPortV1,
    pub price_envelope: ZDEXSpotPriceEnvelopeV1,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotFlowIdentityV1 {
    pub role: ZDEXSpotFlowRoleV1,
    pub context_root: RootV1,
    pub selected_pool_id: RootV1,
    pub asset: RootV1,
    pub source_principal: String,
    pub destination_principal: String,
    pub amount_atoms: u128,
}

impl ZDEXSpotFlowIdentityV1 {
    fn validate(&self) -> AbiResultV1<()> {
        for root in [&self.context_root, &self.selected_pool_id, &self.asset] {
            root.validate("Spot flow root", false)?;
        }
        validate_token_v1(&self.source_principal, "Spot flow source principal")?;
        validate_token_v1(
            &self.destination_principal,
            "Spot flow destination principal",
        )?;
        if self.amount_atoms == 0 || self.amount_atoms > MAX_DELTA_ATOMS_V1 {
            return Err(AbiErrorV1::InvalidBounds("Spot flow amount"));
        }
        Ok(())
    }

    pub fn flow_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-spot-buyback-flow-v1", &canonical_flow_v1(self))
    }
}

fn canonical_flow_v1(flow: &ZDEXSpotFlowIdentityV1) -> CanonicalFlowV1<'_> {
    CanonicalFlowV1 {
        schema: ZDEX_SPOT_FLOW_SCHEMA_V1,
        role: flow.role,
        context_root: &flow.context_root,
        selected_pool_id: &flow.selected_pool_id,
        asset: &flow.asset,
        source_principal: &flow.source_principal,
        destination_principal: &flow.destination_principal,
        amount_atoms: flow.amount_atoms,
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotPrivatePortsV1 {
    pub quote_input: ZDEXSpotFlowIdentityV1,
    pub purchased_output: ZDEXSpotFlowIdentityV1,
}

impl ZDEXSpotPrivatePortsV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.quote_input.validate()?;
        self.purchased_output.validate()?;
        if self.quote_input.role != ZDEXSpotFlowRoleV1::QUOTE_INPUT
            || self.purchased_output.role != ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT
            || self.quote_input.context_root != self.purchased_output.context_root
            || self.quote_input.selected_pool_id != self.purchased_output.selected_pool_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot private ports exact role pair",
            ));
        }
        Ok(())
    }

    pub fn ports_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            quote_input: CanonicalFlowV1<'a>,
            purchased_output: CanonicalFlowV1<'a>,
            quote_input_flow_id: RootV1,
            purchased_output_flow_id: RootV1,
        }
        hash_global_v1(
            "zdex-spot-private-ports-v1",
            &Canonical {
                schema: ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V1,
                quote_input: canonical_flow_v1(&self.quote_input),
                purchased_output: canonical_flow_v1(&self.purchased_output),
                quote_input_flow_id: self.quote_input.flow_id()?,
                purchased_output_flow_id: self.purchased_output.flow_id()?,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotTerminalObligationV1 {
    pub context_root: RootV1,
    pub post_state_root: RootV1,
    pub consumer_module_release_id: RootV1,
    pub burn_asset: RootV1,
    pub burn_principal: String,
    pub selected_pool_id: RootV1,
    pub quote_input_flow_id: RootV1,
    pub purchased_output_flow_id: RootV1,
    pub purchased_atoms: u128,
}

impl ZDEXSpotTerminalObligationV1 {
    pub fn obligation_id(&self) -> AbiResultV1<RootV1> {
        for root in [
            &self.context_root,
            &self.post_state_root,
            &self.consumer_module_release_id,
            &self.burn_asset,
            &self.selected_pool_id,
            &self.quote_input_flow_id,
            &self.purchased_output_flow_id,
        ] {
            root.validate("Spot terminal root", false)?;
        }
        validate_token_v1(&self.burn_principal, "Spot terminal burn principal")?;
        if self.purchased_atoms == 0 || self.purchased_atoms > MAX_DELTA_ATOMS_V1 {
            return Err(AbiErrorV1::InvalidBounds("Spot terminal amount"));
        }
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            kind: &'static str,
            burn_domain: &'static str,
            context_root: &'a RootV1,
            post_state_root: &'a RootV1,
            consumer_module_release_id: &'a RootV1,
            burn_asset: &'a RootV1,
            burn_principal: &'a str,
            selected_pool_id: &'a RootV1,
            quote_input_flow_id: &'a RootV1,
            purchased_output_flow_id: &'a RootV1,
            purchased_atoms: u128,
        }
        hash_global_v1(
            "zdex-spot-terminal-obligation-v1",
            &Canonical {
                schema: ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V1,
                kind: "MUST_BURN_PURCHASED_ZDEX",
                burn_domain: "ZDEX_TOKEN_SUPPLY",
                context_root: &self.context_root,
                post_state_root: &self.post_state_root,
                consumer_module_release_id: &self.consumer_module_release_id,
                burn_asset: &self.burn_asset,
                burn_principal: &self.burn_principal,
                selected_pool_id: &self.selected_pool_id,
                quote_input_flow_id: &self.quote_input_flow_id,
                purchased_output_flow_id: &self.purchased_output_flow_id,
                purchased_atoms: self.purchased_atoms,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXSpotBuybackJournalV1 {
    pub context_root: RootV1,
    pub post_state_root: RootV1,
    pub effect_plan_root: RootV1,
    pub private_ports_root: RootV1,
    pub terminal_obligation_id: RootV1,
    pub selected_pool_id: RootV1,
    pub pool_definition_root: RootV1,
    pub quote_input_atoms: u128,
    pub fee_atoms: u128,
    pub net_input_atoms: u128,
    pub purchased_zdex_atoms: u128,
    pub route_safe_quote_limit_atoms: u128,
    pub minimum_output_atoms: u128,
    pub pre_quote_reserve_atoms: u128,
    pub post_quote_reserve_atoms: u128,
    pub pre_zdex_reserve_atoms: u128,
    pub post_zdex_reserve_atoms: u128,
}

impl ZDEXSpotBuybackJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.context_root,
            &self.post_state_root,
            &self.effect_plan_root,
            &self.private_ports_root,
            &self.terminal_obligation_id,
            &self.selected_pool_id,
            &self.pool_definition_root,
        ] {
            root.validate("Spot journal root", false)?;
        }
        if self.quote_input_atoms == 0
            || self.purchased_zdex_atoms == 0
            || self.quote_input_atoms.checked_sub(self.fee_atoms) != Some(self.net_input_atoms)
            || self
                .pre_quote_reserve_atoms
                .checked_add(self.quote_input_atoms)
                != Some(self.post_quote_reserve_atoms)
            || self
                .post_zdex_reserve_atoms
                .checked_add(self.purchased_zdex_atoms)
                != Some(self.pre_zdex_reserve_atoms)
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot journal accounting projection",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            context_root: &'a RootV1,
            post_state_root: &'a RootV1,
            effect_plan_root: &'a RootV1,
            private_ports_root: &'a RootV1,
            terminal_obligation_id: &'a RootV1,
            selected_pool_id: &'a RootV1,
            pool_definition_root: &'a RootV1,
            quote_input_atoms: u128,
            fee_atoms: u128,
            net_input_atoms: u128,
            purchased_zdex_atoms: u128,
            route_safe_quote_limit_atoms: u128,
            minimum_output_atoms: u128,
            pre_quote_reserve_atoms: u128,
            post_quote_reserve_atoms: u128,
            pre_zdex_reserve_atoms: u128,
            post_zdex_reserve_atoms: u128,
        }
        hash_global_v1(
            "zdex-spot-buyback-transition-journal-v1",
            &Canonical {
                schema: ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V1,
                context_root: &self.context_root,
                post_state_root: &self.post_state_root,
                effect_plan_root: &self.effect_plan_root,
                private_ports_root: &self.private_ports_root,
                terminal_obligation_id: &self.terminal_obligation_id,
                selected_pool_id: &self.selected_pool_id,
                pool_definition_root: &self.pool_definition_root,
                quote_input_atoms: self.quote_input_atoms,
                fee_atoms: self.fee_atoms,
                net_input_atoms: self.net_input_atoms,
                purchased_zdex_atoms: self.purchased_zdex_atoms,
                route_safe_quote_limit_atoms: self.route_safe_quote_limit_atoms,
                minimum_output_atoms: self.minimum_output_atoms,
                pre_quote_reserve_atoms: self.pre_quote_reserve_atoms,
                post_quote_reserve_atoms: self.post_quote_reserve_atoms,
                pre_zdex_reserve_atoms: self.pre_zdex_reserve_atoms,
                post_zdex_reserve_atoms: self.post_zdex_reserve_atoms,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackRejectedV1 {
    code: ZDEXSpotBuybackRejectCodeV1,
    pre_state: ZDEXSpotLaneStateV1,
    post_state: ZDEXSpotLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXSpotBuybackRejectedV1 {
    pub fn code(&self) -> ZDEXSpotBuybackRejectCodeV1 {
        self.code
    }

    pub fn pre_state(&self) -> &ZDEXSpotLaneStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSpotLaneStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate_wire()?;
        self.post_state.validate_wire()?;
        self.effects.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot buyback reject is exact no-op",
            ));
        }
        Ok(())
    }
}

/// Private accepted fields prevent callers from fabricating a successful
/// transition. The wrapper remains SHADOW evidence and is not a receipt.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackAcceptedV1 {
    pre_state: ZDEXSpotLaneStateV1,
    post_state: ZDEXSpotLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    ports: ZDEXSpotPrivatePortsV1,
    journal: ZDEXSpotBuybackJournalV1,
    terminal_obligation: ZDEXSpotTerminalObligationV1,
    price_safety: VerifiedZDEXBuybackPriceSafetyV1,
}

impl ZDEXSpotBuybackAcceptedV1 {
    pub fn pre_state(&self) -> &ZDEXSpotLaneStateV1 {
        &self.pre_state
    }

    pub fn post_state(&self) -> &ZDEXSpotLaneStateV1 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effects
    }

    pub fn ports(&self) -> &ZDEXSpotPrivatePortsV1 {
        &self.ports
    }

    pub fn journal(&self) -> &ZDEXSpotBuybackJournalV1 {
        &self.journal
    }

    pub fn terminal_obligation(&self) -> &ZDEXSpotTerminalObligationV1 {
        &self.terminal_obligation
    }

    pub fn price_safety(&self) -> &VerifiedZDEXBuybackPriceSafetyV1 {
        &self.price_safety
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate_wire()?;
        self.post_state.validate_wire()?;
        self.effects.validate()?;
        self.journal.validate()?;
        self.ports.validate()?;
        let pre_root = self.pre_state.state_root()?;
        let post_root = self.post_state.state_root()?;
        let effects_root = self.effects.effect_plan_root()?;
        let ports_root = self.ports.ports_root()?;
        let terminal_id = self.terminal_obligation.obligation_id()?;
        let quote_flow_id = self.ports.quote_input.flow_id()?;
        let purchased_flow_id = self.ports.purchased_output.flow_id()?;
        let quote_delta = i128::try_from(self.ports.quote_input.amount_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("Spot quote flow effect width"))?;
        let purchased_delta = i128::try_from(self.ports.purchased_output.amount_atoms)
            .map_err(|_| AbiErrorV1::InvalidBounds("Spot purchased flow effect width"))?;
        let lane_write_matches = self.effects.lane_writes.len() == 1
            && self.effects.lane_writes[0].lane_id == LaneIdV1::SPOT_LIQUIDITY
            && self.effects.lane_writes[0].pre_root == pre_root
            && self.effects.lane_writes[0].post_root == post_root;
        let quote_effect_matches = self.effects.rows.iter().any(|row| {
            row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT
                && row.principal == self.ports.quote_input.destination_principal
                && row.asset == self.ports.quote_input.asset.to_string()
                && row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
                && row.delta_atoms == quote_delta
        });
        let purchased_effect_matches = self.effects.rows.iter().any(|row| {
            row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT
                && row.principal == self.ports.purchased_output.source_principal
                && row.asset == self.ports.purchased_output.asset.to_string()
                && row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
                && row.delta_atoms == -purchased_delta
        });
        if pre_root == post_root
            || self.effects.is_empty()
            || self.effects.rows.len() != 2
            || !self.effects.asset_conservation.is_empty()
            || !self.effects.fee_conservation.is_empty()
            || !self.effects.occurrence_consumptions.is_empty()
            || !self.effects.external_outbox_enqueue.is_empty()
            || !lane_write_matches
            || !quote_effect_matches
            || !purchased_effect_matches
            || self.journal.post_state_root != post_root
            || self.journal.effect_plan_root != effects_root
            || self.journal.private_ports_root != ports_root
            || self.journal.terminal_obligation_id != terminal_id
            || self.journal.quote_input_atoms != self.ports.quote_input.amount_atoms
            || self.journal.purchased_zdex_atoms != self.ports.purchased_output.amount_atoms
            || self.ports.quote_input.role != ZDEXSpotFlowRoleV1::QUOTE_INPUT
            || self.ports.purchased_output.role != ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT
            || self.ports.quote_input.context_root != self.journal.context_root
            || self.ports.purchased_output.context_root != self.journal.context_root
            || self.ports.quote_input.selected_pool_id != self.journal.selected_pool_id
            || self.ports.purchased_output.selected_pool_id != self.journal.selected_pool_id
            || self.terminal_obligation.context_root != self.journal.context_root
            || self.terminal_obligation.post_state_root != post_root
            || self.terminal_obligation.selected_pool_id != self.journal.selected_pool_id
            || self.terminal_obligation.quote_input_flow_id != quote_flow_id
            || self.terminal_obligation.purchased_output_flow_id != purchased_flow_id
            || self.terminal_obligation.purchased_atoms != self.journal.purchased_zdex_atoms
            || self.terminal_obligation.burn_asset != self.ports.purchased_output.asset
            || self.terminal_obligation.burn_principal
                != self.ports.purchased_output.destination_principal
            || self.price_safety.route_safe_quote_limit_atoms()
                != self.journal.route_safe_quote_limit_atoms
            || self.price_safety.minimum_output_atoms() != self.journal.minimum_output_atoms
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot buyback accepted projection binding",
            ));
        }
        Ok(())
    }
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXSpotBuybackResultV1 {
    Accepted(Box<ZDEXSpotBuybackAcceptedV1>),
    Rejected(Box<ZDEXSpotBuybackRejectedV1>),
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
    code: ZDEXSpotBuybackRejectCodeV1,
    state: &ZDEXSpotLaneStateV1,
) -> ZDEXSpotBuybackResultV1 {
    let rejected = ZDEXSpotBuybackRejectedV1 {
        code,
        pre_state: state.clone(),
        post_state: state.clone(),
        effects: empty_effect_plan_v1(),
    };
    ZDEXSpotBuybackResultV1::Rejected(Box::new(rejected))
}

fn checked_product_v1(values: &[u128]) -> Option<u128> {
    values
        .iter()
        .try_fold(1_u128, |product, value| product.checked_mul(*value))
}

fn fee_atoms_v1(gross: u128, fee_bps: u128) -> Option<u128> {
    let product = checked_product_v1(&[gross, fee_bps])?;
    product
        .checked_add(BASIS_POINTS_V1 - 1)
        .map(|value| value / BASIS_POINTS_V1)
}

fn active_or_drain_v1(status: ReleaseStatusV1) -> bool {
    matches!(
        status,
        ReleaseStatusV1::ACTIVE_NEW | ReleaseStatusV1::DRAIN_ONLY
    )
}

fn pool_static_well_formed_v1(release: &ZDEXSpotBuybackReleaseV1, pool: &ZDEXSpotPoolV1) -> bool {
    let definition = &pool.definition;
    let definition_id = definition.pool_id();
    if definition_id.as_ref() != Ok(&pool.pool_id)
        || definition.asset0 >= definition.asset1
        || definition.fee_bps > BASIS_POINTS_V1
        || !release.pool_creation_releases.iter().any(|row| {
            row.module_release_id == pool.creation_release_id && active_or_drain_v1(row.status)
        })
    {
        return false;
    }
    match definition.curve_kind {
        ZDEXSpotCurveKindV1::CPMM_V8_EXACT_IN => {
            definition.curve_release_id == release.cpmm_curve_release_id
                && definition.curve_params_root.as_str() == ZERO_ROOT_V1
        }
        ZDEXSpotCurveKindV1::REGISTERED_OTHER => {
            definition.curve_params_root.as_str() != ZERO_ROOT_V1
                && release.registered_sibling_curve_releases.iter().any(|row| {
                    row.release_id == definition.curve_release_id && active_or_drain_v1(row.status)
                })
        }
    }
}

fn pool_well_formed_v1(release: &ZDEXSpotBuybackReleaseV1, pool: &ZDEXSpotPoolV1) -> bool {
    pool_static_well_formed_v1(release, pool)
        && [
            pool.reserve0_atoms,
            pool.reserve1_atoms,
            pool.lp_supply_atoms,
        ]
        .iter()
        .all(|value| *value <= release.reserve_cap_atoms)
        && (pool.status != ZDEXSpotPoolStatusV1::ACTIVE
            || [
                pool.reserve0_atoms,
                pool.reserve1_atoms,
                pool.lp_supply_atoms,
            ]
            .iter()
            .all(|value| *value > 0))
}

fn lane_well_formed_v1(release: &ZDEXSpotBuybackReleaseV1, state: &ZDEXSpotLaneStateV1) -> bool {
    let Some(pool_count_cap) = release.pool_count_cap() else {
        return false;
    };
    !state.pools.is_empty()
        && state.pools.len() <= pool_count_cap
        && state
            .pools
            .windows(2)
            .all(|pair| pair[0].pool_id < pair[1].pool_id)
        && state
            .pools
            .iter()
            .all(|pool| pool_well_formed_v1(release, pool))
}

fn price_arithmetic_fits_v1(
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    pool: &ZDEXSpotPoolV1,
    gross: u128,
    fee: u128,
    net: u128,
    purchased: u128,
    envelope: &ZDEXSpotPriceEnvelopeV1,
) -> bool {
    let policy = &authority.price_policy;
    let pool_oracle_quote =
        checked_product_v1(&[pool.reserve0_atoms, envelope.oracle_zdex_denominator_atoms]);
    let pool_oracle_zdex =
        checked_product_v1(&[pool.reserve1_atoms, envelope.oracle_quote_numerator_atoms]);
    let pool_oracle_difference = match (pool_oracle_quote, pool_oracle_zdex) {
        (Some(quote), Some(zdex)) => Some(quote.abs_diff(zdex)),
        _ => None,
    };
    let products = [
        checked_product_v1(&[gross, pool.definition.fee_bps]),
        checked_product_v1(&[pool.reserve1_atoms, net]),
        checked_product_v1(&[
            pool.reserve0_atoms,
            u128::from(policy.maximum_quote_reserve_spend_bps),
        ]),
        checked_product_v1(&[gross, envelope.oracle_zdex_denominator_atoms]),
        checked_product_v1(&[
            gross,
            envelope.oracle_zdex_denominator_atoms,
            BASIS_POINTS_V1,
        ]),
        checked_product_v1(&[
            envelope.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_oracle_execution_deviation_bps),
        ]),
        pool_oracle_quote,
        pool_oracle_zdex,
        pool_oracle_difference
            .and_then(|difference| checked_product_v1(&[difference, BASIS_POINTS_V1])),
        checked_product_v1(&[
            pool.reserve1_atoms,
            envelope.oracle_quote_numerator_atoms,
            u128::from(policy.maximum_pool_oracle_deviation_bps),
        ]),
        checked_product_v1(&[gross, pool.reserve1_atoms, BASIS_POINTS_V1]),
        checked_product_v1(&[
            purchased,
            pool.reserve0_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_execution_impact_bps),
        ]),
        checked_product_v1(&[
            purchased,
            envelope.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + u128::from(policy.maximum_oracle_execution_deviation_bps),
        ]),
    ];
    fee.checked_add(net) == Some(gross)
        && pool.reserve0_atoms.checked_add(net).is_some()
        && gross <= MAX_DELTA_ATOMS_V1
        && purchased <= MAX_DELTA_ATOMS_V1
        && products.iter().all(Option::is_some)
}

fn context_root_v1(
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    quote_port: &ZDEXSpotQuoteInputPortV1,
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
        spot_pre_state_root: &'a RootV1,
        writer_epoch: u64,
        current_height: u64,
        spot_module_release_id: &'a RootV1,
        tokenomics_module_release_id: &'a RootV1,
        release_root: RootV1,
        execution_policy_root: RootV1,
        price_policy_root: RootV1,
        oracle_registry_root: RootV1,
        oracle_occurrence_id: RootV1,
        tokenomics_source_pre_state_root: &'a RootV1,
        tokenomics_source_post_state_root: &'a RootV1,
        tokenomics_source_effect_plan_root: &'a RootV1,
        tokenomics_source_journal_root: &'a RootV1,
        tokenomics_source_receipt_binding_root: &'a RootV1,
    }
    hash_global_v1(
        "zdex-spot-buyback-transition-context-v1",
        &Canonical {
            chain_id: &authority.chain_id,
            deployment_root: &authority.deployment_root,
            profile_root: &authority.profile_root,
            profile_authorization_root: &authority.profile_authorization_root,
            route_release_id: &authority.route_release_id,
            command_occurrence_id: &authority.command_occurrence_id,
            global_pre_state_root: &authority.global_pre_state_root,
            spot_pre_state_root: &authority.spot_pre_state_root,
            writer_epoch: authority.writer_epoch,
            current_height: authority.current_height,
            spot_module_release_id: &authority.spot_module_release_id,
            tokenomics_module_release_id: &authority.tokenomics_module_release_id,
            release_root: authority.release.release_root()?,
            execution_policy_root: authority.execution_policy.policy_root()?,
            price_policy_root: authority.price_policy.policy_root()?,
            oracle_registry_root: authority.oracle_registry.registry_root()?,
            oracle_occurrence_id: authority.oracle_occurrence.occurrence_id()?,
            tokenomics_source_pre_state_root: &quote_port.source_pre_state_root,
            tokenomics_source_post_state_root: &quote_port.source_post_state_root,
            tokenomics_source_effect_plan_root: &quote_port.source_effect_plan_root,
            tokenomics_source_journal_root: &quote_port.source_journal_root,
            tokenomics_source_receipt_binding_root: &quote_port.source_receipt_binding_root,
        },
    )
}

fn profile_matches_v1(authority: &ZDEXSpotBuybackAuthorityContextV1) -> bool {
    let profile = &authority.profile_authorization;
    let Ok(profile_root) = profile.authorization_root() else {
        return false;
    };
    let Ok(release_root) = authority.release.release_root() else {
        return false;
    };
    let Ok(execution_policy_root) = authority.execution_policy.policy_root() else {
        return false;
    };
    let Ok(price_policy_root) = authority.price_policy.policy_root() else {
        return false;
    };
    authority.profile_authorization_root == profile_root
        && profile.profile_root == authority.profile_root
        && profile.chain_id == authority.chain_id
        && profile.deployment_root == authority.deployment_root
        && profile.route_release_id == authority.route_release_id
        && profile.spot_module_release_id == authority.spot_module_release_id
        && profile.tokenomics_module_release_id == authority.tokenomics_module_release_id
        && profile.oracle_id == authority.price_policy.oracle_id
        && profile.release_root == release_root
        && profile.execution_policy_root == execution_policy_root
        && profile.price_policy_root == price_policy_root
}

fn oracle_matches_v1(authority: &ZDEXSpotBuybackAuthorityContextV1) -> bool {
    let registry = &authority.oracle_registry;
    let ids = registry
        .occurrences
        .iter()
        .map(ZDEXSpotOracleOccurrenceV1::occurrence_id)
        .collect::<Result<Vec<_>, _>>();
    let Ok(ids) = ids else {
        return false;
    };
    let Ok(registry_root) = registry.registry_root() else {
        return false;
    };
    let oracle = &authority.oracle_occurrence;
    !ids.is_empty()
        && ids.windows(2).all(|pair| pair[0] < pair[1])
        && !registry_root.is_zero()
        && registry.occurrences.iter().any(|item| item == oracle)
        && oracle.status == ZDEXSpotOracleStatusV1::FINAL
        && oracle.price.oracle_id == authority.price_policy.oracle_id
        && oracle.price.quote_asset_id == authority.execution_policy.quote_asset_id
        && oracle.price.zdex_asset_id == authority.execution_policy.zdex_asset_id
        && registry.occurrences.iter().all(|item| {
            item.status == ZDEXSpotOracleStatusV1::FINAL
                && item.price.oracle_id == authority.price_policy.oracle_id
        })
}

fn price_subject_matches_v1(
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    quote: &ZDEXSpotQuoteInputPortV1,
    envelope: &ZDEXSpotPriceEnvelopeV1,
) -> bool {
    let Ok(occurrence_id) = authority.oracle_occurrence.occurrence_id() else {
        return false;
    };
    envelope.profile_root == authority.profile_root
        && envelope.route_release_id == authority.route_release_id
        && envelope.command_occurrence_id == authority.command_occurrence_id
        && envelope.global_pre_state_root == authority.global_pre_state_root
        && envelope.spot_pre_state_root == authority.spot_pre_state_root
        && envelope.selected_pool_id == authority.execution_policy.pool_id
        && envelope.oracle_occurrence_id == occurrence_id
        && envelope.oracle_finality_root == authority.oracle_occurrence.finality_root
        && envelope.quote_amount_atoms == quote.amount_atoms
        && envelope.current_height == authority.current_height
        && envelope.oracle_observed_height == authority.oracle_occurrence.price.observed_height
        && envelope.oracle_quote_numerator_atoms
            == authority.oracle_occurrence.price.quote_numerator_atoms
        && envelope.oracle_zdex_denominator_atoms
            == authority.oracle_occurrence.price.zdex_denominator_atoms
}

fn policy_matches_v1(authority: &ZDEXSpotBuybackAuthorityContextV1) -> bool {
    let expected = &authority.expected_pool_definition;
    let Ok(expected_pool_id) = expected.pool_id() else {
        return false;
    };
    let Ok(expected_root) = expected.definition_root() else {
        return false;
    };
    authority.execution_policy.pool_id == expected_pool_id
        && authority.execution_policy.pool_definition_root == expected_root
        && expected.asset0 == authority.execution_policy.quote_asset_id
        && expected.asset1 == authority.execution_policy.zdex_asset_id
        && authority.execution_policy.quote_asset_id < authority.execution_policy.zdex_asset_id
        && expected.curve_kind == ZDEXSpotCurveKindV1::CPMM_V8_EXACT_IN
        && expected.curve_release_id == authority.release.cpmm_curve_release_id
        && expected.curve_params_root.as_str() == ZERO_ROOT_V1
}

/// Execute the bounded Spot-owned transition using the proved guard order.
///
/// The caller cannot select a pool or an output: the active pool comes from
/// the governed execution-policy ID and all output/effects/ports are derived.
/// A rejection returns the exact pre-state value plus an empty effect plan.
pub fn transition_zdex_spot_buyback_v1(
    candidate: &ZDEXSpotBuybackInputV1,
) -> AbiResultV1<ZDEXSpotBuybackResultV1> {
    let pre_state = &candidate.pre_state;
    let authority = match &candidate.authority {
        ZDEXSpotBuybackAuthorityInputV1::CONTEXT(authority)
            if authority.validate_wire().is_ok() =>
        {
            authority
        }
        ZDEXSpotBuybackAuthorityInputV1::CONTEXT(_)
        | ZDEXSpotBuybackAuthorityInputV1::MALFORMED => {
            return Ok(reject_v1(
                ZDEXSpotBuybackRejectCodeV1::AUTHORITY_MALFORMED,
                pre_state,
            ));
        }
    };
    let release = &authority.release;
    let policy = &authority.execution_policy;
    let price_policy = &authority.price_policy;
    let oracle = &authority.oracle_occurrence;
    let quote = &candidate.quote_port;
    let envelope = &candidate.price_envelope;

    if !release.is_bounded_v1()
        || authority.route_release_id != release.route_release_id
        || authority.spot_module_release_id != release.spot_module_release_id
        || authority.tokenomics_module_release_id != release.tokenomics_module_release_id
    {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::RELEASE_MISMATCH,
            pre_state,
        ));
    }
    if !profile_matches_v1(authority) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::PROFILE_MISMATCH,
            pre_state,
        ));
    }
    if authority.spot_pre_state_root != pre_state.state_root()? {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH,
            pre_state,
        ));
    }
    if quote.validate().is_err()
        || quote.profile_root != authority.profile_root
        || quote.route_release_id != authority.route_release_id
        || quote.command_occurrence_id != authority.command_occurrence_id
        || quote.global_pre_state_root != authority.global_pre_state_root
        || quote.spot_pre_state_root != authority.spot_pre_state_root
        || quote.source_module_release_id != authority.tokenomics_module_release_id
        || quote.destination_module_release_id != authority.spot_module_release_id
        || quote.source_pre_state_root == quote.source_post_state_root
    {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::QUOTE_PORT_MISMATCH,
            pre_state,
        ));
    }
    if !oracle_matches_v1(authority) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::ORACLE_MISMATCH,
            pre_state,
        ));
    }
    if envelope.validate().is_err() || !price_subject_matches_v1(authority, quote, envelope) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::PRICE_SUBJECT_MISMATCH,
            pre_state,
        ));
    }
    if !policy_matches_v1(authority) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::POLICY_MISMATCH,
            pre_state,
        ));
    }
    if !lane_well_formed_v1(release, pre_state) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::LANE_MALFORMED,
            pre_state,
        ));
    }
    let selected_rows = pre_state
        .pools
        .iter()
        .enumerate()
        .filter(|(_, pool)| pool.pool_id == policy.pool_id)
        .collect::<Vec<_>>();
    if selected_rows.len() != 1 {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::SELECTION_MISMATCH,
            pre_state,
        ));
    }
    let (selected_index, selected) = selected_rows[0];
    if selected.definition != authority.expected_pool_definition {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::SELECTION_MISMATCH,
            pre_state,
        ));
    }
    if selected.status != ZDEXSpotPoolStatusV1::ACTIVE {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::POOL_INACTIVE,
            pre_state,
        ));
    }

    let gross = quote.amount_atoms;
    let exceeds_reserve_cap = release
        .reserve_cap_atoms
        .checked_sub(gross)
        .is_none_or(|limit| selected.reserve0_atoms > limit);
    if gross == 0 || gross > release.swap_cap_atoms || exceeds_reserve_cap {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::AMOUNT_OUT_OF_RANGE,
            pre_state,
        ));
    }
    let Some(fee) = fee_atoms_v1(gross, selected.definition.fee_bps) else {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::ARITHMETIC_OUT_OF_RANGE,
            pre_state,
        ));
    };
    let net = gross.saturating_sub(fee);
    let denominator = selected.reserve0_atoms.checked_add(net).unwrap_or(0);
    let output_product = checked_product_v1(&[selected.reserve1_atoms, net]);
    let purchased = match (output_product, denominator) {
        (Some(product), nonzero) if nonzero != 0 => product / nonzero,
        _ => 0,
    };
    if !price_arithmetic_fits_v1(authority, selected, gross, fee, net, purchased, envelope) {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::ARITHMETIC_OUT_OF_RANGE,
            pre_state,
        ));
    }
    if fee >= gross {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::FEE_CONSUMES_INPUT,
            pre_state,
        ));
    }
    if purchased == 0 {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::ZERO_OUTPUT,
            pre_state,
        ));
    }
    if envelope.minimum_output_atoms == 0 || envelope.minimum_output_atoms > purchased {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH,
            pre_state,
        ));
    }
    if envelope.claimed_route_safe_quote_limit_atoms == 0 {
        return Ok(reject_v1(
            ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE,
            pre_state,
        ));
    }

    let price_observation = ZDEXBuybackPriceSafetyObservationV1 {
        schema: ZDEX_BUYBACK_PRICE_SAFETY_OBSERVATION_SCHEMA_V1.to_owned(),
        oracle_occurrence_root: oracle.price.occurrence_root()?,
        current_height: envelope.current_height,
        oracle_observed_height: envelope.oracle_observed_height,
        oracle_quote_numerator_atoms: envelope.oracle_quote_numerator_atoms,
        oracle_zdex_denominator_atoms: envelope.oracle_zdex_denominator_atoms,
        quote_reserve_atoms: selected.reserve0_atoms,
        zdex_reserve_atoms: selected.reserve1_atoms,
        quote_amount_in_atoms: gross,
        purchased_zdex_atoms: purchased,
        claimed_route_safe_quote_limit_atoms: envelope.claimed_route_safe_quote_limit_atoms,
        claimed_minimum_output_atoms: envelope.minimum_output_atoms,
    };
    let price_safety = match verify_zdex_buyback_price_safety_v1(price_policy, &price_observation)?
    {
        ZDEXBuybackPriceSafetyResultV1::Accepted(verified) => verified,
        ZDEXBuybackPriceSafetyResultV1::Rejected(
            ZDEXBuybackPriceSafetyRejectCodeV1::DERIVED_MINIMUM_OUTPUT_MISMATCH,
        ) => {
            return Ok(reject_v1(
                ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH,
                pre_state,
            ));
        }
        ZDEXBuybackPriceSafetyResultV1::Rejected(_) => {
            return Ok(reject_v1(
                ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE,
                pre_state,
            ));
        }
    };

    let post_reserve0 = selected
        .reserve0_atoms
        .checked_add(gross)
        .ok_or(AbiErrorV1::InvalidBounds("Spot post quote reserve"))?;
    let post_reserve1 = selected
        .reserve1_atoms
        .checked_sub(purchased)
        .ok_or(AbiErrorV1::InvalidBounds("Spot post ZDEX reserve"))?;
    let updated = ZDEXSpotPoolV1 {
        pool_id: selected.pool_id.clone(),
        definition: selected.definition.clone(),
        reserve0_atoms: post_reserve0,
        reserve1_atoms: post_reserve1,
        lp_supply_atoms: selected.lp_supply_atoms,
        status: selected.status,
        creation_release_id: selected.creation_release_id.clone(),
        created_height: selected.created_height,
    };
    let mut post_pools = pre_state.pools.clone();
    post_pools[selected_index] = updated.clone();
    let post_state = ZDEXSpotLaneStateV1 {
        pools: post_pools,
        lp_ownership_root: pre_state.lp_ownership_root.clone(),
        route_batch_root: pre_state.route_batch_root.clone(),
        fee_residue_root: pre_state.fee_residue_root.clone(),
        pool_terminal_obligations_root: pre_state.pool_terminal_obligations_root.clone(),
    };
    let quote_pool = zdex_pool_reserve_principal_v1(&selected.pool_id, &policy.quote_asset_id)?;
    let zdex_pool = zdex_pool_reserve_principal_v1(&selected.pool_id, &policy.zdex_asset_id)?;
    let burn_principal = zdex_occurrence_burn_port_v1(
        &authority.profile_root,
        &authority.route_release_id,
        &authority.command_occurrence_id,
    )?;
    let gross_delta =
        i128::try_from(gross).map_err(|_| AbiErrorV1::InvalidBounds("Spot quote effect width"))?;
    let purchased_delta = i128::try_from(purchased)
        .map_err(|_| AbiErrorV1::InvalidBounds("Spot ZDEX effect width"))?;
    let effects = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                principal: quote_pool.clone(),
                asset: policy.quote_asset_id.to_string(),
                custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: gross_delta,
            },
            EconomicEffectRowV1 {
                kind: EconomicEffectKindV1::ACCOUNT_MOVEMENT,
                principal: zdex_pool.clone(),
                asset: policy.zdex_asset_id.to_string(),
                custody_domain: AMM_POOL_CUSTODY_DOMAIN_V1.to_owned(),
                delta_atoms: -purchased_delta,
            },
        ],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::SPOT_LIQUIDITY,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    };
    effects.validate()?;
    let context_root = context_root_v1(authority, quote)?;
    let quote_flow = ZDEXSpotFlowIdentityV1 {
        role: ZDEXSpotFlowRoleV1::QUOTE_INPUT,
        context_root: context_root.clone(),
        selected_pool_id: selected.pool_id.clone(),
        asset: policy.quote_asset_id.clone(),
        source_principal: FEE_BUYBACK_PRINCIPAL_V1.to_owned(),
        destination_principal: quote_pool,
        amount_atoms: gross,
    };
    let purchased_flow = ZDEXSpotFlowIdentityV1 {
        role: ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
        context_root: context_root.clone(),
        selected_pool_id: selected.pool_id.clone(),
        asset: policy.zdex_asset_id.clone(),
        source_principal: zdex_pool,
        destination_principal: burn_principal.clone(),
        amount_atoms: purchased,
    };
    let ports = ZDEXSpotPrivatePortsV1 {
        quote_input: quote_flow,
        purchased_output: purchased_flow,
    };
    let terminal_obligation = ZDEXSpotTerminalObligationV1 {
        context_root: context_root.clone(),
        post_state_root: post_state.state_root()?,
        consumer_module_release_id: authority.tokenomics_module_release_id.clone(),
        burn_asset: policy.zdex_asset_id.clone(),
        burn_principal,
        selected_pool_id: selected.pool_id.clone(),
        quote_input_flow_id: ports.quote_input.flow_id()?,
        purchased_output_flow_id: ports.purchased_output.flow_id()?,
        purchased_atoms: purchased,
    };
    let journal = ZDEXSpotBuybackJournalV1 {
        context_root,
        post_state_root: post_state.state_root()?,
        effect_plan_root: effects.effect_plan_root()?,
        private_ports_root: ports.ports_root()?,
        terminal_obligation_id: terminal_obligation.obligation_id()?,
        selected_pool_id: selected.pool_id.clone(),
        pool_definition_root: selected.definition.definition_root()?,
        quote_input_atoms: gross,
        fee_atoms: fee,
        net_input_atoms: net,
        purchased_zdex_atoms: purchased,
        route_safe_quote_limit_atoms: envelope.claimed_route_safe_quote_limit_atoms,
        minimum_output_atoms: envelope.minimum_output_atoms,
        pre_quote_reserve_atoms: selected.reserve0_atoms,
        post_quote_reserve_atoms: updated.reserve0_atoms,
        pre_zdex_reserve_atoms: selected.reserve1_atoms,
        post_zdex_reserve_atoms: updated.reserve1_atoms,
    };
    let accepted = ZDEXSpotBuybackAcceptedV1 {
        pre_state: pre_state.clone(),
        post_state,
        effects,
        ports,
        journal,
        terminal_obligation,
        price_safety,
    };
    accepted.validate()?;
    Ok(ZDEXSpotBuybackResultV1::Accepted(Box::new(accepted)))
}
