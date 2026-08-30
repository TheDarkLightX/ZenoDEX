//! SHADOW-only successor for the source-pinned Spot buyback V2 schema.
//!
//! V2 commits the acyclic quote port directly.  The private V1 view below is
//! limited to the pre-existing, deterministic CPMM/policy kernel; it has no
//! V2-facing receipt or journal field and never leaves this module.  This is
//! a functional core only: it neither verifies a receipt nor applies effects.

use serde::Serialize;

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::zdex_atomic_buyback_quote_port_v2::ZDEXAtomicBuybackQuotePortV2;
use crate::zdex_buyback_price_safety::VerifiedZDEXBuybackPriceSafetyV1;
use crate::zdex_purchase_burn_types::{
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1,
};
use crate::zdex_spot_buyback_transition::{
    transition_zdex_spot_buyback_v1, ZDEXSpotBuybackAcceptedV1, ZDEXSpotBuybackAuthorityContextV1,
    ZDEXSpotBuybackAuthorityInputV1, ZDEXSpotBuybackInputV1, ZDEXSpotBuybackRejectCodeV1,
    ZDEXSpotBuybackResultV1, ZDEXSpotFlowRoleV1, ZDEXSpotLaneStateV1, ZDEXSpotPriceEnvelopeV1,
};

pub const ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2: &str =
    "zenodex/zdex-spot-buyback-coordinates/v2";
pub const ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2: &str =
    "zenodex/zdex-spot-buyback-transition-context/v2";
pub const ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V2: &str = "zenodex/zdex-spot-price-envelope/v2";
pub const ZDEX_SPOT_FLOW_SCHEMA_V2: &str = "zenodex/zdex-spot-buyback-flow/v2";
pub const ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2: &str = "zenodex/zdex-spot-private-ports/v2";
pub const ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2: &str =
    "zenodex/zdex-spot-terminal-obligation/v2";
pub const ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2: &str =
    "zenodex/zdex-spot-buyback-transition-journal/v2";

const MAX_DELTA_ATOMS_V2: u128 = i128::MAX.unsigned_abs();

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotBuybackRejectCodeV2 {
    INPUT_MALFORMED,
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

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ZDEXSpotBuybackAuthorityInputV2 {
    CONTEXT(Box<ZDEXSpotBuybackAuthorityContextV2>),
    MALFORMED,
}

/// V2 retains the frozen V1 policy graph while changing only the cross-lane
/// quote-port commitment shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackAuthorityContextV2 {
    pub stable_authority: ZDEXSpotBuybackAuthorityContextV1,
}

impl ZDEXSpotBuybackAuthorityContextV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        let authority = &self.stable_authority;
        validate_token_v1(&authority.chain_id, "Spot V2 authority chain id")?;
        for root in [
            &authority.deployment_root,
            &authority.profile_root,
            &authority.profile_authorization_root,
            &authority.route_release_id,
            &authority.command_occurrence_id,
            &authority.global_pre_state_root,
            &authority.spot_pre_state_root,
            &authority.spot_module_release_id,
            &authority.tokenomics_module_release_id,
        ] {
            root.validate("Spot V2 authority root", false)?;
        }
        authority.release.validate()?;
        authority.execution_policy.validate()?;
        authority.expected_pool_definition.validate()?;
        authority.price_policy.validate()?;
        authority.profile_authorization.authorization_root()?;
        let mut registry_ids = Vec::with_capacity(authority.oracle_registry.occurrences.len());
        for occurrence in &authority.oracle_registry.occurrences {
            occurrence.price.validate()?;
            occurrence
                .finality_root
                .validate("Spot V2 Oracle finality root", false)?;
            registry_ids.push(occurrence.occurrence_id()?);
        }
        if registry_ids.is_empty() || registry_ids.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(AbiErrorV1::InvalidOrder("Spot V2 Oracle registry"));
        }
        authority.oracle_occurrence.price.validate()?;
        authority
            .oracle_occurrence
            .finality_root
            .validate("Spot V2 selected Oracle finality root", false)?;
        authority.oracle_occurrence.occurrence_id()?;
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackCoordinatesV2 {
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub spot_pre_state_root: RootV1,
    pub producer_quote_pre_state_root: RootV1,
    pub producer_quote_post_state_root: RootV1,
    pub producer_quote_effect_plan_root: RootV1,
    pub quote_port_root: RootV1,
}

impl ZDEXSpotBuybackCoordinatesV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.spot_pre_state_root,
            &self.producer_quote_pre_state_root,
            &self.producer_quote_post_state_root,
            &self.producer_quote_effect_plan_root,
            &self.quote_port_root,
        ] {
            root.validate("Spot V2 coordinates root", false)?;
        }
        if self.producer_quote_pre_state_root == self.producer_quote_post_state_root {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot V2 producer quote phase state transition",
            ));
        }
        Ok(())
    }

    pub fn coordinates_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            "zdex-spot-buyback-coordinates-v2",
            &canonical_coordinates_v2(self),
        )
    }
}

#[derive(Serialize)]
struct CanonicalCoordinatesV2<'a> {
    schema: &'static str,
    profile_root: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    global_pre_state_root: &'a RootV1,
    spot_pre_state_root: &'a RootV1,
    producer_quote_pre_state_root: &'a RootV1,
    producer_quote_post_state_root: &'a RootV1,
    producer_quote_effect_plan_root: &'a RootV1,
    quote_port_root: &'a RootV1,
}

fn canonical_coordinates_v2(value: &ZDEXSpotBuybackCoordinatesV2) -> CanonicalCoordinatesV2<'_> {
    CanonicalCoordinatesV2 {
        schema: ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2,
        profile_root: &value.profile_root,
        route_release_id: &value.route_release_id,
        command_occurrence_id: &value.command_occurrence_id,
        global_pre_state_root: &value.global_pre_state_root,
        spot_pre_state_root: &value.spot_pre_state_root,
        producer_quote_pre_state_root: &value.producer_quote_pre_state_root,
        producer_quote_post_state_root: &value.producer_quote_post_state_root,
        producer_quote_effect_plan_root: &value.producer_quote_effect_plan_root,
        quote_port_root: &value.quote_port_root,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackContextV2 {
    pub coordinates: ZDEXSpotBuybackCoordinatesV2,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_authorization_root: RootV1,
    pub writer_epoch: u64,
    pub current_height: u64,
    pub spot_module_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub release_root: RootV1,
    pub execution_policy_root: RootV1,
    pub price_policy_root: RootV1,
    pub oracle_registry_root: RootV1,
    pub oracle_occurrence_id: RootV1,
}

impl ZDEXSpotBuybackContextV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.coordinates.validate()?;
        validate_token_v1(&self.chain_id, "Spot V2 context chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_authorization_root,
            &self.spot_module_release_id,
            &self.tokenomics_module_release_id,
            &self.release_root,
            &self.execution_policy_root,
            &self.price_policy_root,
            &self.oracle_registry_root,
            &self.oracle_occurrence_id,
        ] {
            root.validate("Spot V2 context root", false)?;
        }
        Ok(())
    }

    pub fn context_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            "zdex-spot-buyback-transition-context-v2",
            &canonical_context_v2(self)?,
        )
    }
}

#[derive(Serialize)]
struct CanonicalContextV2<'a> {
    schema: &'static str,
    coordinates: CanonicalCoordinatesV2<'a>,
    coordinates_root: RootV1,
    quote_port_root: &'a RootV1,
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    profile_authorization_root: &'a RootV1,
    writer_epoch: u64,
    current_height: u64,
    spot_module_release_id: &'a RootV1,
    tokenomics_module_release_id: &'a RootV1,
    release_root: &'a RootV1,
    execution_policy_root: &'a RootV1,
    price_policy_root: &'a RootV1,
    oracle_registry_root: &'a RootV1,
    oracle_occurrence_id: &'a RootV1,
}

fn canonical_context_v2(value: &ZDEXSpotBuybackContextV2) -> AbiResultV1<CanonicalContextV2<'_>> {
    Ok(CanonicalContextV2 {
        schema: ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2,
        coordinates: canonical_coordinates_v2(&value.coordinates),
        coordinates_root: value.coordinates.coordinates_root()?,
        quote_port_root: &value.coordinates.quote_port_root,
        chain_id: &value.chain_id,
        deployment_root: &value.deployment_root,
        profile_authorization_root: &value.profile_authorization_root,
        writer_epoch: value.writer_epoch,
        current_height: value.current_height,
        spot_module_release_id: &value.spot_module_release_id,
        tokenomics_module_release_id: &value.tokenomics_module_release_id,
        release_root: &value.release_root,
        execution_policy_root: &value.execution_policy_root,
        price_policy_root: &value.price_policy_root,
        oracle_registry_root: &value.oracle_registry_root,
        oracle_occurrence_id: &value.oracle_occurrence_id,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotPriceEnvelopeV2 {
    pub coordinates: ZDEXSpotBuybackCoordinatesV2,
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

impl ZDEXSpotPriceEnvelopeV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.coordinates.validate()?;
        for root in [
            &self.selected_pool_id,
            &self.oracle_occurrence_id,
            &self.oracle_finality_root,
        ] {
            root.validate("Spot V2 price-envelope root", false)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackInputV2 {
    pub authority: ZDEXSpotBuybackAuthorityInputV2,
    pub pre_state: ZDEXSpotLaneStateV1,
    pub quote_port: ZDEXAtomicBuybackQuotePortV2,
    pub price_envelope: ZDEXSpotPriceEnvelopeV2,
}

impl ZDEXSpotBuybackInputV2 {
    pub fn validate_payload(&self) -> AbiResultV1<()> {
        deep_validate_lane_state_v2(&self.pre_state)?;
        self.quote_port.validate()?;
        self.price_envelope.validate()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotFlowIdentityV2 {
    pub role: ZDEXSpotFlowRoleV1,
    pub context: ZDEXSpotBuybackContextV2,
    pub selected_pool_id: RootV1,
    pub asset: RootV1,
    pub source_principal: String,
    pub destination_principal: String,
    pub amount_atoms: u128,
}

impl ZDEXSpotFlowIdentityV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        self.selected_pool_id
            .validate("Spot V2 flow pool id", false)?;
        self.asset.validate("Spot V2 flow asset", false)?;
        validate_token_v1(&self.source_principal, "Spot V2 flow source principal")?;
        validate_token_v1(
            &self.destination_principal,
            "Spot V2 flow destination principal",
        )?;
        validate_positive_effect_atoms_v2(self.amount_atoms, "Spot V2 flow amount")
    }

    pub fn flow_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-spot-buyback-flow-v2", &canonical_flow_v2(self)?)
    }
}

#[derive(Serialize)]
struct CanonicalFlowV2<'a> {
    schema: &'static str,
    role: ZDEXSpotFlowRoleV1,
    context_root: RootV1,
    coordinates_root: RootV1,
    quote_port_root: &'a RootV1,
    selected_pool_id: &'a RootV1,
    asset: &'a RootV1,
    source_principal: &'a str,
    destination_principal: &'a str,
    amount_atoms: u128,
}

fn canonical_flow_v2(value: &ZDEXSpotFlowIdentityV2) -> AbiResultV1<CanonicalFlowV2<'_>> {
    Ok(CanonicalFlowV2 {
        schema: ZDEX_SPOT_FLOW_SCHEMA_V2,
        role: value.role,
        context_root: value.context.context_root()?,
        coordinates_root: value.context.coordinates.coordinates_root()?,
        quote_port_root: &value.context.coordinates.quote_port_root,
        selected_pool_id: &value.selected_pool_id,
        asset: &value.asset,
        source_principal: &value.source_principal,
        destination_principal: &value.destination_principal,
        amount_atoms: value.amount_atoms,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotPrivatePortsV2 {
    pub quote_input: ZDEXSpotFlowIdentityV2,
    pub purchased_output: ZDEXSpotFlowIdentityV2,
}

impl ZDEXSpotPrivatePortsV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.quote_input.validate()?;
        self.purchased_output.validate()?;
        if self.quote_input.role != ZDEXSpotFlowRoleV1::QUOTE_INPUT
            || self.purchased_output.role != ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT
            || self.quote_input.context.context_root()?
                != self.purchased_output.context.context_root()?
            || self.quote_input.selected_pool_id != self.purchased_output.selected_pool_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot V2 private ports exact role pair",
            ));
        }
        Ok(())
    }

    pub fn ports_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            context_root: RootV1,
            quote_port_root: &'a RootV1,
            quote_input: CanonicalFlowV2<'a>,
            purchased_output: CanonicalFlowV2<'a>,
            quote_input_flow_id: RootV1,
            purchased_output_flow_id: RootV1,
        }
        hash_global_v1(
            "zdex-spot-private-ports-v2",
            &Canonical {
                schema: ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2,
                context_root: self.quote_input.context.context_root()?,
                quote_port_root: &self.quote_input.context.coordinates.quote_port_root,
                quote_input: canonical_flow_v2(&self.quote_input)?,
                purchased_output: canonical_flow_v2(&self.purchased_output)?,
                quote_input_flow_id: self.quote_input.flow_id()?,
                purchased_output_flow_id: self.purchased_output.flow_id()?,
            },
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotTerminalObligationV2 {
    pub context: ZDEXSpotBuybackContextV2,
    pub post_state_root: RootV1,
    pub consumer_module_release_id: RootV1,
    pub burn_asset: RootV1,
    pub burn_principal: String,
    pub selected_pool_id: RootV1,
    pub quote_input_flow_id: RootV1,
    pub purchased_output_flow_id: RootV1,
    pub purchased_atoms: u128,
}

impl ZDEXSpotTerminalObligationV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        for root in [
            &self.post_state_root,
            &self.consumer_module_release_id,
            &self.burn_asset,
            &self.selected_pool_id,
            &self.quote_input_flow_id,
            &self.purchased_output_flow_id,
        ] {
            root.validate("Spot V2 terminal root", false)?;
        }
        validate_token_v1(&self.burn_principal, "Spot V2 terminal burn principal")?;
        validate_positive_effect_atoms_v2(self.purchased_atoms, "Spot V2 terminal amount")
    }

    pub fn obligation_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            kind: &'static str,
            burn_domain: &'static str,
            context_root: RootV1,
            coordinates_root: RootV1,
            quote_port_root: &'a RootV1,
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
            "zdex-spot-terminal-obligation-v2",
            &Canonical {
                schema: ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
                kind: "MUST_BURN_PURCHASED_ZDEX",
                burn_domain: "ZDEX_TOKEN_SUPPLY",
                context_root: self.context.context_root()?,
                coordinates_root: self.context.coordinates.coordinates_root()?,
                quote_port_root: &self.context.coordinates.quote_port_root,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackJournalV2 {
    pub context: ZDEXSpotBuybackContextV2,
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

impl ZDEXSpotBuybackJournalV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        for root in [
            &self.post_state_root,
            &self.effect_plan_root,
            &self.private_ports_root,
            &self.terminal_obligation_id,
            &self.selected_pool_id,
            &self.pool_definition_root,
        ] {
            root.validate("Spot V2 journal root", false)?;
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
                "Spot V2 journal accounting projection",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct Canonical<'a> {
            schema: &'static str,
            context_root: RootV1,
            coordinates_root: RootV1,
            quote_port_root: &'a RootV1,
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
            "zdex-spot-buyback-transition-journal-v2",
            &Canonical {
                schema: ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2,
                context_root: self.context.context_root()?,
                coordinates_root: self.context.coordinates.coordinates_root()?,
                quote_port_root: &self.context.coordinates.quote_port_root,
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

/// Exact typed V2 no-op.  Every rejection owns a fresh empty plan and carries
/// no successful projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackRejectedV2 {
    code: ZDEXSpotBuybackRejectCodeV2,
    pre_state: ZDEXSpotLaneStateV1,
    post_state: ZDEXSpotLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    context: Option<ZDEXSpotBuybackContextV2>,
    ports: Option<ZDEXSpotPrivatePortsV2>,
    journal: Option<ZDEXSpotBuybackJournalV2>,
    terminal_obligation: Option<ZDEXSpotTerminalObligationV2>,
}

impl ZDEXSpotBuybackRejectedV2 {
    fn new(code: ZDEXSpotBuybackRejectCodeV2, state: &ZDEXSpotLaneStateV1) -> Self {
        Self {
            code,
            pre_state: state.clone(),
            post_state: state.clone(),
            effects: empty_effect_plan_v2(),
            context: None,
            ports: None,
            journal: None,
            terminal_obligation: None,
        }
    }

    pub fn code(&self) -> ZDEXSpotBuybackRejectCodeV2 {
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

    pub fn context(&self) -> Option<&ZDEXSpotBuybackContextV2> {
        self.context.as_ref()
    }

    pub fn ports(&self) -> Option<&ZDEXSpotPrivatePortsV2> {
        self.ports.as_ref()
    }

    pub fn journal(&self) -> Option<&ZDEXSpotBuybackJournalV2> {
        self.journal.as_ref()
    }

    pub fn terminal_obligation(&self) -> Option<&ZDEXSpotTerminalObligationV2> {
        self.terminal_obligation.as_ref()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        deep_validate_lane_state_v2(&self.pre_state)?;
        deep_validate_lane_state_v2(&self.post_state)?;
        self.effects.validate()?;
        if self.pre_state != self.post_state
            || !self.effects.is_empty()
            || self.context.is_some()
            || self.ports.is_some()
            || self.journal.is_some()
            || self.terminal_obligation.is_some()
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot V2 rejection exact no-effect no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ZDEXSpotBuybackAcceptedFieldsV2 {
    pre_state: ZDEXSpotLaneStateV1,
    post_state: ZDEXSpotLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    context: ZDEXSpotBuybackContextV2,
    ports: ZDEXSpotPrivatePortsV2,
    journal: ZDEXSpotBuybackJournalV2,
    terminal_obligation: ZDEXSpotTerminalObligationV2,
    price_safety: VerifiedZDEXBuybackPriceSafetyV1,
}

impl ZDEXSpotBuybackAcceptedFieldsV2 {
    fn validate(&self) -> AbiResultV1<()> {
        let pre_root = deep_validate_lane_state_v2(&self.pre_state)?;
        let post_root = deep_validate_lane_state_v2(&self.post_state)?;
        self.effects.validate()?;
        self.context.validate()?;
        self.ports.validate()?;
        self.journal.validate()?;
        self.terminal_obligation.validate()?;
        if pre_root == post_root
            || self.effects.is_empty()
            || self.journal.context.context_root()? != self.context.context_root()?
            || self.terminal_obligation.context.context_root()? != self.context.context_root()?
            || self.journal.post_state_root != post_root
            || self.journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.journal.private_ports_root != self.ports.ports_root()?
            || self.journal.terminal_obligation_id != self.terminal_obligation.obligation_id()?
            || self.terminal_obligation.post_state_root != post_root
            || self.terminal_obligation.selected_pool_id != self.journal.selected_pool_id
            || self.terminal_obligation.quote_input_flow_id != self.ports.quote_input.flow_id()?
            || self.terminal_obligation.purchased_output_flow_id
                != self.ports.purchased_output.flow_id()?
            || self.terminal_obligation.purchased_atoms != self.journal.purchased_zdex_atoms
            || self.ports.quote_input.context.context_root()? != self.context.context_root()?
            || self.ports.purchased_output.context.context_root()? != self.context.context_root()?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot V2 accepted projection binding",
            ));
        }
        Ok(())
    }
}

/// Locally rederived SHADOW evidence.  It is intentionally not a receipt.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXSpotBuybackAcceptedV2 {
    subject: ZDEXSpotBuybackInputV2,
    fields: ZDEXSpotBuybackAcceptedFieldsV2,
}

impl ZDEXSpotBuybackAcceptedV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.subject.validate_payload()?;
        self.fields.validate()?;
        let expected = derive_zdex_spot_buyback_v2(&self.subject)?;
        match expected {
            ZDEXSpotBuybackDerivationV2::Accepted(expected)
                if expected.as_ref() == &self.fields =>
            {
                Ok(())
            }
            _ => Err(AbiErrorV1::InvalidBinding(
                "Spot V2 accepted projection no longer rederives",
            )),
        }
    }

    pub fn pre_state(&self) -> AbiResultV1<&ZDEXSpotLaneStateV1> {
        self.validate()?;
        Ok(&self.fields.pre_state)
    }

    pub fn post_state(&self) -> AbiResultV1<&ZDEXSpotLaneStateV1> {
        self.validate()?;
        Ok(&self.fields.post_state)
    }

    pub fn effects(&self) -> AbiResultV1<&GlobalEconomicEffectPlanV1> {
        self.validate()?;
        Ok(&self.fields.effects)
    }

    pub fn context(&self) -> AbiResultV1<&ZDEXSpotBuybackContextV2> {
        self.validate()?;
        Ok(&self.fields.context)
    }

    pub fn quote_port_root(&self) -> AbiResultV1<&RootV1> {
        self.validate()?;
        Ok(&self.fields.context.coordinates.quote_port_root)
    }

    pub fn ports(&self) -> AbiResultV1<&ZDEXSpotPrivatePortsV2> {
        self.validate()?;
        Ok(&self.fields.ports)
    }

    pub fn journal(&self) -> AbiResultV1<&ZDEXSpotBuybackJournalV2> {
        self.validate()?;
        Ok(&self.fields.journal)
    }

    pub fn terminal_obligation(&self) -> AbiResultV1<&ZDEXSpotTerminalObligationV2> {
        self.validate()?;
        Ok(&self.fields.terminal_obligation)
    }

    pub fn price_safety(&self) -> AbiResultV1<&VerifiedZDEXBuybackPriceSafetyV1> {
        self.validate()?;
        Ok(&self.fields.price_safety)
    }
}

/// Host-facing extraction boundary.  The accepted wrapper is revalidated before
/// any terminal leaves this module; this does not authenticate route provenance.
pub fn terminal_from_spot_accepted_v2(
    accepted: &ZDEXSpotBuybackAcceptedV2,
) -> AbiResultV1<ZDEXSpotTerminalObligationV2> {
    accepted.validate()?;
    Ok(accepted.fields.terminal_obligation.clone())
}

/// Host-facing effect extraction boundary.  As with terminal extraction, this
/// is SHADOW data only and revalidates the accepted wrapper first.
pub fn effect_plan_from_spot_accepted_v2(
    accepted: &ZDEXSpotBuybackAcceptedV2,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    accepted.validate()?;
    Ok(accepted.fields.effects.clone())
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXSpotBuybackResultV2 {
    Accepted(Box<ZDEXSpotBuybackAcceptedV2>),
    Rejected(Box<ZDEXSpotBuybackRejectedV2>),
}

enum ZDEXSpotBuybackDerivationV2 {
    Accepted(Box<ZDEXSpotBuybackAcceptedFieldsV2>),
    Rejected(ZDEXSpotBuybackRejectCodeV2),
}

/// Execute the V2 Spot leaf.  It does no I/O, verification, publication, or
/// effect application.
pub fn transition_zdex_spot_buyback_v2(
    candidate: &ZDEXSpotBuybackInputV2,
) -> AbiResultV1<ZDEXSpotBuybackResultV2> {
    // The supplied lane state is authoritative pre-state.  It must clear deep
    // admission before this transition can construct a typed no-op rejection;
    // otherwise the rejection would retain an invalid state and violate its
    // own exact no-op invariant.
    deep_validate_lane_state_v2(&candidate.pre_state)?;
    let derived = derive_zdex_spot_buyback_v2(candidate)?;
    match derived {
        ZDEXSpotBuybackDerivationV2::Accepted(fields) => Ok(ZDEXSpotBuybackResultV2::Accepted(
            Box::new(ZDEXSpotBuybackAcceptedV2 {
                subject: candidate.clone(),
                fields: *fields,
            }),
        )),
        ZDEXSpotBuybackDerivationV2::Rejected(code) => Ok(ZDEXSpotBuybackResultV2::Rejected(
            Box::new(ZDEXSpotBuybackRejectedV2::new(code, &candidate.pre_state)),
        )),
    }
}

fn derive_zdex_spot_buyback_v2(
    candidate: &ZDEXSpotBuybackInputV2,
) -> AbiResultV1<ZDEXSpotBuybackDerivationV2> {
    if validate_non_authoritative_payload_v2(candidate).is_err() {
        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
            ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED,
        ));
    }
    let authority = match &candidate.authority {
        ZDEXSpotBuybackAuthorityInputV2::CONTEXT(authority) if authority.validate().is_ok() => {
            &authority.stable_authority
        }
        ZDEXSpotBuybackAuthorityInputV2::CONTEXT(_)
        | ZDEXSpotBuybackAuthorityInputV2::MALFORMED => {
            return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
                ZDEXSpotBuybackRejectCodeV2::AUTHORITY_MALFORMED,
            ));
        }
    };
    let coordinates = coordinates_for_v2(authority, &candidate.pre_state, &candidate.quote_port)?;
    let stable_result = transition_zdex_spot_buyback_v1(&v1_math_view(candidate, authority)?)?;
    let (stable_accepted, stable_late_rejection) = match stable_result {
        ZDEXSpotBuybackResultV1::Accepted(accepted) => (Some(*accepted), None),
        ZDEXSpotBuybackResultV1::Rejected(rejected) => {
            let code = map_v1_reject_v2(rejected.code());
            match code {
                ZDEXSpotBuybackRejectCodeV2::AUTHORITY_MALFORMED
                | ZDEXSpotBuybackRejectCodeV2::RELEASE_MISMATCH
                | ZDEXSpotBuybackRejectCodeV2::PROFILE_MISMATCH
                | ZDEXSpotBuybackRejectCodeV2::STATE_COMMITMENT_MISMATCH
                | ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH => {
                    return Ok(ZDEXSpotBuybackDerivationV2::Rejected(code));
                }
                ZDEXSpotBuybackRejectCodeV2::ORACLE_MISMATCH => {
                    if !quote_matches_v2(candidate, authority, &coordinates)? {
                        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
                            ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH,
                        ));
                    }
                    return Ok(ZDEXSpotBuybackDerivationV2::Rejected(code));
                }
                ZDEXSpotBuybackRejectCodeV2::PRICE_SUBJECT_MISMATCH => {
                    if !quote_matches_v2(candidate, authority, &coordinates)? {
                        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
                            ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH,
                        ));
                    }
                    return Ok(ZDEXSpotBuybackDerivationV2::Rejected(code));
                }
                _ => (None, Some(code)),
            }
        }
    };
    if !quote_matches_v2(candidate, authority, &coordinates)? {
        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
            ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH,
        ));
    }
    if !price_subject_matches_v2(candidate, authority, &coordinates)? {
        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(
            ZDEXSpotBuybackRejectCodeV2::PRICE_SUBJECT_MISMATCH,
        ));
    }
    if let Some(code) = stable_late_rejection {
        return Ok(ZDEXSpotBuybackDerivationV2::Rejected(code));
    }
    let accepted = match stable_accepted {
        Some(accepted) => accepted,
        None => {
            return Err(AbiErrorV1::InvalidBinding(
                "Spot V2 stable derivation shape",
            ))
        }
    };
    let fields = build_accepted_fields_v2(candidate, authority, coordinates, &accepted)?;
    fields.validate()?;
    Ok(ZDEXSpotBuybackDerivationV2::Accepted(Box::new(fields)))
}

fn validate_non_authoritative_payload_v2(candidate: &ZDEXSpotBuybackInputV2) -> AbiResultV1<()> {
    candidate.quote_port.validate()?;
    candidate.price_envelope.validate()
}

fn coordinates_for_v2(
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    pre_state: &ZDEXSpotLaneStateV1,
    quote_port: &ZDEXAtomicBuybackQuotePortV2,
) -> AbiResultV1<ZDEXSpotBuybackCoordinatesV2> {
    Ok(ZDEXSpotBuybackCoordinatesV2 {
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        global_pre_state_root: authority.global_pre_state_root.clone(),
        spot_pre_state_root: pre_state.state_root()?,
        producer_quote_pre_state_root: quote_port.producer_quote_pre_state_root.clone(),
        producer_quote_post_state_root: quote_port.producer_quote_post_state_root.clone(),
        producer_quote_effect_plan_root: quote_port.producer_quote_effect_plan_root.clone(),
        quote_port_root: quote_port.port_root()?,
    })
}

fn quote_matches_v2(
    candidate: &ZDEXSpotBuybackInputV2,
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    coordinates: &ZDEXSpotBuybackCoordinatesV2,
) -> AbiResultV1<bool> {
    let quote = &candidate.quote_port;
    Ok(quote.profile_root == coordinates.profile_root
        && quote.route_release_id == coordinates.route_release_id
        && quote.command_occurrence_id == coordinates.command_occurrence_id
        && quote.global_pre_state_root == coordinates.global_pre_state_root
        && quote.producer_module_release_id == authority.tokenomics_module_release_id
        && quote.consumer_module_release_id == authority.spot_module_release_id
        && quote.selected_pool_id == authority.execution_policy.pool_id
        && quote.quote_asset_id == authority.execution_policy.quote_asset_id
        && quote.producer_quote_pre_state_root == coordinates.producer_quote_pre_state_root
        && quote.producer_quote_post_state_root == coordinates.producer_quote_post_state_root
        && quote.producer_quote_effect_plan_root == coordinates.producer_quote_effect_plan_root
        && quote.port_root()? == coordinates.quote_port_root)
}

fn price_subject_matches_v2(
    candidate: &ZDEXSpotBuybackInputV2,
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    coordinates: &ZDEXSpotBuybackCoordinatesV2,
) -> AbiResultV1<bool> {
    let envelope = &candidate.price_envelope;
    let oracle = &authority.oracle_occurrence;
    Ok(
        envelope.coordinates.coordinates_root()? == coordinates.coordinates_root()?
            && envelope.coordinates.quote_port_root == coordinates.quote_port_root
            && envelope.selected_pool_id == authority.execution_policy.pool_id
            && envelope.oracle_occurrence_id == oracle.occurrence_id()?
            && envelope.oracle_finality_root == oracle.finality_root
            && envelope.quote_amount_atoms == candidate.quote_port.amount_atoms
            && envelope.current_height == authority.current_height
            && envelope.oracle_observed_height == oracle.price.observed_height
            && envelope.oracle_quote_numerator_atoms == oracle.price.quote_numerator_atoms
            && envelope.oracle_zdex_denominator_atoms == oracle.price.zdex_denominator_atoms,
    )
}

/// Rust cannot access V1's private arithmetic helpers.  This view is only an
/// invocation adapter for the public V1 transition.  Its two legacy slots are
/// bound to the V2 port hash and are neither exported nor committed by V2.
fn v1_math_view(
    candidate: &ZDEXSpotBuybackInputV2,
    authority: &ZDEXSpotBuybackAuthorityContextV1,
) -> AbiResultV1<ZDEXSpotBuybackInputV1> {
    let quote = &candidate.quote_port;
    let port_root = quote.port_root()?;
    Ok(ZDEXSpotBuybackInputV1 {
        authority: ZDEXSpotBuybackAuthorityInputV1::CONTEXT(Box::new(authority.clone())),
        pre_state: candidate.pre_state.clone(),
        quote_port: crate::ZDEXSpotQuoteInputPortV1 {
            profile_root: quote.profile_root.clone(),
            route_release_id: quote.route_release_id.clone(),
            command_occurrence_id: quote.command_occurrence_id.clone(),
            global_pre_state_root: quote.global_pre_state_root.clone(),
            spot_pre_state_root: candidate.pre_state.state_root()?,
            source_module_release_id: quote.producer_module_release_id.clone(),
            destination_module_release_id: quote.consumer_module_release_id.clone(),
            source_pre_state_root: quote.producer_quote_pre_state_root.clone(),
            source_post_state_root: quote.producer_quote_post_state_root.clone(),
            source_effect_plan_root: quote.producer_quote_effect_plan_root.clone(),
            source_journal_root: port_root.clone(),
            source_receipt_binding_root: port_root,
            amount_atoms: quote.amount_atoms,
        },
        price_envelope: ZDEXSpotPriceEnvelopeV1 {
            profile_root: authority.profile_root.clone(),
            route_release_id: authority.route_release_id.clone(),
            command_occurrence_id: authority.command_occurrence_id.clone(),
            global_pre_state_root: authority.global_pre_state_root.clone(),
            spot_pre_state_root: candidate.pre_state.state_root()?,
            selected_pool_id: candidate.price_envelope.selected_pool_id.clone(),
            oracle_occurrence_id: candidate.price_envelope.oracle_occurrence_id.clone(),
            oracle_finality_root: candidate.price_envelope.oracle_finality_root.clone(),
            quote_amount_atoms: candidate.price_envelope.quote_amount_atoms,
            current_height: candidate.price_envelope.current_height,
            oracle_observed_height: candidate.price_envelope.oracle_observed_height,
            oracle_quote_numerator_atoms: candidate.price_envelope.oracle_quote_numerator_atoms,
            oracle_zdex_denominator_atoms: candidate.price_envelope.oracle_zdex_denominator_atoms,
            claimed_route_safe_quote_limit_atoms: candidate
                .price_envelope
                .claimed_route_safe_quote_limit_atoms,
            minimum_output_atoms: candidate.price_envelope.minimum_output_atoms,
        },
    })
}

fn build_accepted_fields_v2(
    candidate: &ZDEXSpotBuybackInputV2,
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
    stable: &ZDEXSpotBuybackAcceptedV1,
) -> AbiResultV1<ZDEXSpotBuybackAcceptedFieldsV2> {
    let context = context_for_v2(authority, coordinates)?;
    let policy = &authority.execution_policy;
    let quote_pool = candidate.quote_port.destination_principal()?;
    let zdex_pool = zdex_pool_reserve_principal_v1(&policy.pool_id, &policy.zdex_asset_id)?;
    let burn_principal = zdex_occurrence_burn_port_v1(
        &context.coordinates.profile_root,
        &context.coordinates.route_release_id,
        &context.coordinates.command_occurrence_id,
    )?;
    let journal_v1 = stable.journal();
    let quote_input = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::QUOTE_INPUT,
        context: context.clone(),
        selected_pool_id: policy.pool_id.clone(),
        asset: policy.quote_asset_id.clone(),
        source_principal: candidate.quote_port.source_principal().to_owned(),
        destination_principal: quote_pool,
        amount_atoms: journal_v1.quote_input_atoms,
    };
    let purchased_output = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
        context: context.clone(),
        selected_pool_id: policy.pool_id.clone(),
        asset: policy.zdex_asset_id.clone(),
        source_principal: zdex_pool,
        destination_principal: burn_principal.clone(),
        amount_atoms: journal_v1.purchased_zdex_atoms,
    };
    let ports = ZDEXSpotPrivatePortsV2 {
        quote_input,
        purchased_output,
    };
    let post_state = stable.post_state().clone();
    let terminal = ZDEXSpotTerminalObligationV2 {
        context: context.clone(),
        post_state_root: post_state.state_root()?,
        consumer_module_release_id: authority.tokenomics_module_release_id.clone(),
        burn_asset: policy.zdex_asset_id.clone(),
        burn_principal,
        selected_pool_id: policy.pool_id.clone(),
        quote_input_flow_id: ports.quote_input.flow_id()?,
        purchased_output_flow_id: ports.purchased_output.flow_id()?,
        purchased_atoms: journal_v1.purchased_zdex_atoms,
    };
    let effects = stable.effects().clone();
    let journal = ZDEXSpotBuybackJournalV2 {
        context,
        post_state_root: post_state.state_root()?,
        effect_plan_root: effects.effect_plan_root()?,
        private_ports_root: ports.ports_root()?,
        terminal_obligation_id: terminal.obligation_id()?,
        selected_pool_id: policy.pool_id.clone(),
        pool_definition_root: policy.pool_definition_root.clone(),
        quote_input_atoms: journal_v1.quote_input_atoms,
        fee_atoms: journal_v1.fee_atoms,
        net_input_atoms: journal_v1.net_input_atoms,
        purchased_zdex_atoms: journal_v1.purchased_zdex_atoms,
        route_safe_quote_limit_atoms: journal_v1.route_safe_quote_limit_atoms,
        minimum_output_atoms: journal_v1.minimum_output_atoms,
        pre_quote_reserve_atoms: journal_v1.pre_quote_reserve_atoms,
        post_quote_reserve_atoms: journal_v1.post_quote_reserve_atoms,
        pre_zdex_reserve_atoms: journal_v1.pre_zdex_reserve_atoms,
        post_zdex_reserve_atoms: journal_v1.post_zdex_reserve_atoms,
    };
    Ok(ZDEXSpotBuybackAcceptedFieldsV2 {
        pre_state: stable.pre_state().clone(),
        post_state,
        effects,
        context: journal.context.clone(),
        ports,
        journal,
        terminal_obligation: terminal,
        price_safety: stable.price_safety().clone(),
    })
}

fn context_for_v2(
    authority: &ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
) -> AbiResultV1<ZDEXSpotBuybackContextV2> {
    #[derive(Serialize)]
    struct CanonicalRegistry<'a> {
        schema: &'static str,
        occurrences: &'a [crate::ZDEXSpotOracleOccurrenceV1],
    }
    let oracle_registry_root = hash_global_v1(
        "zdex-spot-oracle-registry-v1",
        &CanonicalRegistry {
            schema: crate::ZDEX_SPOT_ORACLE_REGISTRY_SCHEMA_V1,
            occurrences: &authority.oracle_registry.occurrences,
        },
    )?;
    Ok(ZDEXSpotBuybackContextV2 {
        coordinates,
        chain_id: authority.chain_id.clone(),
        deployment_root: authority.deployment_root.clone(),
        profile_authorization_root: authority.profile_authorization_root.clone(),
        writer_epoch: authority.writer_epoch,
        current_height: authority.current_height,
        spot_module_release_id: authority.spot_module_release_id.clone(),
        tokenomics_module_release_id: authority.tokenomics_module_release_id.clone(),
        release_root: authority.release.release_root()?,
        execution_policy_root: authority.execution_policy.policy_root()?,
        price_policy_root: authority.price_policy.policy_root()?,
        oracle_registry_root,
        oracle_occurrence_id: authority.oracle_occurrence.occurrence_id()?,
    })
}

fn empty_effect_plan_v2() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}

fn validate_positive_effect_atoms_v2(value: u128, name: &'static str) -> AbiResultV1<()> {
    if value == 0 || value > MAX_DELTA_ATOMS_V2 {
        return Err(AbiErrorV1::InvalidBounds(name));
    }
    Ok(())
}

fn deep_validate_lane_state_v2(state: &ZDEXSpotLaneStateV1) -> AbiResultV1<RootV1> {
    for pool in &state.pools {
        pool.pool_id.validate("Spot V2 state pool id", false)?;
        pool.creation_release_id
            .validate("Spot V2 state pool creation release", false)?;
        pool.definition.validate()?;
        if pool.definition.pool_id()? != pool.pool_id {
            return Err(AbiErrorV1::InvalidBinding("Spot V2 state pool identity"));
        }
    }
    state.state_root()
}

fn map_v1_reject_v2(code: ZDEXSpotBuybackRejectCodeV1) -> ZDEXSpotBuybackRejectCodeV2 {
    match code {
        ZDEXSpotBuybackRejectCodeV1::AUTHORITY_MALFORMED => {
            ZDEXSpotBuybackRejectCodeV2::AUTHORITY_MALFORMED
        }
        ZDEXSpotBuybackRejectCodeV1::RELEASE_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::RELEASE_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::PROFILE_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::PROFILE_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::STATE_COMMITMENT_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::QUOTE_PORT_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::ORACLE_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::ORACLE_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::PRICE_SUBJECT_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::PRICE_SUBJECT_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::POLICY_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::POLICY_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::LANE_MALFORMED => ZDEXSpotBuybackRejectCodeV2::LANE_MALFORMED,
        ZDEXSpotBuybackRejectCodeV1::SELECTION_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::SELECTION_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::POOL_INACTIVE => ZDEXSpotBuybackRejectCodeV2::POOL_INACTIVE,
        ZDEXSpotBuybackRejectCodeV1::AMOUNT_OUT_OF_RANGE => {
            ZDEXSpotBuybackRejectCodeV2::AMOUNT_OUT_OF_RANGE
        }
        ZDEXSpotBuybackRejectCodeV1::ARITHMETIC_OUT_OF_RANGE => {
            ZDEXSpotBuybackRejectCodeV2::ARITHMETIC_OUT_OF_RANGE
        }
        ZDEXSpotBuybackRejectCodeV1::FEE_CONSUMES_INPUT => {
            ZDEXSpotBuybackRejectCodeV2::FEE_CONSUMES_INPUT
        }
        ZDEXSpotBuybackRejectCodeV1::ZERO_OUTPUT => ZDEXSpotBuybackRejectCodeV2::ZERO_OUTPUT,
        ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH => {
            ZDEXSpotBuybackRejectCodeV2::MINIMUM_OUTPUT_MISMATCH
        }
        ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE => ZDEXSpotBuybackRejectCodeV2::PRICE_UNSAFE,
    }
}

#[cfg(test)]
#[path = "zdex_spot_buyback_transition_v2_rejection_fixture.rs"]
mod rejection_fixture;

#[cfg(test)]
mod rejection_tests {
    use super::*;

    fn root(value: u64) -> RootV1 {
        RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed root")
    }

    fn zero_root() -> RootV1 {
        RootV1::parse(
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "zero root",
            true,
        )
        .expect("fixed zero root")
    }

    fn state() -> ZDEXSpotLaneStateV1 {
        ZDEXSpotLaneStateV1 {
            pools: Vec::new(),
            lp_ownership_root: root(1),
            route_batch_root: root(2),
            fee_residue_root: root(3),
            pool_terminal_obligations_root: root(4),
        }
    }

    #[test]
    fn rejected_v2_effect_plans_are_not_shared() {
        let first =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        let second =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        assert!(!std::ptr::eq(first.effects(), second.effects()));
    }

    #[test]
    fn rejected_v2_revalidates_retained_state_after_mutation() {
        let mut rejected =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        rejected.pre_state.route_batch_root = zero_root();
        rejected.post_state.route_batch_root = zero_root();
        assert!(rejected.validate().is_err());
    }

    #[test]
    fn rejected_v2_requires_exact_empty_and_null_success_payloads() {
        let mut rejected =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        rejected.effects.rows.push(crate::EconomicEffectRowV1 {
            kind: crate::EconomicEffectKindV1::ACCOUNT_MOVEMENT,
            principal: "protocol:test".to_owned(),
            asset: root(5).to_string(),
            custody_domain: "zenoledger:test".to_owned(),
            delta_atoms: 1,
        });
        assert!(rejected.validate().is_err());

        let ZDEXSpotBuybackResultV2::Accepted(accepted) =
            transition_zdex_spot_buyback_v2(&super::rejection_fixture::accepted_candidate())
                .expect("typed transition")
        else {
            panic!("fixture must accept");
        };

        let mut nonnull =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        nonnull.context = Some(accepted.fields.context.clone());
        assert!(nonnull.validate().is_err());

        let mut nonnull =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        nonnull.ports = Some(accepted.fields.ports.clone());
        assert!(nonnull.validate().is_err());

        let mut nonnull =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        nonnull.journal = Some(accepted.fields.journal.clone());
        assert!(nonnull.validate().is_err());

        let mut nonnull =
            ZDEXSpotBuybackRejectedV2::new(ZDEXSpotBuybackRejectCodeV2::INPUT_MALFORMED, &state());
        nonnull.terminal_obligation = Some(accepted.fields.terminal_obligation.clone());
        assert!(nonnull.validate().is_err());
    }

    #[test]
    fn spot_result_adapter_rejects_stale_or_object_new_forged_accepted_wrapper() {
        let candidate = super::rejection_fixture::accepted_candidate();
        let ZDEXSpotBuybackResultV2::Accepted(accepted) =
            transition_zdex_spot_buyback_v2(&candidate).expect("typed transition")
        else {
            panic!("fixture must accept");
        };

        // Safe callers cannot instantiate or mutate the wrapper's private
        // fields.  These in-module copies emulate a stale or unsafe/object-new
        // forged wrapper and ensure both host extraction boundaries revalidate.
        let mut stale = (*accepted).clone();
        stale.subject.quote_port.amount_atoms = stale
            .subject
            .quote_port
            .amount_atoms
            .checked_add(1)
            .expect("test amount");
        assert!(terminal_from_spot_accepted_v2(&stale).is_err());
        assert!(effect_plan_from_spot_accepted_v2(&stale).is_err());

        let mut forged = (*accepted).clone();
        forged.fields.terminal_obligation.purchased_atoms = 1;
        assert!(terminal_from_spot_accepted_v2(&forged).is_err());
        assert!(effect_plan_from_spot_accepted_v2(&forged).is_err());
    }

    #[test]
    fn m10_maps_each_of_the_seventeen_stable_reject_codes() {
        let pairs = [
            (
                ZDEXSpotBuybackRejectCodeV1::AUTHORITY_MALFORMED,
                ZDEXSpotBuybackRejectCodeV2::AUTHORITY_MALFORMED,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::RELEASE_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::RELEASE_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::PROFILE_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::PROFILE_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::STATE_COMMITMENT_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::QUOTE_PORT_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::QUOTE_PORT_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::ORACLE_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::ORACLE_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::PRICE_SUBJECT_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::PRICE_SUBJECT_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::POLICY_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::POLICY_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::LANE_MALFORMED,
                ZDEXSpotBuybackRejectCodeV2::LANE_MALFORMED,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::SELECTION_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::SELECTION_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::POOL_INACTIVE,
                ZDEXSpotBuybackRejectCodeV2::POOL_INACTIVE,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::AMOUNT_OUT_OF_RANGE,
                ZDEXSpotBuybackRejectCodeV2::AMOUNT_OUT_OF_RANGE,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::ARITHMETIC_OUT_OF_RANGE,
                ZDEXSpotBuybackRejectCodeV2::ARITHMETIC_OUT_OF_RANGE,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::FEE_CONSUMES_INPUT,
                ZDEXSpotBuybackRejectCodeV2::FEE_CONSUMES_INPUT,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::ZERO_OUTPUT,
                ZDEXSpotBuybackRejectCodeV2::ZERO_OUTPUT,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH,
                ZDEXSpotBuybackRejectCodeV2::MINIMUM_OUTPUT_MISMATCH,
            ),
            (
                ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE,
                ZDEXSpotBuybackRejectCodeV2::PRICE_UNSAFE,
            ),
        ];
        assert_eq!(pairs.len(), 17);
        for (v1, v2) in pairs {
            assert_eq!(map_v1_reject_v2(v1), v2);
        }
    }
}
