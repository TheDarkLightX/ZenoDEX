//! Route-bound Oracle occurrence authority inside an exact global pre-state.
//!
//! Finalized observations are reusable authenticated reads, not single-use
//! consumed objects. This checker verifies structural authority only. Profile
//! selection, receipt verification, and atomic publication remain separate
//! verifier obligations.

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::RouteReleaseV1;
use crate::state::GlobalEconomicStateV1;

pub const GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1: &str =
    "zenodex/global-oracle-occurrence-authority/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalOracleOccurrencePolicyV1 {
    pub schema: String,
    pub oracle_id: String,
    pub max_observation_age_blocks: u64,
}

impl GlobalOracleOccurrencePolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.oracle_id, "global oracle policy oracle id")
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-oracle-occurrence-policy-v1", self)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct GlobalOracleOccurrenceAuthorityCandidateV1<'a> {
    pub pre_state: &'a GlobalEconomicStateV1,
    pub route: &'a RouteReleaseV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub policy: &'a GlobalOracleOccurrencePolicyV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalOracleOccurrenceAuthorityV1 {
    pre_state_root: RootV1,
    route_release_id: RootV1,
    command_occurrence_id: RootV1,
    policy_root: RootV1,
    oracle_id: String,
    occurrence_root: RootV1,
    observed_height: u64,
    state_height: u64,
    evaluation_height: u64,
    observation_age_blocks: u64,
}

#[derive(Serialize)]
struct GlobalOracleOccurrenceAuthorityContentV1<'a> {
    schema: &'static str,
    pre_state_root: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    policy_root: &'a RootV1,
    oracle_id: &'a str,
    occurrence_root: &'a RootV1,
    observed_height: u64,
    state_height: u64,
    evaluation_height: u64,
    observation_age_blocks: u64,
}

impl GlobalOracleOccurrenceAuthorityV1 {
    pub fn pre_state_root(&self) -> &RootV1 {
        &self.pre_state_root
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn policy_root(&self) -> &RootV1 {
        &self.policy_root
    }

    pub fn oracle_id(&self) -> &str {
        &self.oracle_id
    }

    pub fn occurrence_root(&self) -> &RootV1 {
        &self.occurrence_root
    }

    pub fn observed_height(&self) -> u64 {
        self.observed_height
    }

    pub fn state_height(&self) -> u64 {
        self.state_height
    }

    pub fn evaluation_height(&self) -> u64 {
        self.evaluation_height
    }

    pub fn observation_age_blocks(&self) -> u64 {
        self.observation_age_blocks
    }

    pub fn authority_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "global-oracle-occurrence-authority-v1",
            &GlobalOracleOccurrenceAuthorityContentV1 {
                schema: GLOBAL_ORACLE_OCCURRENCE_AUTHORITY_SCHEMA_V1,
                pre_state_root: &self.pre_state_root,
                route_release_id: &self.route_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                policy_root: &self.policy_root,
                oracle_id: &self.oracle_id,
                occurrence_root: &self.occurrence_root,
                observed_height: self.observed_height,
                state_height: self.state_height,
                evaluation_height: self.evaluation_height,
                observation_age_blocks: self.observation_age_blocks,
            },
        )
    }
}

fn require_exact_context_v1(
    candidate: &GlobalOracleOccurrenceAuthorityCandidateV1<'_>,
    pre_state_root: &RootV1,
    policy_root: &RootV1,
) -> AbiResultV1<()> {
    let expected_height = candidate
        .pre_state
        .height
        .checked_add(1)
        .ok_or(AbiErrorV1::InvalidBounds("oracle authority command height"))?;
    if candidate.route.oracle_policy_root != *policy_root {
        return Err(AbiErrorV1::InvalidBinding("route oracle policy root"));
    }
    if candidate.occurrence.chain_id != candidate.pre_state.chain_id
        || candidate.occurrence.deployment_root != candidate.pre_state.deployment_root
        || candidate.occurrence.profile_root != candidate.pre_state.profile_root
        || candidate.occurrence.pre_state_root != *pre_state_root
        || candidate.occurrence.route_release_id != candidate.route.route_release_id
        || candidate.occurrence.command_kind != candidate.route.command_kind
        || candidate.occurrence.height != expected_height
    {
        return Err(AbiErrorV1::InvalidBinding(
            "oracle authority command context",
        ));
    }
    Ok(())
}

pub fn verify_global_oracle_occurrence_authority_v1(
    candidate: GlobalOracleOccurrenceAuthorityCandidateV1<'_>,
) -> AbiResultV1<GlobalOracleOccurrenceAuthorityV1> {
    candidate.pre_state.validate()?;
    candidate.route.validate()?;
    candidate.occurrence.validate()?;
    candidate.policy.validate()?;
    let pre_state_root = candidate.pre_state.state_root()?;
    let policy_root = candidate.policy.policy_root()?;
    require_exact_context_v1(&candidate, &pre_state_root, &policy_root)?;
    let occurrence = candidate
        .pre_state
        .oracle_occurrences
        .iter()
        .find(|occurrence| occurrence.oracle_id == candidate.policy.oracle_id)
        .ok_or(AbiErrorV1::InvalidBinding("route-bound oracle occurrence"))?;
    if !occurrence.finalized {
        return Err(AbiErrorV1::InvalidBinding("oracle occurrence finality"));
    }
    if occurrence.observed_height > candidate.pre_state.height {
        return Err(AbiErrorV1::InvalidBounds(
            "oracle occurrence observed height",
        ));
    }
    let observation_age_blocks = candidate
        .occurrence
        .height
        .checked_sub(occurrence.observed_height)
        .ok_or(AbiErrorV1::InvalidBounds(
            "oracle occurrence observed height",
        ))?;
    if observation_age_blocks > candidate.policy.max_observation_age_blocks {
        return Err(AbiErrorV1::InvalidBounds("oracle occurrence freshness"));
    }
    Ok(GlobalOracleOccurrenceAuthorityV1 {
        pre_state_root,
        route_release_id: candidate.route.route_release_id.clone(),
        command_occurrence_id: candidate.occurrence.occurrence_id()?,
        policy_root,
        oracle_id: candidate.policy.oracle_id.clone(),
        occurrence_root: occurrence.occurrence_root.clone(),
        observed_height: occurrence.observed_height,
        state_height: candidate.pre_state.height,
        evaluation_height: candidate.occurrence.height,
        observation_age_blocks,
    })
}
