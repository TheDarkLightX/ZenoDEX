use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::{
    EconomicCommandOccurrenceIdV1, EconomicProfileIdV1, GlobalAssetReconciliationV1,
    GlobalEconomicEffectBodyInputV1, GlobalEconomicEffectPlanErrorV1,
    GlobalEconomicEffectPlanInputV1, GlobalEconomicEffectRowV1, GlobalEconomicStateRootV1,
    GlobalOccurrenceConsumptionKindV1, RouteReleaseIdV1, StateBoundEconomicCommandOccurrenceV1,
    GLOBAL_ECONOMIC_EFFECT_PLAN_VERSION_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

use super::global_economic_effect_plan_bounded::{
    deserialize_effect_rows, deserialize_reconciliations,
};
use super::global_economic_effect_plan_hash::{
    commitment, domain_hasher, effect_rows_root_v1, effect_semantics_root_v1,
    lane_effect_rows_root_v1, lane_terminal_obligations_root_v1, reconciliations_root_v1,
    EFFECT_BODY_COMMITMENT_DOMAIN_V1, EFFECT_PLAN_COMMITMENT_DOMAIN_V1,
};
use super::global_economic_effect_plan_validate::{
    authority_rows_match_v1, canonicalize_body_rows_v1, consumption_rows_v1,
    issue_burn_policy_matches_v1, validate_body_rows_v1,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GlobalEconomicEffectBodyV1 {
    post_state_root: GlobalEconomicStateRootV1,
    effects: Vec<GlobalEconomicEffectRowV1>,
    reconciliations: Vec<GlobalAssetReconciliationV1>,
    effect_rows_root: CommitmentV3,
    effect_semantics_root: CommitmentV3,
    reconciliations_root: CommitmentV3,
    effect_commitment: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GlobalEconomicEffectBodyWireV1 {
    post_state_root: GlobalEconomicStateRootV1,
    #[serde(deserialize_with = "deserialize_effect_rows")]
    effects: Vec<GlobalEconomicEffectRowV1>,
    #[serde(deserialize_with = "deserialize_reconciliations")]
    reconciliations: Vec<GlobalAssetReconciliationV1>,
    effect_rows_root: CommitmentV3,
    effect_semantics_root: CommitmentV3,
    reconciliations_root: CommitmentV3,
    effect_commitment: CommitmentV3,
}

impl GlobalEconomicEffectBodyV1 {
    pub fn new(
        mut input: GlobalEconomicEffectBodyInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        canonicalize_body_rows_v1(&mut input.effects, &mut input.reconciliations)?;
        validate_body_rows_v1(None, &input.effects, &input.reconciliations)?;
        let effect_rows_root = effect_rows_root_v1(&input.effects)?;
        let effect_semantics_root = effect_semantics_root_v1(&input.effects)?;
        let reconciliations_root = reconciliations_root_v1(&input.reconciliations)?;
        let effect_commitment = effect_body_commitment_v1(
            input.post_state_root,
            effect_semantics_root,
            reconciliations_root,
        )?;
        Ok(Self {
            post_state_root: input.post_state_root,
            effects: input.effects,
            reconciliations: input.reconciliations,
            effect_rows_root,
            effect_semantics_root,
            reconciliations_root,
            effect_commitment,
        })
    }

    fn from_wire(
        wire: GlobalEconomicEffectBodyWireV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        let body = Self {
            post_state_root: wire.post_state_root,
            effects: wire.effects,
            reconciliations: wire.reconciliations,
            effect_rows_root: wire.effect_rows_root,
            effect_semantics_root: wire.effect_semantics_root,
            reconciliations_root: wire.reconciliations_root,
            effect_commitment: wire.effect_commitment,
        };
        body.validate_self_consistency(None)?;
        Ok(body)
    }

    pub(super) fn validate_self_consistency(
        &self,
        local_domain_id: Option<DomainIdV3>,
    ) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
        validate_body_rows_v1(local_domain_id, &self.effects, &self.reconciliations)?;
        require_commitment(
            "effect_rows_root",
            self.effect_rows_root,
            effect_rows_root_v1(&self.effects)?,
        )?;
        require_commitment(
            "effect_semantics_root",
            self.effect_semantics_root,
            effect_semantics_root_v1(&self.effects)?,
        )?;
        require_commitment(
            "reconciliations_root",
            self.reconciliations_root,
            reconciliations_root_v1(&self.reconciliations)?,
        )?;
        require_commitment(
            "effect_commitment",
            self.effect_commitment,
            effect_body_commitment_v1(
                self.post_state_root,
                self.effect_semantics_root,
                self.reconciliations_root,
            )?,
        )
    }

    pub const fn post_state_root(&self) -> GlobalEconomicStateRootV1 {
        self.post_state_root
    }
    pub fn effects(&self) -> &[GlobalEconomicEffectRowV1] {
        &self.effects
    }
    pub fn reconciliations(&self) -> &[GlobalAssetReconciliationV1] {
        &self.reconciliations
    }
    pub const fn effect_rows_root(&self) -> CommitmentV3 {
        self.effect_rows_root
    }
    pub const fn effect_semantics_root(&self) -> CommitmentV3 {
        self.effect_semantics_root
    }
    pub const fn reconciliations_root(&self) -> CommitmentV3 {
        self.reconciliations_root
    }
    pub const fn effect_commitment(&self) -> CommitmentV3 {
        self.effect_commitment
    }

    pub fn lane_effect_rows_root(
        &self,
        lane_id: super::EconomicLaneIdV1,
    ) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
        lane_effect_rows_root_v1(&self.effects, lane_id)
    }

    pub fn lane_terminal_obligations_root(
        &self,
        lane_id: super::EconomicLaneIdV1,
    ) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
        lane_terminal_obligations_root_v1(&self.effects, lane_id)
    }

    pub fn lane_writes(&self, lane_id: super::EconomicLaneIdV1) -> Vec<super::GlobalLaneWriteV1> {
        let mut writes = self
            .effects
            .iter()
            .filter_map(GlobalEconomicEffectRowV1::as_lane_write)
            .filter(|write| write.lane_id() == lane_id)
            .collect::<Vec<_>>();
        writes.sort_unstable_by_key(|write| write.object_id());
        writes
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicEffectBodyV1 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::from_wire(GlobalEconomicEffectBodyWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "a global economic effect plan is ordinary data until verifier stages bind it"]
pub struct GlobalEconomicEffectPlanV1 {
    plan_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    route_release_id: RouteReleaseIdV1,
    pre_state_root: GlobalEconomicStateRootV1,
    body: GlobalEconomicEffectBodyV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct GlobalEconomicEffectPlanWireV1 {
    plan_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    route_release_id: RouteReleaseIdV1,
    pre_state_root: GlobalEconomicStateRootV1,
    body: GlobalEconomicEffectBodyV1,
}

impl GlobalEconomicEffectPlanV1 {
    pub fn new(
        input: GlobalEconomicEffectPlanInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        Self::from_parts(GLOBAL_ECONOMIC_EFFECT_PLAN_VERSION_V1, input)
    }

    fn from_parts(
        plan_version: u16,
        input: GlobalEconomicEffectPlanInputV1,
    ) -> Result<Self, GlobalEconomicEffectPlanErrorV1> {
        let plan = Self {
            plan_version,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            profile_id: input.profile_id,
            writer_epoch: input.writer_epoch,
            occurrence_id: input.occurrence_id,
            route_release_id: input.route_release_id,
            pre_state_root: input.pre_state_root,
            body: input.body,
        };
        plan.validate_self_consistency()?;
        Ok(plan)
    }

    pub fn validate_self_consistency(&self) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
        if self.plan_version != GLOBAL_ECONOMIC_EFFECT_PLAN_VERSION_V1 {
            return Err(GlobalEconomicEffectPlanErrorV1::InvalidVersion(
                self.plan_version,
            ));
        }
        if self.pre_state_root == self.body.post_state_root() {
            return Err(GlobalEconomicEffectPlanErrorV1::PreAndPostStateMatch);
        }
        self.body
            .validate_self_consistency(Some(self.chain_or_domain_id))
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
        self.validate_self_consistency()?;
        let mut hasher = domain_hasher(EFFECT_PLAN_COMMITMENT_DOMAIN_V1)?;
        hasher.update(self.plan_version.to_be_bytes());
        hasher.update(self.application_id.as_bytes());
        hasher.update(self.chain_or_domain_id.as_bytes());
        hasher.update(self.profile_id.as_bytes());
        hasher.update(self.writer_epoch.to_be_bytes());
        hasher.update(self.occurrence_id.as_bytes());
        hasher.update(self.route_release_id.as_bytes());
        hasher.update(self.pre_state_root.as_bytes());
        hasher.update(self.body.effect_rows_root().as_bytes());
        hasher.update(self.body.effect_commitment().as_bytes());
        commitment(hasher, "global_economic_effect_plan")
    }

    pub const fn plan_version(&self) -> u16 {
        self.plan_version
    }
    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }
    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }
    pub const fn profile_id(&self) -> EconomicProfileIdV1 {
        self.profile_id
    }
    pub const fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }
    pub const fn occurrence_id(&self) -> EconomicCommandOccurrenceIdV1 {
        self.occurrence_id
    }
    pub const fn route_release_id(&self) -> RouteReleaseIdV1 {
        self.route_release_id
    }
    pub const fn pre_state_root(&self) -> GlobalEconomicStateRootV1 {
        self.pre_state_root
    }
    pub const fn body(&self) -> &GlobalEconomicEffectBodyV1 {
        &self.body
    }
}

impl<'de> Deserialize<'de> for GlobalEconomicEffectPlanV1 {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = GlobalEconomicEffectPlanWireV1::deserialize(deserializer)?;
        Self::from_parts(
            wire.plan_version,
            GlobalEconomicEffectPlanInputV1 {
                application_id: wire.application_id,
                chain_or_domain_id: wire.chain_or_domain_id,
                profile_id: wire.profile_id,
                writer_epoch: wire.writer_epoch,
                occurrence_id: wire.occurrence_id,
                route_release_id: wire.route_release_id,
                pre_state_root: wire.pre_state_root,
                body: wire.body,
            },
        )
        .map_err(de::Error::custom)
    }
}

/// Constructor-private structural witness tying one declared effect plan to one
/// state-bound occurrence. It is not a proof receipt or publication capability.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::OccurrenceBoundGlobalEconomicEffectPlanV1;
/// let plan = unimplemented!();
/// let occurrence = unimplemented!();
/// let _ = OccurrenceBoundGlobalEconomicEffectPlanV1 { plan, occurrence };
/// ```
///
/// ```compile_fail
/// use serde::Serialize;
/// use zenodex_zrpf_protocol_v3::OccurrenceBoundGlobalEconomicEffectPlanV1;
/// fn require_serializable<T: Serialize>() {}
/// require_serializable::<OccurrenceBoundGlobalEconomicEffectPlanV1<'static>>();
/// ```
#[must_use]
pub struct OccurrenceBoundGlobalEconomicEffectPlanV1<'a> {
    plan: &'a GlobalEconomicEffectPlanV1,
    occurrence: &'a StateBoundEconomicCommandOccurrenceV1<'a>,
}

impl<'a> OccurrenceBoundGlobalEconomicEffectPlanV1<'a> {
    pub const fn plan(&self) -> &'a GlobalEconomicEffectPlanV1 {
        self.plan
    }
    pub const fn occurrence(&self) -> &'a StateBoundEconomicCommandOccurrenceV1<'a> {
        self.occurrence
    }
}

pub fn bind_global_economic_effect_plan_to_occurrence_v1<'a>(
    plan: &'a GlobalEconomicEffectPlanV1,
    occurrence: &'a StateBoundEconomicCommandOccurrenceV1<'a>,
) -> Result<OccurrenceBoundGlobalEconomicEffectPlanV1<'a>, GlobalEconomicEffectPlanErrorV1> {
    plan.validate_self_consistency()?;
    validate_plan_occurrence_envelope(plan, occurrence)?;
    validate_plan_authority_and_route(plan, occurrence)?;
    validate_plan_replay_rows(plan, occurrence)?;
    Ok(OccurrenceBoundGlobalEconomicEffectPlanV1 { plan, occurrence })
}

fn validate_plan_occurrence_envelope(
    plan: &GlobalEconomicEffectPlanV1,
    occurrence: &StateBoundEconomicCommandOccurrenceV1<'_>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let profile_occurrence = occurrence.profile_bound_occurrence();
    let command = profile_occurrence.occurrence();
    let content = command.content();
    let record = content.authorized_action().record();
    if plan.application_id != record.application_id() {
        return Err(GlobalEconomicEffectPlanErrorV1::ApplicationMismatch);
    }
    if plan.chain_or_domain_id != record.chain_or_domain_id() {
        return Err(GlobalEconomicEffectPlanErrorV1::DomainMismatch);
    }
    if plan.profile_id != content.profile_id() {
        return Err(GlobalEconomicEffectPlanErrorV1::ProfileMismatch);
    }
    if plan.writer_epoch != content.writer_epoch() {
        return Err(GlobalEconomicEffectPlanErrorV1::WriterEpochMismatch);
    }
    if plan.occurrence_id != command.occurrence_id() {
        return Err(GlobalEconomicEffectPlanErrorV1::OccurrenceMismatch);
    }
    if plan.route_release_id != content.route_release_id() {
        return Err(GlobalEconomicEffectPlanErrorV1::RouteMismatch);
    }
    if plan.pre_state_root.as_bytes() != record.pre_state_root().as_bytes() {
        return Err(GlobalEconomicEffectPlanErrorV1::PreStateMismatch);
    }
    if plan.body.effect_commitment() != record.effect_commitment() {
        return Err(GlobalEconomicEffectPlanErrorV1::EffectCommitmentMismatch);
    }
    Ok(())
}

fn validate_plan_authority_and_route(
    plan: &GlobalEconomicEffectPlanV1,
    occurrence: &StateBoundEconomicCommandOccurrenceV1<'_>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let profile_occurrence = occurrence.profile_bound_occurrence();
    let action = profile_occurrence
        .occurrence()
        .content()
        .authorized_action();
    let record = action.record();
    let binding = action.action_authorization_binding()?;
    if !authority_rows_match_v1(
        plan.body.effects(),
        record.authorization_scope_id(),
        binding,
    ) {
        return Err(GlobalEconomicEffectPlanErrorV1::AuthorizationMismatch);
    }
    if !issue_burn_policy_matches_v1(
        plan.body.effects(),
        profile_occurrence
            .route_release()
            .content()
            .issue_burn_policy(),
    ) {
        return Err(GlobalEconomicEffectPlanErrorV1::IssueBurnPolicyMismatch);
    }
    Ok(())
}

fn validate_plan_replay_rows(
    plan: &GlobalEconomicEffectPlanV1,
    occurrence: &StateBoundEconomicCommandOccurrenceV1<'_>,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    let action = occurrence
        .profile_bound_occurrence()
        .occurrence()
        .content()
        .authorized_action();
    let record = action.record();
    let consumed = consumption_rows_v1(
        plan.body.effects(),
        GlobalOccurrenceConsumptionKindV1::ConsumedObject,
    );
    if consumed.as_slice() != record.consumed_object_ids() {
        return Err(GlobalEconomicEffectPlanErrorV1::ConsumedObjectMismatch);
    }
    let grant_spend =
        CommitmentV3::new(action.authorization_grant_spend()?.into_bytes()).map_err(|_| {
            GlobalEconomicEffectPlanErrorV1::InvalidDerivedCommitment("authorization_grant_spend")
        })?;
    if consumption_rows_v1(
        plan.body.effects(),
        GlobalOccurrenceConsumptionKindV1::AuthorizationGrantSpend,
    ) != [grant_spend]
    {
        return Err(GlobalEconomicEffectPlanErrorV1::AuthorizationGrantSpendMismatch);
    }
    Ok(())
}

fn effect_body_commitment_v1(
    post_state_root: GlobalEconomicStateRootV1,
    effect_semantics_root: CommitmentV3,
    reconciliations_root: CommitmentV3,
) -> Result<CommitmentV3, GlobalEconomicEffectPlanErrorV1> {
    let mut hasher = domain_hasher(EFFECT_BODY_COMMITMENT_DOMAIN_V1)?;
    hasher.update(GLOBAL_ECONOMIC_EFFECT_PLAN_VERSION_V1.to_be_bytes());
    hasher.update(post_state_root.as_bytes());
    hasher.update(effect_semantics_root.as_bytes());
    hasher.update(reconciliations_root.as_bytes());
    commitment(hasher, "global_economic_effect_body")
}

fn require_commitment(
    field: &'static str,
    actual: CommitmentV3,
    expected: CommitmentV3,
) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    if actual == expected {
        Ok(())
    } else {
        Err(GlobalEconomicEffectPlanErrorV1::CommitmentMismatch(field))
    }
}
