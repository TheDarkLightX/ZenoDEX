//! Closed canonical wire records for V2 SHADOW outcomes and candidates.
//!
//! Wire records are untrusted transport values. They validate every observable
//! field and derived root, yet never construct an accepted domain witness.

use serde::{Deserialize, Deserializer, Serialize};

use crate::asset_lane_coordinator_types::{
    AssetLaneCoordinatorRejectCodeV2, AssetLaneRouteV2, ALL_ASSET_LANE_COORDINATOR_REJECT_CODES_V2,
};
use crate::asset_lane_state::{
    AssetLaneContextV2, AssetLaneStateV2, ASSET_LANE_PROFILE_AUTHENTICATION_V2,
};
use crate::asset_origin_registry_types::{
    AssetOriginRegistrationRejectCodeV2, AssetOriginRegistryStateV2,
};
use crate::asset_transfer_types::{
    AssetTransferRejectCodeV2, ALL_ASSET_TRANSFER_REJECT_CODES_V2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
};
use crate::canonical::{
    canonical_bytes_v2, validate_token_v2, AbiErrorV2, AbiResultV2, RootV2, ValidateCanonicalV2,
    MAX_CANONICAL_INPUT_BYTES_V2,
};
use crate::effects::{ExternalOutboxEnqueueV2, GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::global_refinement::{
    GlobalEconomicStateEffectRefinementCandidateV2, GlobalEconomicStateEffectRefinementV2,
};
use crate::global_state::GlobalEconomicStateV2;
use crate::lifecycle::{GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2};
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleRejectCodeV2, ManagedAssetLifecycleStateV2,
    ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2, MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2,
};
use crate::outcome::{
    GlobalEconomicRefinementRejectCodeV2, GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2,
};
use crate::proof::{EconomicCommandOccurrenceV2, LaneModuleTransitionJournalV2};
use crate::resource_limits::validate_consumed_occurrence_count_v2;

/// Canonically encode one wire-transport value within the decoder's byte ceiling.
///
/// Internal state and root hashing deliberately continue to use
/// [`canonical_bytes_v2`] without this transport-only envelope.
pub fn canonical_wire_bytes_v2<T>(value: &T) -> AbiResultV2<Vec<u8>>
where
    T: Serialize + ValidateCanonicalV2,
{
    value.validate_canonical_v2()?;
    let bytes = canonical_bytes_v2(value)?;
    if bytes.len() > MAX_CANONICAL_INPUT_BYTES_V2 {
        return Err(AbiErrorV2::InvalidBounds("canonical wire bytes"));
    }
    Ok(bytes)
}

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicStateEffectRefinementWireV2 {
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effect_plan_root: RootV2,
    pub terminal_plan_root: RootV2,
    pub oracle_plan_root: RootV2,
    pub state_delta_root: RootV2,
    pub production_authority: String,
    pub refinement_root: RootV2,
}

impl GlobalEconomicStateEffectRefinementWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        GlobalEconomicStateEffectRefinementV2::validate_wire_observables(
            &self.pre_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
            &self.terminal_plan_root,
            &self.oracle_plan_root,
            &self.state_delta_root,
            &self.production_authority,
            &self.refinement_root,
        )
    }
}

impl ValidateCanonicalV2 for GlobalEconomicStateEffectRefinementWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicRefinementAcceptedWireV2 {
    pub witness: GlobalEconomicStateEffectRefinementWireV2,
    pub production_authority: String,
}

impl GlobalEconomicRefinementAcceptedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.witness.validate()?;
        if self.production_authority != GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement accepted wire production authority",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for GlobalEconomicRefinementAcceptedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicRefinementRejectedWireV2 {
    pub reject_code: GlobalEconomicRefinementRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effect_plan: GlobalEconomicEffectPlanV2,
    pub terminal_plan: GlobalTerminalObligationPlanV2,
    pub oracle_plan: GlobalOracleOccurrencePlanV2,
    pub consumed_occurrences: Vec<EconomicCommandOccurrenceV2>,
    pub outbox: Vec<ExternalOutboxEnqueueV2>,
    pub production_authority: String,
}

impl GlobalEconomicRefinementRejectedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("global refinement rejected wire pre-state root", false)?;
        self.post_state_root
            .validate("global refinement rejected wire post-state root", false)?;
        self.effect_plan.validate()?;
        self.terminal_plan.validate()?;
        self.oracle_plan.validate()?;
        if self.pre_state_root != self.post_state_root
            || !self.effect_plan.is_empty()
            || !self.terminal_plan.deltas.is_empty()
            || !self.oracle_plan.deltas.is_empty()
            || !self.consumed_occurrences.is_empty()
            || !self.outbox.is_empty()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement rejected wire is not a no-op",
            ));
        }
        if self.production_authority != GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement rejected wire production authority",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for GlobalEconomicRefinementRejectedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleAcceptedWireV2 {
    pub post_state: ManagedAssetLifecycleStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
    pub receipt_root: RootV2,
    pub production_authority: String,
}

impl ManagedAssetLifecycleAcceptedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        self.receipt_root
            .validate("managed asset accepted wire receipt root", false)?;
        let expected_lane_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.module_journal.post_lane_root.clone(),
        };
        if self.effects.is_empty()
            || self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || self.effects.lane_writes != vec![expected_lane_write]
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
            || self.receipt_root != self.module_journal.receipt_root
        {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset accepted wire bindings",
            ));
        }
        if self.production_authority != MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset accepted wire production authority",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleAcceptedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleRejectedWireV2 {
    pub code: ManagedAssetLifecycleRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub terminal_obligations_root: RootV2,
    pub oracle_occurrence_plan_root: RootV2,
    pub production_authority: String,
}

impl ManagedAssetLifecycleRejectedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("managed asset rejected wire pre-state root", false)?;
        self.post_state_root
            .validate("managed asset rejected wire post-state root", false)?;
        self.effects.validate()?;
        self.terminal_obligations_root.validate(
            "managed asset rejected wire terminal obligations root",
            true,
        )?;
        self.oracle_occurrence_plan_root.validate(
            "managed asset rejected wire Oracle occurrence plan root",
            true,
        )?;
        if self.pre_state_root != self.post_state_root
            || !self.effects.is_empty()
            || !self.terminal_obligations_root.is_zero()
            || !self.oracle_occurrence_plan_root.is_zero()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset rejected wire is not a no-op",
            ));
        }
        if self.production_authority != MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset rejected wire production authority",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleRejectedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationAcceptedWireV2 {
    pub post_state: AssetOriginRegistryStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
    pub production_authority: String,
}

impl AssetOriginRegistrationAcceptedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        let expected_lane_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.module_journal.post_lane_root.clone(),
        };
        if !self.effects.rows.is_empty()
            || !self.effects.asset_conservation.is_empty()
            || !self.effects.fee_conservation.is_empty()
            || !self.effects.external_outbox_enqueue.is_empty()
            || self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || self.effects.lane_writes != vec![expected_lane_write]
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin accepted wire bindings",
            ));
        }
        if self.production_authority != ASSET_LANE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin accepted wire production authority",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationAcceptedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetOriginRegistrationRejectedWireV2 {
    pub code: AssetOriginRegistrationRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
}

impl AssetOriginRegistrationRejectedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("asset origin rejected wire pre-state root", false)?;
        self.post_state_root
            .validate("asset origin rejected wire post-state root", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset origin rejected wire is not a no-op",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetOriginRegistrationRejectedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneContextWireV2 {
    pub writer_epoch: u64,
    pub module_release_id: RootV2,
    pub global_pre_state_root: RootV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub occurrence: Option<EconomicCommandOccurrenceV2>,
}

impl AssetLaneContextWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("asset lane context wire release", false)?;
        self.global_pre_state_root
            .validate("asset lane context wire global pre-state", false)?;
        if let Some(occurrence) = &self.occurrence {
            occurrence.validate()?;
        }
        Ok(())
    }

    pub fn validated_into_domain(self) -> AbiResultV2<AssetLaneContextV2> {
        self.validate()?;
        Ok(AssetLaneContextV2 {
            writer_epoch: self.writer_epoch,
            module_release_id: self.module_release_id,
            global_pre_state_root: self.global_pre_state_root,
            occurrence: self.occurrence,
        })
    }
}

impl ValidateCanonicalV2 for AssetLaneContextWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneAcceptedWireV2 {
    pub route: AssetLaneRouteV2,
    pub source_leaf_journal_root: RootV2,
    pub post_state: AssetLaneStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
    pub receipt_root: RootV2,
    pub production_authority: String,
    pub profile_authentication: String,
}

impl AssetLaneAcceptedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        if self.route == AssetLaneRouteV2::COORDINATOR {
            return Err(AbiErrorV2::InvalidBinding("asset lane accepted wire route"));
        }
        self.source_leaf_journal_root
            .validate("asset lane accepted wire source leaf journal", false)?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        self.receipt_root
            .validate("asset lane accepted wire receipt root", false)?;
        let expected_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.post_state.state_root()?,
        };
        if self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.effects.lane_writes != vec![expected_write]
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || !self.effects.external_outbox_enqueue.is_empty()
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
            || !self.post_state.policy_origin_bindings_hold()
            || self.receipt_root != self.module_journal.receipt_root
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane accepted wire bindings",
            ));
        }
        if self.production_authority != ASSET_LANE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane accepted wire production authority",
            ));
        }
        if self.profile_authentication != ASSET_LANE_PROFILE_AUTHENTICATION_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane accepted wire profile authentication",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetLaneAcceptedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneRejectedWireV2 {
    pub route: AssetLaneRouteV2,
    pub code: String,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub production_authority: String,
    pub profile_authentication: String,
}

impl AssetLaneRejectedWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.code, "asset lane rejected wire code")?;
        validate_asset_lane_reject_code_v2(self.route, &self.code)?;
        self.pre_state_root
            .validate("asset lane rejected wire pre-state root", false)?;
        self.post_state_root
            .validate("asset lane rejected wire post-state root", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane rejected wire is not a no-op",
            ));
        }
        if self.production_authority != ASSET_LANE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane rejected wire production authority",
            ));
        }
        if self.profile_authentication != ASSET_LANE_PROFILE_AUTHENTICATION_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane rejected wire profile authentication",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetLaneRejectedWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

fn validate_asset_lane_reject_code_v2(route: AssetLaneRouteV2, code: &str) -> AbiResultV2<()> {
    let known = match route {
        AssetLaneRouteV2::TRANSFER => ALL_ASSET_TRANSFER_REJECT_CODES_V2
            .iter()
            .any(|candidate: &AssetTransferRejectCodeV2| candidate.as_str() == code),
        AssetLaneRouteV2::MANAGED_LIFECYCLE => ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2
            .iter()
            .any(|candidate: &ManagedAssetLifecycleRejectCodeV2| candidate.as_str() == code),
        AssetLaneRouteV2::COORDINATOR => ALL_ASSET_LANE_COORDINATOR_REJECT_CODES_V2
            .iter()
            .any(|candidate: &AssetLaneCoordinatorRejectCodeV2| candidate.as_str() == code),
    };
    if known {
        Ok(())
    } else {
        Err(AbiErrorV2::InvalidBinding(
            "asset lane rejected wire route code",
        ))
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicStateEffectRefinementCandidateWireV2 {
    pub pre_state: GlobalEconomicStateV2,
    pub post_state: GlobalEconomicStateV2,
    pub effect_plan: GlobalEconomicEffectPlanV2,
    pub consumed_occurrences: Vec<EconomicCommandOccurrenceV2>,
    pub terminal_plan: GlobalTerminalObligationPlanV2,
    pub oracle_plan: GlobalOracleOccurrencePlanV2,
}

impl GlobalEconomicStateEffectRefinementCandidateWireV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_consumed_occurrence_count_v2(
            self.consumed_occurrences.len(),
            "global refinement consumed occurrences",
        )?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effect_plan.validate()?;
        self.terminal_plan.validate()?;
        self.oracle_plan.validate()?;
        let mut occurrence_ids = Vec::with_capacity(self.consumed_occurrences.len());
        for occurrence in &self.consumed_occurrences {
            occurrence.validate()?;
            occurrence_ids.push(occurrence.occurrence_id()?);
        }
        if occurrence_ids.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(AbiErrorV2::InvalidOrder(
                "global refinement occurrences must be ordered and unique",
            ));
        }
        if self.effect_plan.occurrence_consumptions != occurrence_ids {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement replay consumption mismatch",
            ));
        }
        Ok(())
    }

    pub fn validated_into_domain(
        &self,
    ) -> AbiResultV2<GlobalEconomicStateEffectRefinementCandidateV2<'_>> {
        self.validate()?;
        Ok(GlobalEconomicStateEffectRefinementCandidateV2 {
            pre_state: &self.pre_state,
            post_state: &self.post_state,
            effect_plan: &self.effect_plan,
            consumed_occurrences: &self.consumed_occurrences,
            terminal_plan: &self.terminal_plan,
            oracle_plan: &self.oracle_plan,
        })
    }
}

impl ValidateCanonicalV2 for GlobalEconomicStateEffectRefinementCandidateWireV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
