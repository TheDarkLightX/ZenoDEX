use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    EconomicCommandOccurrenceIdV1, EconomicLaneIdV1, EconomicProfileIdV1,
    GlobalEconomicStateRootV1, LaneModuleReleaseIdV1, LaneModuleTransitionJournalErrorV1,
    LaneModuleTransitionJournalInputV1, LaneModuleTransitionOutcomeV1, RouteReleaseIdV1,
    LANE_MODULE_TRANSITION_JOURNAL_VERSION_V1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3, EconomicActionIdV1, ProgramIdV3};

use super::lane_module_transition_journal_hash::journal_hash_v1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "a lane journal is ordinary data until a release-aware receipt verifier accepts it"]
pub struct LaneModuleTransitionJournalV1 {
    journal_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    route_release_id: RouteReleaseIdV1,
    economic_action_id: EconomicActionIdV1,
    lane_id: EconomicLaneIdV1,
    module_release_id: LaneModuleReleaseIdV1,
    guest_image_id: ProgramIdV3,
    state_schema_root: CommitmentV3,
    command_schema_root: CommitmentV3,
    effect_schema_root: CommitmentV3,
    private_port_schema_root: CommitmentV3,
    command_variants_root: CommitmentV3,
    spec_root: CommitmentV3,
    source_root: CommitmentV3,
    toolchain_root: CommitmentV3,
    receipt_journal_schema_root: CommitmentV3,
    input_port_schema_root: CommitmentV3,
    output_port_schema_root: CommitmentV3,
    global_pre_state_root: GlobalEconomicStateRootV1,
    lane_pre_state_root: CommitmentV3,
    outcome: LaneModuleTransitionOutcomeV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LaneModuleTransitionJournalWireV1 {
    journal_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    profile_id: EconomicProfileIdV1,
    writer_epoch: u64,
    occurrence_id: EconomicCommandOccurrenceIdV1,
    route_release_id: RouteReleaseIdV1,
    economic_action_id: EconomicActionIdV1,
    lane_id: EconomicLaneIdV1,
    module_release_id: LaneModuleReleaseIdV1,
    guest_image_id: ProgramIdV3,
    state_schema_root: CommitmentV3,
    command_schema_root: CommitmentV3,
    effect_schema_root: CommitmentV3,
    private_port_schema_root: CommitmentV3,
    command_variants_root: CommitmentV3,
    spec_root: CommitmentV3,
    source_root: CommitmentV3,
    toolchain_root: CommitmentV3,
    receipt_journal_schema_root: CommitmentV3,
    input_port_schema_root: CommitmentV3,
    output_port_schema_root: CommitmentV3,
    global_pre_state_root: GlobalEconomicStateRootV1,
    lane_pre_state_root: CommitmentV3,
    outcome: LaneModuleTransitionOutcomeV1,
}

impl LaneModuleTransitionJournalV1 {
    pub fn new(
        input: LaneModuleTransitionJournalInputV1,
    ) -> Result<Self, LaneModuleTransitionJournalErrorV1> {
        Self::from_parts(LANE_MODULE_TRANSITION_JOURNAL_VERSION_V1, input)
    }

    fn from_parts(
        journal_version: u16,
        input: LaneModuleTransitionJournalInputV1,
    ) -> Result<Self, LaneModuleTransitionJournalErrorV1> {
        let journal = Self {
            journal_version,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            profile_id: input.profile_id,
            writer_epoch: input.writer_epoch,
            occurrence_id: input.occurrence_id,
            route_release_id: input.route_release_id,
            economic_action_id: input.economic_action_id,
            lane_id: input.lane_id,
            module_release_id: input.module_release_id,
            guest_image_id: input.guest_image_id,
            state_schema_root: input.state_schema_root,
            command_schema_root: input.command_schema_root,
            effect_schema_root: input.effect_schema_root,
            private_port_schema_root: input.private_port_schema_root,
            command_variants_root: input.command_variants_root,
            spec_root: input.spec_root,
            source_root: input.source_root,
            toolchain_root: input.toolchain_root,
            receipt_journal_schema_root: input.receipt_journal_schema_root,
            input_port_schema_root: input.input_port_schema_root,
            output_port_schema_root: input.output_port_schema_root,
            global_pre_state_root: input.global_pre_state_root,
            lane_pre_state_root: input.lane_pre_state_root,
            outcome: input.outcome,
        };
        journal.validate_self_consistency()?;
        Ok(journal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), LaneModuleTransitionJournalErrorV1> {
        if self.journal_version != LANE_MODULE_TRANSITION_JOURNAL_VERSION_V1 {
            return Err(LaneModuleTransitionJournalErrorV1::InvalidJournalVersion(
                self.journal_version,
            ));
        }
        if let LaneModuleTransitionOutcomeV1::Accepted(accepted) = self.outcome {
            if accepted.global_post_state_root() == self.global_pre_state_root {
                return Err(LaneModuleTransitionJournalErrorV1::PreAndPostGlobalStateMatch);
            }
        }
        Ok(())
    }

    pub fn canonical_journal_hash(
        &self,
    ) -> Result<CommitmentV3, LaneModuleTransitionJournalErrorV1> {
        self.validate_self_consistency()?;
        journal_hash_v1(self)
    }

    pub const fn journal_version(&self) -> u16 {
        self.journal_version
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
    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }
    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        self.lane_id
    }
    pub const fn module_release_id(&self) -> LaneModuleReleaseIdV1 {
        self.module_release_id
    }
    pub const fn guest_image_id(&self) -> ProgramIdV3 {
        self.guest_image_id
    }
    pub const fn state_schema_root(&self) -> CommitmentV3 {
        self.state_schema_root
    }
    pub const fn command_schema_root(&self) -> CommitmentV3 {
        self.command_schema_root
    }
    pub const fn effect_schema_root(&self) -> CommitmentV3 {
        self.effect_schema_root
    }
    pub const fn private_port_schema_root(&self) -> CommitmentV3 {
        self.private_port_schema_root
    }
    pub const fn command_variants_root(&self) -> CommitmentV3 {
        self.command_variants_root
    }
    pub const fn spec_root(&self) -> CommitmentV3 {
        self.spec_root
    }
    pub const fn source_root(&self) -> CommitmentV3 {
        self.source_root
    }
    pub const fn toolchain_root(&self) -> CommitmentV3 {
        self.toolchain_root
    }
    pub const fn receipt_journal_schema_root(&self) -> CommitmentV3 {
        self.receipt_journal_schema_root
    }
    pub const fn input_port_schema_root(&self) -> CommitmentV3 {
        self.input_port_schema_root
    }
    pub const fn output_port_schema_root(&self) -> CommitmentV3 {
        self.output_port_schema_root
    }
    pub const fn global_pre_state_root(&self) -> GlobalEconomicStateRootV1 {
        self.global_pre_state_root
    }
    pub const fn lane_pre_state_root(&self) -> CommitmentV3 {
        self.lane_pre_state_root
    }
    pub const fn outcome(&self) -> LaneModuleTransitionOutcomeV1 {
        self.outcome
    }
}

impl<'de> Deserialize<'de> for LaneModuleTransitionJournalV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = LaneModuleTransitionJournalWireV1::deserialize(deserializer)?;
        Self::from_parts(
            wire.journal_version,
            LaneModuleTransitionJournalInputV1 {
                application_id: wire.application_id,
                chain_or_domain_id: wire.chain_or_domain_id,
                profile_id: wire.profile_id,
                writer_epoch: wire.writer_epoch,
                occurrence_id: wire.occurrence_id,
                route_release_id: wire.route_release_id,
                economic_action_id: wire.economic_action_id,
                lane_id: wire.lane_id,
                module_release_id: wire.module_release_id,
                guest_image_id: wire.guest_image_id,
                state_schema_root: wire.state_schema_root,
                command_schema_root: wire.command_schema_root,
                effect_schema_root: wire.effect_schema_root,
                private_port_schema_root: wire.private_port_schema_root,
                command_variants_root: wire.command_variants_root,
                spec_root: wire.spec_root,
                source_root: wire.source_root,
                toolchain_root: wire.toolchain_root,
                receipt_journal_schema_root: wire.receipt_journal_schema_root,
                input_port_schema_root: wire.input_port_schema_root,
                output_port_schema_root: wire.output_port_schema_root,
                global_pre_state_root: wire.global_pre_state_root,
                lane_pre_state_root: wire.lane_pre_state_root,
                outcome: wire.outcome,
            },
        )
        .map_err(de::Error::custom)
    }
}
