use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    EconomicCommandOccurrenceIdV1, EconomicLaneIdV1, EconomicProfileIdV1,
    GlobalEconomicStateRootV1, LaneModuleReleaseIdV1, LaneModuleTransitionJournalErrorV1,
    RouteReleaseIdV1,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3, EconomicActionIdV1, ProgramIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(transparent)]
pub struct LaneModuleRejectCodeV1(u32);

impl LaneModuleRejectCodeV1 {
    pub fn new(code: u32) -> Result<Self, LaneModuleTransitionJournalErrorV1> {
        if code == 0 {
            return Err(LaneModuleTransitionJournalErrorV1::ZeroRejectCode);
        }
        Ok(Self(code))
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

impl<'de> Deserialize<'de> for LaneModuleRejectCodeV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(u32::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneModuleAcceptedTransitionInputV1 {
    pub global_post_state_root: GlobalEconomicStateRootV1,
    pub global_effect_plan_commitment: CommitmentV3,
    pub lane_post_state_root: CommitmentV3,
    pub lane_effect_rows_root: CommitmentV3,
    pub state_transition_root: CommitmentV3,
    pub private_input_ports_root: CommitmentV3,
    pub private_output_ports_root: CommitmentV3,
    pub terminal_obligations_root: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaneModuleAcceptedTransitionV1 {
    global_post_state_root: GlobalEconomicStateRootV1,
    global_effect_plan_commitment: CommitmentV3,
    lane_post_state_root: CommitmentV3,
    lane_effect_rows_root: CommitmentV3,
    state_transition_root: CommitmentV3,
    private_input_ports_root: CommitmentV3,
    private_output_ports_root: CommitmentV3,
    terminal_obligations_root: CommitmentV3,
}

impl LaneModuleAcceptedTransitionV1 {
    pub const fn new(input: LaneModuleAcceptedTransitionInputV1) -> Self {
        Self {
            global_post_state_root: input.global_post_state_root,
            global_effect_plan_commitment: input.global_effect_plan_commitment,
            lane_post_state_root: input.lane_post_state_root,
            lane_effect_rows_root: input.lane_effect_rows_root,
            state_transition_root: input.state_transition_root,
            private_input_ports_root: input.private_input_ports_root,
            private_output_ports_root: input.private_output_ports_root,
            terminal_obligations_root: input.terminal_obligations_root,
        }
    }

    pub const fn global_post_state_root(self) -> GlobalEconomicStateRootV1 {
        self.global_post_state_root
    }
    pub const fn global_effect_plan_commitment(self) -> CommitmentV3 {
        self.global_effect_plan_commitment
    }
    pub const fn lane_post_state_root(self) -> CommitmentV3 {
        self.lane_post_state_root
    }
    pub const fn lane_effect_rows_root(self) -> CommitmentV3 {
        self.lane_effect_rows_root
    }
    pub const fn state_transition_root(self) -> CommitmentV3 {
        self.state_transition_root
    }
    pub const fn private_input_ports_root(self) -> CommitmentV3 {
        self.private_input_ports_root
    }
    pub const fn private_output_ports_root(self) -> CommitmentV3 {
        self.private_output_ports_root
    }
    pub const fn terminal_obligations_root(self) -> CommitmentV3 {
        self.terminal_obligations_root
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
// This bounded proof-ABI value stays inline so guest and host construction do
// not require heap allocation merely to represent the accepted variant.
#[allow(clippy::large_enum_variant)]
pub enum LaneModuleTransitionOutcomeV1 {
    Accepted(LaneModuleAcceptedTransitionV1),
    Rejected(LaneModuleRejectCodeV1),
}

impl LaneModuleTransitionOutcomeV1 {
    pub const fn kind_code(self) -> u8 {
        match self {
            Self::Accepted(_) => 0,
            Self::Rejected(_) => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LaneModuleTransitionJournalInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub profile_id: EconomicProfileIdV1,
    pub writer_epoch: u64,
    pub occurrence_id: EconomicCommandOccurrenceIdV1,
    pub route_release_id: RouteReleaseIdV1,
    pub economic_action_id: EconomicActionIdV1,
    pub lane_id: EconomicLaneIdV1,
    pub module_release_id: LaneModuleReleaseIdV1,
    pub guest_image_id: ProgramIdV3,
    pub state_schema_root: CommitmentV3,
    pub command_schema_root: CommitmentV3,
    pub effect_schema_root: CommitmentV3,
    pub private_port_schema_root: CommitmentV3,
    pub command_variants_root: CommitmentV3,
    pub spec_root: CommitmentV3,
    pub source_root: CommitmentV3,
    pub toolchain_root: CommitmentV3,
    pub receipt_journal_schema_root: CommitmentV3,
    pub input_port_schema_root: CommitmentV3,
    pub output_port_schema_root: CommitmentV3,
    pub global_pre_state_root: GlobalEconomicStateRootV1,
    pub lane_pre_state_root: CommitmentV3,
    pub outcome: LaneModuleTransitionOutcomeV1,
}
