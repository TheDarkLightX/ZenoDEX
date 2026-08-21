use serde::{Deserialize, Serialize};

use crate::canonical::{
    canonical_bytes_v1, hash_global_v1, validate_root_sequence_v1, validate_schema_v1,
    validate_sorted_unique_tokens_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
    MAX_CYCLE_BUDGET_V1, MAX_EPOCH_COMMANDS_V1, MAX_EPOCH_LEAF_OCCURRENCES_V1,
    MAX_JOURNAL_BYTES_V1, MAX_ROUTE_MODULES_V1,
};
use crate::release::LaneIdV1;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandOccurrenceV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub height: u64,
    pub tx_index: u64,
    pub op_index: u64,
    pub command_kind: String,
    pub route_release_id: RootV1,
    pub subject_id: String,
    pub grant_root: RootV1,
    pub nonce: u64,
    pub profile_root: RootV1,
    pub pre_state_root: RootV1,
    pub consumed_object_ids: Vec<String>,
}

#[derive(Serialize)]
struct ReplayIdContentV1<'a> {
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    subject_id: &'a str,
    nonce: u64,
}

impl EconomicCommandOccurrenceV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "occurrence chain id")?;
        validate_token_v1(&self.command_kind, "occurrence command kind")?;
        validate_token_v1(&self.subject_id, "occurrence subject id")?;
        for root in [
            &self.deployment_root,
            &self.route_release_id,
            &self.grant_root,
            &self.profile_root,
            &self.pre_state_root,
        ] {
            root.validate("occurrence root", false)?;
        }
        validate_sorted_unique_tokens_v1(
            &self.consumed_object_ids,
            "occurrence consumed object ids",
            true,
        )
    }

    pub fn occurrence_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-economic-command-occurrence-v1", self)
    }

    pub fn replay_id(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1(
            "global-economic-replay-id-v1",
            &ReplayIdContentV1 {
                chain_id: &self.chain_id,
                deployment_root: &self.deployment_root,
                subject_id: &self.subject_id,
                nonce: self.nonce,
            },
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneModuleTransitionJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub lane_id: LaneIdV1,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub pre_lane_root: RootV1,
    pub post_lane_root: RootV1,
    pub effect_plan_root: RootV1,
    pub private_port_root: RootV1,
    pub receipt_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl LaneModuleTransitionJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "module journal chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.module_release_id,
            &self.command_occurrence_id,
            &self.effect_plan_root,
            &self.receipt_root,
        ] {
            root.validate("module journal required root", false)?;
        }
        for root in [
            &self.pre_lane_root,
            &self.post_lane_root,
            &self.private_port_root,
            &self.terminal_obligations_root,
        ] {
            root.validate("module journal optional root", true)?;
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("lane-module-transition-journal-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneCompositionJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub lane_id: LaneIdV1,
    pub coordinator_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub ordered_module_journal_roots: Vec<RootV1>,
    pub pre_lane_root: RootV1,
    pub post_lane_root: RootV1,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl LaneCompositionJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "lane journal chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.coordinator_release_id,
            &self.command_occurrence_id,
            &self.effect_plan_root,
        ] {
            root.validate("lane journal required root", false)?;
        }
        for root in [
            &self.pre_lane_root,
            &self.post_lane_root,
            &self.terminal_obligations_root,
        ] {
            root.validate("lane journal optional root", true)?;
        }
        validate_semantic_root_set_v1(
            &self.ordered_module_journal_roots,
            "lane module journal roots",
        )
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("lane-composition-journal-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RouteCompositionJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub ordered_lane_journal_roots: Vec<RootV1>,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl RouteCompositionJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "route journal chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.pre_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
        ] {
            root.validate("route journal required root", false)?;
        }
        self.terminal_obligations_root
            .validate("route terminal obligations root", true)?;
        validate_semantic_root_set_v1(&self.ordered_lane_journal_roots, "route lane journal roots")
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("route-composition-journal-v1", self)
    }
}

pub const COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1: &str = "zenodex/command-aggregation-journal/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CommandAggregationJournalV1 {
    pub schema: String,
    pub settlement_abi: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub epoch_height: u64,
    pub group_index: u64,
    pub first_command_index: u64,
    pub ordered_occurrence_ids: Vec<RootV1>,
    pub ordered_route_journal_roots: Vec<RootV1>,
    pub ordered_route_assumption_roots: Vec<RootV1>,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub module_leaf_occurrences: u64,
}

impl CommandAggregationJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_schema_v1(&self.settlement_abi)?;
        validate_token_v1(&self.chain_id, "command aggregation chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.pre_state_root,
            &self.post_state_root,
        ] {
            root.validate("command aggregation required root", false)?;
        }
        let command_count = self.validate_route_vectors_v1()?;
        self.validate_position_and_leaf_bounds_v1(command_count)
    }

    fn validate_route_vectors_v1(&self) -> AbiResultV1<u64> {
        let command_count = self.ordered_occurrence_ids.len();
        if !(1..=MAX_ROUTE_MODULES_V1).contains(&command_count)
            || self.ordered_route_journal_roots.len() != command_count
            || self.ordered_route_assumption_roots.len() != command_count
        {
            return Err(AbiErrorV1::InvalidBounds("command aggregation route count"));
        }
        validate_root_sequence_v1(
            &self.ordered_occurrence_ids,
            "command aggregation occurrences",
            true,
        )?;
        validate_root_sequence_v1(
            &self.ordered_route_journal_roots,
            "command aggregation route journals",
            true,
        )?;
        validate_root_sequence_v1(
            &self.ordered_route_assumption_roots,
            "command aggregation route assumptions",
            true,
        )?;
        u64::try_from(command_count)
            .map_err(|_| AbiErrorV1::InvalidBounds("command aggregation route count width"))
    }

    fn validate_position_and_leaf_bounds_v1(&self, command_count: u64) -> AbiResultV1<()> {
        let expected_start = self
            .group_index
            .checked_mul(8)
            .ok_or(AbiErrorV1::InvalidBounds("command aggregation first index"))?;
        let command_end = self
            .first_command_index
            .checked_add(command_count)
            .ok_or(AbiErrorV1::InvalidBounds("command aggregation command end"))?;
        let maximum_leaf_occurrences =
            command_count
                .checked_mul(8)
                .ok_or(AbiErrorV1::InvalidBounds(
                    "command aggregation maximum leaf occurrences",
                ))?;
        let maximum_epoch_commands = u64::try_from(MAX_EPOCH_COMMANDS_V1)
            .map_err(|_| AbiErrorV1::InvalidBounds("epoch command count width"))?;
        if self.group_index >= 8 || self.first_command_index != expected_start {
            return Err(AbiErrorV1::InvalidOrder(
                "command aggregation group position",
            ));
        }
        if command_end > maximum_epoch_commands
            || self.module_leaf_occurrences < command_count
            || self.module_leaf_occurrences > maximum_leaf_occurrences
        {
            return Err(AbiErrorV1::InvalidBounds(
                "command aggregation occurrence bounds",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("command-aggregation-journal-v1", self)
    }
}

fn validate_semantic_root_set_v1(values: &[RootV1], field: &'static str) -> AbiResultV1<()> {
    if !(1..=MAX_ROUTE_MODULES_V1).contains(&values.len()) {
        return Err(AbiErrorV1::InvalidBounds(field));
    }
    validate_root_sequence_v1(values, field, true)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ReceiptKindV1 {
    SUCCINCT,
    COMPOSITE,
    CONDITIONAL,
    FAKE,
    DEVELOPMENT,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicEpochCertificateV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub height: u64,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub ordered_occurrence_ids: Vec<RootV1>,
    pub ordered_route_journal_roots: Vec<RootV1>,
    pub ordered_route_assumption_roots: Vec<RootV1>,
    pub module_leaf_occurrences: u64,
    pub aggregation_fanout: u64,
    pub aggregation_levels: u64,
    pub effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
    pub body_commitment: RootV1,
    pub data_availability_root: RootV1,
    pub finality_root: RootV1,
    pub source_manifest_root: RootV1,
    pub toolchain_manifest_root: RootV1,
    pub root_image_id: RootV1,
    pub receipt_root: RootV1,
    pub receipt_kind: ReceiptKindV1,
    pub journal_bytes: u64,
    pub cycle_budget: u64,
}

#[derive(Serialize)]
struct GlobalEconomicEpochJournalV1<'a> {
    schema: &'a str,
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    profile_root: &'a RootV1,
    writer_epoch: u64,
    height: u64,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    ordered_occurrence_ids: &'a [RootV1],
    ordered_route_journal_roots: &'a [RootV1],
    ordered_route_assumption_roots: &'a [RootV1],
    module_leaf_occurrences: u64,
    aggregation_fanout: u64,
    aggregation_levels: u64,
    effect_plan_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
    body_commitment: &'a RootV1,
    data_availability_root: &'a RootV1,
    finality_root: &'a RootV1,
    source_manifest_root: &'a RootV1,
    toolchain_manifest_root: &'a RootV1,
    root_image_id: &'a RootV1,
}

impl GlobalEconomicEpochCertificateV1 {
    fn journal(&self) -> GlobalEconomicEpochJournalV1<'_> {
        GlobalEconomicEpochJournalV1 {
            schema: &self.schema,
            chain_id: &self.chain_id,
            deployment_root: &self.deployment_root,
            profile_root: &self.profile_root,
            writer_epoch: self.writer_epoch,
            height: self.height,
            pre_state_root: &self.pre_state_root,
            post_state_root: &self.post_state_root,
            ordered_occurrence_ids: &self.ordered_occurrence_ids,
            ordered_route_journal_roots: &self.ordered_route_journal_roots,
            ordered_route_assumption_roots: &self.ordered_route_assumption_roots,
            module_leaf_occurrences: self.module_leaf_occurrences,
            aggregation_fanout: self.aggregation_fanout,
            aggregation_levels: self.aggregation_levels,
            effect_plan_root: &self.effect_plan_root,
            terminal_obligations_root: &self.terminal_obligations_root,
            body_commitment: &self.body_commitment,
            data_availability_root: &self.data_availability_root,
            finality_root: &self.finality_root,
            source_manifest_root: &self.source_manifest_root,
            toolchain_manifest_root: &self.toolchain_manifest_root,
            root_image_id: &self.root_image_id,
        }
    }

    pub fn canonical_journal_bytes(&self) -> AbiResultV1<Vec<u8>> {
        canonical_bytes_v1(&self.journal())
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "epoch chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.pre_state_root,
            &self.post_state_root,
            &self.effect_plan_root,
            &self.body_commitment,
            &self.data_availability_root,
            &self.finality_root,
            &self.source_manifest_root,
            &self.toolchain_manifest_root,
            &self.root_image_id,
            &self.receipt_root,
        ] {
            root.validate("epoch required root", false)?;
        }
        self.terminal_obligations_root
            .validate("epoch terminal obligations root", true)?;
        if !(1..=MAX_EPOCH_COMMANDS_V1).contains(&self.ordered_occurrence_ids.len()) {
            return Err(AbiErrorV1::InvalidBounds("epoch command count"));
        }
        validate_root_sequence_v1(&self.ordered_occurrence_ids, "epoch occurrences", true)?;
        validate_root_sequence_v1(
            &self.ordered_route_journal_roots,
            "epoch route journals",
            true,
        )?;
        validate_root_sequence_v1(
            &self.ordered_route_assumption_roots,
            "epoch route assumptions",
            true,
        )?;
        if self.ordered_route_journal_roots.len() != self.ordered_occurrence_ids.len()
            || self.ordered_route_assumption_roots.len() != self.ordered_occurrence_ids.len()
        {
            return Err(AbiErrorV1::InvalidBinding(
                "epoch occurrence route and assumption cardinality",
            ));
        }
        let command_count = u64::try_from(self.ordered_occurrence_ids.len())
            .map_err(|_| AbiErrorV1::InvalidBounds("epoch command count width"))?;
        if self.module_leaf_occurrences == 0
            || self.module_leaf_occurrences > MAX_EPOCH_LEAF_OCCURRENCES_V1
            || self.module_leaf_occurrences < command_count
        {
            return Err(AbiErrorV1::InvalidBounds("epoch module leaf occurrences"));
        }
        if self.aggregation_fanout != 8 || self.aggregation_levels > 2 {
            return Err(AbiErrorV1::InvalidBounds("epoch aggregation shape"));
        }
        if self.journal_bytes == 0 || self.journal_bytes > MAX_JOURNAL_BYTES_V1 {
            return Err(AbiErrorV1::InvalidBounds("epoch journal bytes"));
        }
        if self.cycle_budget == 0 || self.cycle_budget > MAX_CYCLE_BUDGET_V1 {
            return Err(AbiErrorV1::InvalidBounds("epoch cycle budget"));
        }
        let actual_journal_bytes = self.canonical_journal_bytes()?.len();
        if u64::try_from(actual_journal_bytes).ok() != Some(self.journal_bytes) {
            return Err(AbiErrorV1::InvalidBinding(
                "epoch canonical journal byte count",
            ));
        }
        Ok(())
    }

    pub fn certificate_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-economic-epoch-certificate-v1", self)
    }
}
