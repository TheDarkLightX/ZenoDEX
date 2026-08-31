use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v2, validate_schema_v2, validate_sorted_unique_tokens_v2, validate_token_v2,
    AbiResultV2, RootV2, ValidateCanonicalV2, GLOBAL_SETTLEMENT_ABI_V2,
};
use crate::effects::LaneIdV2;
use crate::resource_limits::validate_consumed_object_id_count_v2;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicCommandOccurrenceV2 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV2,
    pub height: u64,
    pub tx_index: u64,
    pub op_index: u64,
    pub command_kind: String,
    pub command_body_hash: RootV2,
    pub route_release_id: RootV2,
    pub subject_id: String,
    pub grant_root: RootV2,
    pub nonce: u64,
    pub profile_root: RootV2,
    pub pre_state_root: RootV2,
    pub consumed_object_ids: Vec<String>,
}

impl EconomicCommandOccurrenceV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_consumed_object_id_count_v2(
            self.consumed_object_ids.len(),
            "occurrence consumed object ids",
        )?;
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "economic command occurrence",
        )?;
        validate_token_v2(&self.chain_id, "occurrence chain id")?;
        self.deployment_root
            .validate("occurrence deployment root", false)?;
        validate_token_v2(&self.command_kind, "occurrence command kind")?;
        self.command_body_hash
            .validate("occurrence command body hash", false)?;
        self.route_release_id
            .validate("occurrence route release id", false)?;
        validate_token_v2(&self.subject_id, "occurrence subject id")?;
        self.grant_root.validate("occurrence grant root", false)?;
        self.profile_root
            .validate("occurrence profile root", false)?;
        self.pre_state_root
            .validate("occurrence pre-state root", false)?;
        validate_sorted_unique_tokens_v2(
            &self.consumed_object_ids,
            "occurrence consumed object ids",
            true,
        )
    }

    pub fn occurrence_id(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("global-economic-command-occurrence-v2", self)
    }

    pub fn replay_id(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        #[derive(Serialize)]
        struct ReplayBody<'a> {
            chain_id: &'a str,
            deployment_root: &'a RootV2,
            subject_id: &'a str,
            nonce: u64,
        }
        hash_global_v2(
            "global-economic-replay-id-v2",
            &ReplayBody {
                chain_id: &self.chain_id,
                deployment_root: &self.deployment_root,
                subject_id: &self.subject_id,
                nonce: self.nonce,
            },
        )
    }
}

impl ValidateCanonicalV2 for EconomicCommandOccurrenceV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneModuleTransitionJournalV2 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV2,
    pub profile_root: RootV2,
    pub writer_epoch: u64,
    pub lane_id: LaneIdV2,
    pub module_release_id: RootV2,
    pub command_occurrence_id: RootV2,
    pub pre_lane_root: RootV2,
    pub post_lane_root: RootV2,
    pub effect_plan_root: RootV2,
    pub private_port_root: RootV2,
    pub receipt_root: RootV2,
    pub terminal_obligations_root: RootV2,
    pub oracle_occurrence_plan_root: RootV2,
}

impl LaneModuleTransitionJournalV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "lane module transition journal",
        )?;
        validate_token_v2(&self.chain_id, "module journal chain id")?;
        self.deployment_root
            .validate("module journal deployment root", false)?;
        self.profile_root
            .validate("module journal profile root", false)?;
        self.module_release_id
            .validate("module journal module release id", false)?;
        self.command_occurrence_id
            .validate("module journal command occurrence id", false)?;
        self.pre_lane_root
            .validate("module journal pre lane root", true)?;
        self.post_lane_root
            .validate("module journal post lane root", true)?;
        self.effect_plan_root
            .validate("module journal effect plan root", false)?;
        self.private_port_root
            .validate("module journal private port root", true)?;
        self.receipt_root
            .validate("module journal receipt root", false)?;
        self.terminal_obligations_root
            .validate("module journal terminal obligations root", true)?;
        self.oracle_occurrence_plan_root
            .validate("module journal Oracle occurrence plan root", true)
    }

    pub fn journal_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("lane-module-transition-journal-v2", self)
    }
}

impl ValidateCanonicalV2 for LaneModuleTransitionJournalV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
