use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::release::{
    EconomicProfileSnapshotV1, LaneIdV1, LaneRegistryV1, ReleaseStatusV1, ALL_LANE_IDS_V1,
};

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneStateRootV1 {
    pub lane_id: LaneIdV1,
    pub module_release_id: RootV1,
    pub enabled: bool,
    pub state_root: RootV1,
}

impl LaneStateRootV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.module_release_id
            .validate("lane state module release id", false)?;
        self.state_root.validate("lane state root", true)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicAmountV1 {
    pub owner: String,
    pub asset: String,
    pub custody_domain: String,
    pub amount_atoms: u128,
}

impl EconomicAmountV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.owner, "economic amount owner")?;
        validate_token_v1(&self.asset, "economic amount asset")?;
        validate_token_v1(&self.custody_domain, "economic amount custody domain")
    }

    fn key(&self) -> (String, String, String) {
        (
            self.asset.clone(),
            self.owner.clone(),
            self.custody_domain.clone(),
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetSupplyV1 {
    pub asset: String,
    pub amount_atoms: u128,
}

impl AssetSupplyV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "supply asset")
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OracleOccurrenceStateV1 {
    pub oracle_id: String,
    pub occurrence_root: RootV1,
    pub observed_height: u64,
    pub finalized: bool,
}

impl OracleOccurrenceStateV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.oracle_id, "oracle id")?;
        self.occurrence_root
            .validate("oracle occurrence root", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayStateV1 {
    pub replay_id: String,
    pub occurrence_id: RootV1,
}

impl ReplayStateV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.replay_id, "replay id")?;
        self.occurrence_id.validate("replay occurrence id", false)
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum TerminalObligationStatusV1 {
    OPEN,
    DRAINED,
    TOMBSTONED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TerminalObligationV1 {
    pub obligation_id: String,
    pub lane_id: LaneIdV1,
    pub claimant: String,
    pub asset: String,
    pub amount_atoms: u128,
    pub status: TerminalObligationStatusV1,
}

impl TerminalObligationV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.obligation_id, "terminal obligation id")?;
        validate_token_v1(&self.claimant, "terminal obligation claimant")?;
        validate_token_v1(&self.asset, "terminal obligation asset")
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum OutboxStatusV1 {
    PENDING,
    ACKNOWLEDGED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OutboxStateV1 {
    pub effect_id: RootV1,
    pub destination_id: String,
    pub payload_hash: RootV1,
    pub commit_id: RootV1,
    pub status: OutboxStatusV1,
}

impl OutboxStateV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.effect_id.validate("outbox effect id", false)?;
        validate_token_v1(&self.destination_id, "outbox destination id")?;
        self.payload_hash.validate("outbox payload hash", false)?;
        self.commit_id.validate("outbox commit id", false)
    }
}

fn validate_ordered_by_v1<T, K: Ord>(
    values: &[T],
    field: &'static str,
    mut key: impl FnMut(&T) -> K,
    mut validate: impl FnMut(&T) -> AbiResultV1<()>,
) -> AbiResultV1<()> {
    for value in values {
        validate(value)?;
    }
    if values.windows(2).any(|pair| key(&pair[0]) >= key(&pair[1])) {
        return Err(AbiErrorV1::InvalidOrder(field));
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicStateV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub writer_epoch: u64,
    pub height: u64,
    pub profile_root: RootV1,
    pub lane_roots: Vec<LaneStateRootV1>,
    pub balances: Vec<EconomicAmountV1>,
    pub supplies: Vec<AssetSupplyV1>,
    pub custody: Vec<EconomicAmountV1>,
    pub liabilities: Vec<EconomicAmountV1>,
    pub reserves: Vec<EconomicAmountV1>,
    pub oracle_occurrences: Vec<OracleOccurrenceStateV1>,
    pub replay_state: Vec<ReplayStateV1>,
    pub terminal_obligations: Vec<TerminalObligationV1>,
    pub history_root: RootV1,
    pub outbox: Vec<OutboxStateV1>,
}

impl GlobalEconomicStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "global state chain id")?;
        self.deployment_root
            .validate("global state deployment root", false)?;
        self.profile_root
            .validate("global state profile root", false)?;
        if self.lane_roots.len() != ALL_LANE_IDS_V1.len()
            || self
                .lane_roots
                .iter()
                .map(|lane| lane.lane_id)
                .ne(ALL_LANE_IDS_V1)
        {
            return Err(AbiErrorV1::InvalidOrder("global state lane roots"));
        }
        for lane in &self.lane_roots {
            lane.validate()?;
        }
        for (field, amounts) in [
            ("global balances", self.balances.as_slice()),
            ("global custody", self.custody.as_slice()),
            ("global liabilities", self.liabilities.as_slice()),
            ("global reserves", self.reserves.as_slice()),
        ] {
            validate_ordered_by_v1(
                amounts,
                field,
                EconomicAmountV1::key,
                EconomicAmountV1::validate,
            )?;
        }
        validate_ordered_by_v1(
            &self.supplies,
            "global supplies",
            |row| row.asset.clone(),
            AssetSupplyV1::validate,
        )?;
        validate_ordered_by_v1(
            &self.oracle_occurrences,
            "global oracle occurrences",
            |row| row.oracle_id.clone(),
            OracleOccurrenceStateV1::validate,
        )?;
        validate_ordered_by_v1(
            &self.replay_state,
            "global replay state",
            |row| row.replay_id.clone(),
            ReplayStateV1::validate,
        )?;
        if self
            .replay_state
            .iter()
            .map(|row| &row.occurrence_id)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != self.replay_state.len()
        {
            return Err(AbiErrorV1::InvalidOrder("global replay occurrence ids"));
        }
        validate_ordered_by_v1(
            &self.terminal_obligations,
            "global terminal obligations",
            |row| row.obligation_id.clone(),
            TerminalObligationV1::validate,
        )?;
        self.history_root.validate("global history root", true)?;
        validate_ordered_by_v1(
            &self.outbox,
            "global outbox",
            |row| row.effect_id.clone(),
            OutboxStateV1::validate,
        )
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-economic-state-root-v1", self)
    }

    pub fn validate_profile(&self, profile: &EconomicProfileSnapshotV1) -> AbiResultV1<()> {
        profile.validate()?;
        if self.profile_root != profile.profile_id || self.writer_epoch != profile.authority_epoch {
            return Err(AbiErrorV1::InvalidBinding("global state profile"));
        }
        Ok(())
    }

    pub fn validate_profile_registry(
        &self,
        profile: &EconomicProfileSnapshotV1,
        lanes: &LaneRegistryV1,
    ) -> AbiResultV1<()> {
        self.validate_profile(profile)?;
        lanes.validate()?;
        if profile.lane_registry_root != lanes.registry_root()? {
            return Err(AbiErrorV1::InvalidBinding(
                "global state lane registry root",
            ));
        }
        for (lane_state, release) in self.lane_roots.iter().zip(lanes.releases.iter()) {
            let expected_enabled =
                release.status == ReleaseStatusV1::ACTIVE_NEW && release.accepts_new_objects;
            if lane_state.lane_id != release.lane_id
                || lane_state.module_release_id != release.release_id
                || lane_state.enabled != expected_enabled
            {
                return Err(AbiErrorV1::InvalidBinding("global state lane release"));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicStateRootV1 {
    pub root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub height: u64,
}

impl GlobalEconomicStateRootV1 {
    pub fn from_state(state: &GlobalEconomicStateV1) -> AbiResultV1<Self> {
        Ok(Self {
            root: state.state_root()?,
            profile_root: state.profile_root.clone(),
            writer_epoch: state.writer_epoch,
            height: state.height,
        })
    }
}
