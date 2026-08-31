use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v2, validate_schema_v2, validate_token_v2, AbiErrorV2, AbiResultV2, RootV2,
    ValidateCanonicalV2, GLOBAL_SETTLEMENT_ABI_V2,
};
use crate::effects::LaneIdV2;
use crate::lifecycle::{OracleOccurrenceStateV2, TerminalObligationV2};
use crate::state::{AssetSupplyV2, EconomicAmountV2};

pub const MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2: usize = 65_536;
pub const MAX_GLOBAL_SUPPLY_ROWS_V2: usize = 4_096;
pub const MAX_GLOBAL_ORACLE_ROWS_V2: usize = 4_096;
pub const MAX_GLOBAL_REPLAY_ROWS_V2: usize = 65_536;
pub const MAX_GLOBAL_TERMINAL_ROWS_V2: usize = 65_536;
pub const MAX_GLOBAL_OUTBOX_ROWS_V2: usize = 65_536;

pub const ALL_LANE_IDS_V2: [LaneIdV2; 12] = [
    LaneIdV2::ASSET_TRANSFER,
    LaneIdV2::SPOT_LIQUIDITY,
    LaneIdV2::FARM_INCENTIVES,
    LaneIdV2::ZDEX_TOKENOMICS,
    LaneIdV2::ZUSD_MONETARY,
    LaneIdV2::PERPS_MARKET,
    LaneIdV2::ORACLE_MARKET,
    LaneIdV2::SEALED_AUCTION,
    LaneIdV2::STRATEGY_ESCROW,
    LaneIdV2::PROOF_REWARDS,
    LaneIdV2::EXTERNAL_CUSTODY,
    LaneIdV2::GOVERNANCE_MIGRATION,
];

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneStateRootV2 {
    pub lane_id: LaneIdV2,
    pub module_release_id: RootV2,
    pub enabled: bool,
    pub state_root: RootV2,
}

impl LaneStateRootV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("lane state module release", false)?;
        self.state_root.validate("lane state root", true)
    }
}

impl ValidateCanonicalV2 for LaneStateRootV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayStateV2 {
    pub replay_id: String,
    pub occurrence_id: RootV2,
}

impl ReplayStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.replay_id, "replay id")?;
        self.occurrence_id.validate("replay occurrence id", false)
    }
}

impl ValidateCanonicalV2 for ReplayStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum OutboxStatusV2 {
    PENDING,
    ACKNOWLEDGED,
}

#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(deny_unknown_fields)]
pub struct OutboxStateV2 {
    pub effect_id: RootV2,
    pub destination_id: String,
    pub payload_hash: RootV2,
    pub adapter_profile_root: RootV2,
    pub commit_id: RootV2,
    pub status: OutboxStatusV2,
}

impl OutboxStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.effect_id.validate("outbox effect id", false)?;
        validate_token_v2(&self.destination_id, "outbox destination")?;
        if self.destination_id.starts_with("zenoledger:") {
            return Err(AbiErrorV2::InvalidBinding("same-ledger external outbox"));
        }
        self.payload_hash.validate("outbox payload hash", false)?;
        self.adapter_profile_root
            .validate("outbox adapter profile root", false)?;
        self.commit_id.validate("outbox commit id", false)
    }
}

impl ValidateCanonicalV2 for OutboxStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicStateV2 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV2,
    pub writer_epoch: u64,
    pub height: u64,
    pub profile_root: RootV2,
    pub lane_roots: Vec<LaneStateRootV2>,
    pub balances: Vec<EconomicAmountV2>,
    pub supplies: Vec<AssetSupplyV2>,
    pub custody: Vec<EconomicAmountV2>,
    pub liabilities: Vec<EconomicAmountV2>,
    pub reserves: Vec<EconomicAmountV2>,
    pub oracle_occurrences: Vec<OracleOccurrenceStateV2>,
    pub replay_state: Vec<ReplayStateV2>,
    pub terminal_obligations: Vec<TerminalObligationV2>,
    pub history_root: RootV2,
    pub outbox: Vec<OutboxStateV2>,
}

impl GlobalEconomicStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "global economic state",
        )?;
        validate_token_v2(&self.chain_id, "global state chain id")?;
        self.deployment_root
            .validate("global state deployment root", false)?;
        self.profile_root
            .validate("global state profile root", false)?;
        self.history_root
            .validate("global state history root", true)?;
        self.validate_lane_roots()?;
        self.validate_economic_tables()?;
        self.validate_control_tables()
    }

    fn validate_lane_roots(&self) -> AbiResultV2<()> {
        if self.lane_roots.len() != ALL_LANE_IDS_V2.len() {
            return Err(AbiErrorV2::InvalidBounds("global state lane roots"));
        }
        for (row, expected_lane) in self.lane_roots.iter().zip(ALL_LANE_IDS_V2) {
            row.validate()?;
            if row.lane_id != expected_lane {
                return Err(AbiErrorV2::InvalidOrder("global state lane roots"));
            }
        }
        Ok(())
    }

    fn validate_economic_tables(&self) -> AbiResultV2<()> {
        for (label, rows) in [
            ("global state balances", self.balances.as_slice()),
            ("global state custody", self.custody.as_slice()),
            ("global state liabilities", self.liabilities.as_slice()),
            ("global state reserves", self.reserves.as_slice()),
        ] {
            if rows.len() > MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V2 {
                return Err(AbiErrorV2::InvalidBounds(label));
            }
            for row in rows {
                row.validate()?;
                if row.amount_atoms == 0 {
                    return Err(AbiErrorV2::InvalidBounds(label));
                }
            }
            if rows.windows(2).any(|pair| pair[0].key() >= pair[1].key()) {
                return Err(AbiErrorV2::InvalidOrder(label));
            }
        }
        if self.supplies.len() > MAX_GLOBAL_SUPPLY_ROWS_V2 {
            return Err(AbiErrorV2::InvalidBounds("global state supplies"));
        }
        for supply in &self.supplies {
            supply.validate()?;
            if supply.amount_atoms == 0 {
                return Err(AbiErrorV2::InvalidBounds("global state supplies"));
            }
        }
        if self
            .supplies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("global state supplies"));
        }
        Ok(())
    }

    fn validate_control_tables(&self) -> AbiResultV2<()> {
        self.validate_oracle_and_replay_tables()?;
        self.validate_terminal_and_outbox_tables()
    }

    fn validate_oracle_and_replay_tables(&self) -> AbiResultV2<()> {
        if self.oracle_occurrences.len() > MAX_GLOBAL_ORACLE_ROWS_V2 {
            return Err(AbiErrorV2::InvalidBounds("global state Oracle occurrences"));
        }
        for row in &self.oracle_occurrences {
            row.validate()?;
            if row.observed_height > self.height {
                return Err(AbiErrorV2::InvalidBinding(
                    "Oracle observed height exceeds global state height",
                ));
            }
        }
        if self
            .oracle_occurrences
            .windows(2)
            .any(|pair| pair[0].oracle_id >= pair[1].oracle_id)
        {
            return Err(AbiErrorV2::InvalidOrder("global state Oracle occurrences"));
        }

        if self.replay_state.len() > MAX_GLOBAL_REPLAY_ROWS_V2 {
            return Err(AbiErrorV2::InvalidBounds("global state replay state"));
        }
        for row in &self.replay_state {
            row.validate()?;
        }
        if self
            .replay_state
            .windows(2)
            .any(|pair| pair[0].replay_id >= pair[1].replay_id)
        {
            return Err(AbiErrorV2::InvalidOrder("global state replay state"));
        }
        let occurrence_ids = self
            .replay_state
            .iter()
            .map(|row| &row.occurrence_id)
            .collect::<BTreeSet<_>>();
        if occurrence_ids.len() != self.replay_state.len() {
            return Err(AbiErrorV2::InvalidBinding(
                "global state replay occurrence ids",
            ));
        }
        Ok(())
    }

    fn validate_terminal_and_outbox_tables(&self) -> AbiResultV2<()> {
        if self.terminal_obligations.len() > MAX_GLOBAL_TERMINAL_ROWS_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "global state terminal obligations",
            ));
        }
        for row in &self.terminal_obligations {
            row.validate()?;
        }
        if self
            .terminal_obligations
            .windows(2)
            .any(|pair| pair[0].obligation_id >= pair[1].obligation_id)
        {
            return Err(AbiErrorV2::InvalidOrder(
                "global state terminal obligations",
            ));
        }

        if self.outbox.len() > MAX_GLOBAL_OUTBOX_ROWS_V2 {
            return Err(AbiErrorV2::InvalidBounds("global state outbox"));
        }
        for row in &self.outbox {
            row.validate()?;
        }
        if self
            .outbox
            .windows(2)
            .any(|pair| pair[0].effect_id >= pair[1].effect_id)
        {
            return Err(AbiErrorV2::InvalidOrder("global state outbox"));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("global-economic-state-root-v2", self)
    }

    pub(crate) fn owned_atoms_by_asset(&self) -> AbiResultV2<BTreeMap<String, u128>> {
        sum_amounts_by_asset(
            self.balances
                .iter()
                .chain(&self.custody)
                .chain(&self.reserves),
            "global owned accounting",
        )
    }

    pub(crate) fn liability_atoms_by_asset(&self) -> AbiResultV2<BTreeMap<String, u128>> {
        sum_amounts_by_asset(self.liabilities.iter(), "global liability")
    }

    pub(crate) fn supply_atoms_by_asset(&self) -> BTreeMap<String, u128> {
        self.supplies
            .iter()
            .map(|row| (row.asset.clone(), row.amount_atoms))
            .collect()
    }
}

fn sum_amounts_by_asset<'a>(
    rows: impl Iterator<Item = &'a EconomicAmountV2>,
    label: &'static str,
) -> AbiResultV2<BTreeMap<String, u128>> {
    let mut totals = BTreeMap::new();
    for row in rows {
        let total = totals
            .get(&row.asset)
            .copied()
            .unwrap_or(0_u128)
            .checked_add(row.amount_atoms)
            .ok_or(AbiErrorV2::InvalidBounds(label))?;
        totals.insert(row.asset.clone(), total);
    }
    Ok(totals)
}

impl ValidateCanonicalV2 for GlobalEconomicStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
