use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::bounded::deserialize_settlement_rows;
use super::hash::{
    asset_effects_root_v2, carry_effects_root_v2, cell_writes_root_v2, commitment, domain_hasher,
    message_effects_root_v2, reward_effects_root_v2, PLAN_COMMITMENT_DOMAIN_V2,
};
use super::validate::{canonicalize_plan_rows, validate_plan_v2};
use super::{
    AssetEffectV2, CarryEffectV2, LedgerCellWriteV2, MessageEffectV2, RewardEffectV2,
    SettlementEffectErrorV2, SETTLEMENT_EFFECT_PLAN_VERSION_V2,
};
use crate::{CommitmentV3, EconomicActionBatchV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettlementEffectPlanInputV2 {
    pub source_semantic_journal_hash: CommitmentV3,
    pub public_policy_hash: CommitmentV3,
    pub post_state_root: CommitmentV3,
    pub economic_action_batch: EconomicActionBatchV1,
    pub ledger_cell_writes: Vec<LedgerCellWriteV2>,
    pub asset_effects: Vec<AssetEffectV2>,
    pub message_effects: Vec<MessageEffectV2>,
    pub carry_effects: Vec<CarryEffectV2>,
    pub reward_effects: Vec<RewardEffectV2>,
}

/// Canonical proof-neutral settlement proposal.
///
/// Construction supplies no receipt or ledger authority:
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::SettlementEffectPlanV2;
/// let plan: SettlementEffectPlanV2 = unimplemented!();
/// let _ = plan.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SettlementEffectPlanV2 {
    plan_version: u16,
    source_semantic_journal_hash: CommitmentV3,
    public_policy_hash: CommitmentV3,
    post_state_root: CommitmentV3,
    economic_action_batch: EconomicActionBatchV1,
    ledger_cell_writes: Vec<LedgerCellWriteV2>,
    asset_effects: Vec<AssetEffectV2>,
    message_effects: Vec<MessageEffectV2>,
    carry_effects: Vec<CarryEffectV2>,
    reward_effects: Vec<RewardEffectV2>,
    cell_writes_root: CommitmentV3,
    asset_effects_root: CommitmentV3,
    message_effects_root: CommitmentV3,
    carry_effects_root: CommitmentV3,
    reward_effects_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SettlementEffectPlanWireV2 {
    plan_version: u16,
    source_semantic_journal_hash: CommitmentV3,
    public_policy_hash: CommitmentV3,
    post_state_root: CommitmentV3,
    economic_action_batch: EconomicActionBatchV1,
    #[serde(deserialize_with = "deserialize_settlement_rows")]
    ledger_cell_writes: Vec<LedgerCellWriteV2>,
    #[serde(deserialize_with = "deserialize_settlement_rows")]
    asset_effects: Vec<AssetEffectV2>,
    #[serde(deserialize_with = "deserialize_settlement_rows")]
    message_effects: Vec<MessageEffectV2>,
    #[serde(deserialize_with = "deserialize_settlement_rows")]
    carry_effects: Vec<CarryEffectV2>,
    #[serde(deserialize_with = "deserialize_settlement_rows")]
    reward_effects: Vec<RewardEffectV2>,
    cell_writes_root: CommitmentV3,
    asset_effects_root: CommitmentV3,
    message_effects_root: CommitmentV3,
    carry_effects_root: CommitmentV3,
    reward_effects_root: CommitmentV3,
}

impl SettlementEffectPlanV2 {
    pub fn new(mut input: SettlementEffectPlanInputV2) -> Result<Self, SettlementEffectErrorV2> {
        canonicalize_plan_rows(&mut input)?;
        let plan = Self {
            plan_version: SETTLEMENT_EFFECT_PLAN_VERSION_V2,
            source_semantic_journal_hash: input.source_semantic_journal_hash,
            public_policy_hash: input.public_policy_hash,
            post_state_root: input.post_state_root,
            economic_action_batch: input.economic_action_batch,
            cell_writes_root: cell_writes_root_v2(&input.ledger_cell_writes)?,
            asset_effects_root: asset_effects_root_v2(&input.asset_effects)?,
            message_effects_root: message_effects_root_v2(&input.message_effects)?,
            carry_effects_root: carry_effects_root_v2(&input.carry_effects)?,
            reward_effects_root: reward_effects_root_v2(&input.reward_effects)?,
            ledger_cell_writes: input.ledger_cell_writes,
            asset_effects: input.asset_effects,
            message_effects: input.message_effects,
            carry_effects: input.carry_effects,
            reward_effects: input.reward_effects,
        };
        plan.validate_self_consistency()?;
        Ok(plan)
    }

    pub fn validate_self_consistency(&self) -> Result<(), SettlementEffectErrorV2> {
        if self.plan_version != SETTLEMENT_EFFECT_PLAN_VERSION_V2 {
            return Err(SettlementEffectErrorV2::InvalidVersion(self.plan_version));
        }
        validate_plan_v2(self)?;
        for (field, actual, expected) in [
            (
                "cell_writes_root",
                self.cell_writes_root,
                cell_writes_root_v2(&self.ledger_cell_writes)?,
            ),
            (
                "asset_effects_root",
                self.asset_effects_root,
                asset_effects_root_v2(&self.asset_effects)?,
            ),
            (
                "message_effects_root",
                self.message_effects_root,
                message_effects_root_v2(&self.message_effects)?,
            ),
            (
                "carry_effects_root",
                self.carry_effects_root,
                carry_effects_root_v2(&self.carry_effects)?,
            ),
            (
                "reward_effects_root",
                self.reward_effects_root,
                reward_effects_root_v2(&self.reward_effects)?,
            ),
        ] {
            if actual != expected {
                return Err(SettlementEffectErrorV2::CommitmentMismatch(field));
            }
        }
        Ok(())
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, SettlementEffectErrorV2> {
        self.validate_self_consistency()?;
        let mut hasher = domain_hasher(PLAN_COMMITMENT_DOMAIN_V2)?;
        hasher.update(self.plan_version.to_be_bytes());
        hasher.update(
            self.economic_action_batch
                .canonical_commitment()?
                .as_bytes(),
        );
        hasher.update(self.source_semantic_journal_hash.as_bytes());
        hasher.update(self.public_policy_hash.as_bytes());
        hasher.update(self.post_state_root.as_bytes());
        for root in [
            self.cell_writes_root,
            self.asset_effects_root,
            self.message_effects_root,
            self.carry_effects_root,
            self.reward_effects_root,
        ] {
            hasher.update(root.as_bytes());
        }
        commitment(hasher, "settlement_effect_plan")
    }

    pub const fn plan_version(&self) -> u16 {
        self.plan_version
    }
    pub const fn source_semantic_journal_hash(&self) -> CommitmentV3 {
        self.source_semantic_journal_hash
    }
    pub const fn public_policy_hash(&self) -> CommitmentV3 {
        self.public_policy_hash
    }
    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }
    pub const fn economic_action_batch(&self) -> &EconomicActionBatchV1 {
        &self.economic_action_batch
    }
    pub fn ledger_cell_writes(&self) -> &[LedgerCellWriteV2] {
        &self.ledger_cell_writes
    }
    pub fn asset_effects(&self) -> &[AssetEffectV2] {
        &self.asset_effects
    }
    pub fn message_effects(&self) -> &[MessageEffectV2] {
        &self.message_effects
    }
    pub fn carry_effects(&self) -> &[CarryEffectV2] {
        &self.carry_effects
    }
    pub fn reward_effects(&self) -> &[RewardEffectV2] {
        &self.reward_effects
    }
    pub const fn cell_writes_root(&self) -> CommitmentV3 {
        self.cell_writes_root
    }
    pub const fn asset_effects_root(&self) -> CommitmentV3 {
        self.asset_effects_root
    }
    pub const fn message_effects_root(&self) -> CommitmentV3 {
        self.message_effects_root
    }
    pub const fn carry_effects_root(&self) -> CommitmentV3 {
        self.carry_effects_root
    }
    pub const fn reward_effects_root(&self) -> CommitmentV3 {
        self.reward_effects_root
    }
}

impl<'de> Deserialize<'de> for SettlementEffectPlanV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SettlementEffectPlanWireV2::deserialize(deserializer)?;
        let plan = Self {
            plan_version: wire.plan_version,
            source_semantic_journal_hash: wire.source_semantic_journal_hash,
            public_policy_hash: wire.public_policy_hash,
            post_state_root: wire.post_state_root,
            economic_action_batch: wire.economic_action_batch,
            ledger_cell_writes: wire.ledger_cell_writes,
            asset_effects: wire.asset_effects,
            message_effects: wire.message_effects,
            carry_effects: wire.carry_effects,
            reward_effects: wire.reward_effects,
            cell_writes_root: wire.cell_writes_root,
            asset_effects_root: wire.asset_effects_root,
            message_effects_root: wire.message_effects_root,
            carry_effects_root: wire.carry_effects_root,
            reward_effects_root: wire.reward_effects_root,
        };
        plan.validate_self_consistency()
            .map_err(de::Error::custom)?;
        Ok(plan)
    }
}
