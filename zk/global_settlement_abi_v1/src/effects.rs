use std::collections::BTreeMap;

use serde::{Deserialize, Deserializer, Serialize};

use crate::bounded_vec::deserialize_bounded_vec_v1;
use crate::canonical::{
    hash_global_v1, validate_root_sequence_v1, validate_schema_v1, validate_token_v1, AbiErrorV1,
    AbiResultV1, RootV1, MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1, MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
    MAX_EFFECT_PLAN_LANE_WRITES_V1, MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
    MAX_EFFECT_PLAN_ROWS_V1,
};
use crate::release::LaneIdV1;
use crate::state::TerminalObligationV1;

pub const FEE_RESIDUE_PRINCIPAL_V1: &str = "protocol:fee-unallocated-reserve";
pub const FEE_RESIDUE_CONTROL_DOMAIN_V1: &str = "zenoledger:protocol-fee-residue";

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[allow(non_camel_case_types)]
pub enum EconomicEffectKindV1 {
    ACCOUNT_MOVEMENT,
    ISSUE,
    BURN,
    CUSTODY,
    LIABILITY,
    RESERVE,
    FEE_ALLOCATION,
    REWARD,
    SLASH,
}

impl EconomicEffectKindV1 {
    fn as_str(self) -> &'static str {
        match self {
            Self::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
            Self::ISSUE => "ISSUE",
            Self::BURN => "BURN",
            Self::CUSTODY => "CUSTODY",
            Self::LIABILITY => "LIABILITY",
            Self::RESERVE => "RESERVE",
            Self::FEE_ALLOCATION => "FEE_ALLOCATION",
            Self::REWARD => "REWARD",
            Self::SLASH => "SLASH",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicEffectRowV1 {
    pub kind: EconomicEffectKindV1,
    pub principal: String,
    pub asset: String,
    pub custody_domain: String,
    pub delta_atoms: i128,
}

impl EconomicEffectRowV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.principal, "effect principal")?;
        validate_token_v1(&self.asset, "effect asset")?;
        validate_token_v1(&self.custody_domain, "effect custody domain")?;
        if self.delta_atoms == 0 {
            return Err(AbiErrorV1::InvalidBounds("effect delta"));
        }
        if self.kind == EconomicEffectKindV1::ISSUE && self.delta_atoms < 0 {
            return Err(AbiErrorV1::InvalidBinding("issue effect sign"));
        }
        if self.kind == EconomicEffectKindV1::BURN && self.delta_atoms > 0 {
            return Err(AbiErrorV1::InvalidBinding("burn effect sign"));
        }
        Ok(())
    }

    fn key(&self) -> (&'static str, String, String, String) {
        (
            self.kind.as_str(),
            self.asset.clone(),
            self.principal.clone(),
            self.custody_domain.clone(),
        )
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetConservationRowV1 {
    pub asset: String,
    pub owned_and_custodied_pre_atoms: u128,
    pub owned_and_custodied_post_atoms: u128,
    pub supply_pre_atoms: u128,
    pub supply_post_atoms: u128,
    pub authorized_issue_atoms: u128,
    pub authorized_burn_atoms: u128,
}

impl AssetConservationRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "conservation asset")?;
        let expected_owned = self
            .owned_and_custodied_pre_atoms
            .checked_add(self.authorized_issue_atoms)
            .and_then(|value| value.checked_sub(self.authorized_burn_atoms))
            .ok_or(AbiErrorV1::Conservation("owned and custodied overflow"))?;
        let expected_supply = self
            .supply_pre_atoms
            .checked_add(self.authorized_issue_atoms)
            .and_then(|value| value.checked_sub(self.authorized_burn_atoms))
            .ok_or(AbiErrorV1::Conservation("supply overflow"))?;
        if expected_owned != self.owned_and_custodied_post_atoms {
            return Err(AbiErrorV1::Conservation("owned and custodied"));
        }
        if expected_supply != self.supply_post_atoms {
            return Err(AbiErrorV1::Conservation("supply"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FeeConservationRowV1 {
    pub asset: String,
    pub fee_charged_atoms: u128,
    pub current_allocations_atoms: u128,
    pub carried_residue_atoms: u128,
}

impl FeeConservationRowV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "fee conservation asset")?;
        let allocated = self
            .current_allocations_atoms
            .checked_add(self.carried_residue_atoms)
            .ok_or(AbiErrorV1::Conservation("fee overflow"))?;
        if self.fee_charged_atoms != allocated {
            return Err(AbiErrorV1::Conservation("fee allocation"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneWriteV1 {
    pub lane_id: LaneIdV1,
    pub pre_root: RootV1,
    pub post_root: RootV1,
}

impl LaneWriteV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.pre_root.validate("lane write pre root", true)?;
        self.post_root.validate("lane write post root", true)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalOutboxEnqueueV1 {
    pub effect_id: RootV1,
    pub destination_id: String,
    pub payload_hash: RootV1,
    pub adapter_profile_root: RootV1,
}

impl ExternalOutboxEnqueueV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.effect_id
            .validate("external outbox effect id", false)?;
        validate_token_v1(&self.destination_id, "external outbox destination")?;
        if self.destination_id.starts_with("zenoledger:") {
            return Err(AbiErrorV1::InvalidBinding("same-ledger external outbox"));
        }
        self.payload_hash
            .validate("external outbox payload hash", false)?;
        self.adapter_profile_root
            .validate("external outbox adapter profile root", false)
    }
}

macro_rules! bounded_effect_vec_deserializer_v1 {
    ($function:ident, $row:ty, $maximum:expr, $label:literal) => {
        fn $function<'de, D>(deserializer: D) -> Result<Vec<$row>, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)
        }
    };
}

bounded_effect_vec_deserializer_v1!(
    deserialize_effect_rows_v1,
    EconomicEffectRowV1,
    MAX_EFFECT_PLAN_ROWS_V1,
    "economic effect plan rows"
);
bounded_effect_vec_deserializer_v1!(
    deserialize_asset_conservation_rows_v1,
    AssetConservationRowV1,
    MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1,
    "economic effect plan asset conservation rows"
);
bounded_effect_vec_deserializer_v1!(
    deserialize_fee_conservation_rows_v1,
    FeeConservationRowV1,
    MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1,
    "economic effect plan fee conservation rows"
);
bounded_effect_vec_deserializer_v1!(
    deserialize_lane_writes_v1,
    LaneWriteV1,
    MAX_EFFECT_PLAN_LANE_WRITES_V1,
    "economic effect plan lane writes"
);
bounded_effect_vec_deserializer_v1!(
    deserialize_occurrence_consumptions_v1,
    RootV1,
    MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1,
    "economic effect plan occurrence consumptions"
);
bounded_effect_vec_deserializer_v1!(
    deserialize_external_outbox_enqueue_v1,
    ExternalOutboxEnqueueV1,
    MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1,
    "economic effect plan external outbox rows"
);

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicEffectPlanV1 {
    pub schema: String,
    #[serde(deserialize_with = "deserialize_effect_rows_v1")]
    pub rows: Vec<EconomicEffectRowV1>,
    #[serde(deserialize_with = "deserialize_asset_conservation_rows_v1")]
    pub asset_conservation: Vec<AssetConservationRowV1>,
    #[serde(deserialize_with = "deserialize_fee_conservation_rows_v1")]
    pub fee_conservation: Vec<FeeConservationRowV1>,
    #[serde(deserialize_with = "deserialize_lane_writes_v1")]
    pub lane_writes: Vec<LaneWriteV1>,
    #[serde(deserialize_with = "deserialize_occurrence_consumptions_v1")]
    pub occurrence_consumptions: Vec<RootV1>,
    #[serde(deserialize_with = "deserialize_external_outbox_enqueue_v1")]
    pub external_outbox_enqueue: Vec<ExternalOutboxEnqueueV1>,
}

impl GlobalEconomicEffectPlanV1 {
    pub(crate) fn validate_resource_bounds(&self) -> AbiResultV1<()> {
        if self.rows.len() > MAX_EFFECT_PLAN_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds("economic effect plan rows"));
        }
        if self.asset_conservation.len() > MAX_EFFECT_PLAN_ASSET_CONSERVATION_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "economic effect plan asset conservation rows",
            ));
        }
        if self.fee_conservation.len() > MAX_EFFECT_PLAN_FEE_CONSERVATION_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "economic effect plan fee conservation rows",
            ));
        }
        if self.lane_writes.len() > MAX_EFFECT_PLAN_LANE_WRITES_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "economic effect plan lane writes",
            ));
        }
        if self.occurrence_consumptions.len() > MAX_EFFECT_PLAN_OCCURRENCE_CONSUMPTIONS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "economic effect plan occurrence consumptions",
            ));
        }
        if self.external_outbox_enqueue.len() > MAX_EFFECT_PLAN_EXTERNAL_OUTBOX_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "economic effect plan external outbox rows",
            ));
        }
        Ok(())
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.validate_resource_bounds()?;
        validate_schema_v1(&self.schema)?;
        for row in &self.rows {
            row.validate()?;
        }
        if self
            .rows
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV1::InvalidOrder("effect rows"));
        }
        for row in &self.asset_conservation {
            row.validate()?;
        }
        if self
            .asset_conservation
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("asset conservation"));
        }
        for row in &self.fee_conservation {
            row.validate()?;
        }
        if self
            .fee_conservation
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("fee conservation"));
        }
        for row in &self.lane_writes {
            row.validate()?;
        }
        if self
            .lane_writes
            .windows(2)
            .any(|pair| pair[0].lane_id.as_str() >= pair[1].lane_id.as_str())
        {
            return Err(AbiErrorV1::InvalidOrder("lane writes"));
        }
        validate_root_sequence_v1(
            &self.occurrence_consumptions,
            "occurrence consumptions",
            false,
        )?;
        for row in &self.external_outbox_enqueue {
            row.validate()?;
        }
        if self
            .external_outbox_enqueue
            .windows(2)
            .any(|pair| pair[0].effect_id >= pair[1].effect_id)
        {
            return Err(AbiErrorV1::InvalidOrder("external outbox enqueue"));
        }
        self.validate_issue_burn_projection()?;
        self.validate_fee_projection()
    }

    fn validate_issue_burn_projection(&self) -> AbiResultV1<()> {
        let mut issued = BTreeMap::<&str, u128>::new();
        let mut burned = BTreeMap::<&str, u128>::new();
        for row in &self.rows {
            let target = match row.kind {
                EconomicEffectKindV1::ISSUE => Some((&mut issued, row.delta_atoms.unsigned_abs())),
                EconomicEffectKindV1::BURN => Some((&mut burned, row.delta_atoms.unsigned_abs())),
                _ => None,
            };
            if let Some((values, amount)) = target {
                let total = values
                    .get(row.asset.as_str())
                    .copied()
                    .unwrap_or(0)
                    .checked_add(amount)
                    .ok_or(AbiErrorV1::Conservation("issue or burn overflow"))?;
                values.insert(row.asset.as_str(), total);
            }
        }
        for row in &self.asset_conservation {
            if row.authorized_issue_atoms != issued.remove(row.asset.as_str()).unwrap_or(0)
                || row.authorized_burn_atoms != burned.remove(row.asset.as_str()).unwrap_or(0)
            {
                return Err(AbiErrorV1::Conservation("issue or burn projection"));
            }
        }
        if !issued.is_empty() || !burned.is_empty() {
            return Err(AbiErrorV1::Conservation("missing issue or burn asset row"));
        }
        Ok(())
    }

    fn validate_fee_projection(&self) -> AbiResultV1<()> {
        let mut allocations = BTreeMap::<&str, u128>::new();
        for row in &self.rows {
            if row.kind != EconomicEffectKindV1::FEE_ALLOCATION {
                continue;
            }
            let amount = u128::try_from(row.delta_atoms)
                .map_err(|_| AbiErrorV1::Conservation("negative fee allocation"))?;
            let total = allocations
                .get(row.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(amount)
                .ok_or(AbiErrorV1::Conservation("fee allocation overflow"))?;
            allocations.insert(row.asset.as_str(), total);
        }
        for row in &self.fee_conservation {
            if row.current_allocations_atoms != allocations.remove(row.asset.as_str()).unwrap_or(0)
            {
                return Err(AbiErrorV1::Conservation("fee projection"));
            }
        }
        if !allocations.is_empty() {
            return Err(AbiErrorV1::Conservation("missing fee conservation row"));
        }
        Ok(())
    }

    pub fn effect_plan_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("global-economic-effect-plan-v1", self)
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
            && self.asset_conservation.is_empty()
            && self.fee_conservation.is_empty()
            && self.lane_writes.is_empty()
            && self.occurrence_consumptions.is_empty()
            && self.external_outbox_enqueue.is_empty()
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneTransitionRejectCodeV1 {
    UNKNOWN_COMMAND,
    DISABLED_FEATURE,
    RELEASE_MISMATCH,
    INVALID_CONTEXT,
    INVALID_STATE,
    POLICY_REJECT,
    RESOURCE_LIMIT,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneTransitionAcceptedV1 {
    pub command_occurrence_id: RootV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub private_ports_root: RootV1,
    pub receipt_root: RootV1,
    pub terminal_obligations: Vec<TerminalObligationV1>,
}

impl LaneTransitionAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.command_occurrence_id
            .validate("accepted occurrence id", false)?;
        self.pre_state_root
            .validate("accepted pre state root", false)?;
        self.post_state_root
            .validate("accepted post state root", false)?;
        self.effects.validate()?;
        self.private_ports_root
            .validate("accepted private ports root", true)?;
        self.receipt_root.validate("accepted receipt root", false)?;
        for obligation in &self.terminal_obligations {
            obligation.validate()?;
        }
        if self
            .terminal_obligations
            .windows(2)
            .any(|pair| pair[0].obligation_id >= pair[1].obligation_id)
        {
            return Err(AbiErrorV1::InvalidOrder("accepted terminal obligations"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LaneTransitionRejectedV1 {
    pub code: LaneTransitionRejectCodeV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl LaneTransitionRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state_root
            .validate("rejected pre state root", false)?;
        self.post_state_root
            .validate("rejected post state root", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding("reject is exact no-op"));
        }
        Ok(())
    }
}
