use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::canonical::{
    canonical_bytes_v2, hash_global_v2, validate_schema_v2, validate_sorted_unique_tokens_v2,
    AbiErrorV2, AbiResultV2, RootV2, ValidateCanonicalV2, GLOBAL_SETTLEMENT_ABI_V2,
};
pub use crate::effect_values::{
    AssetConservationRowV2, EconomicEffectKindV2, EconomicEffectRowV2, ExternalOutboxEnqueueV2,
    FeeConservationRowV2, LaneIdV2, LaneWriteV2, FEE_RESIDUE_CONTROL_DOMAIN_V2,
    FEE_RESIDUE_PRINCIPAL_V2,
};
use crate::resource_limits::MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2;

pub const MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2: usize = 4_096;
pub const MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2: usize = 256;
pub const MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2: usize = 256;
pub const MAX_LANE_WRITES_PER_PLAN_V2: usize = 12;
pub const MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2: usize =
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2;
pub const MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2: usize = 4_096;
pub const MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2: usize = 8_192;
pub const MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2: usize = 1_048_576;

const _: [(); MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2] =
    [(); MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GlobalEconomicEffectPlanV2 {
    pub schema: String,
    pub rows: Vec<EconomicEffectRowV2>,
    pub asset_conservation: Vec<AssetConservationRowV2>,
    pub fee_conservation: Vec<FeeConservationRowV2>,
    pub lane_writes: Vec<LaneWriteV2>,
    pub occurrence_consumptions: Vec<RootV2>,
    pub external_outbox_enqueue: Vec<ExternalOutboxEnqueueV2>,
}

impl GlobalEconomicEffectPlanV2 {
    pub fn empty() -> Self {
        Self {
            schema: GLOBAL_SETTLEMENT_ABI_V2.to_owned(),
            rows: Vec::new(),
            asset_conservation: Vec::new(),
            fee_conservation: Vec::new(),
            lane_writes: Vec::new(),
            occurrence_consumptions: Vec::new(),
            external_outbox_enqueue: Vec::new(),
        }
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            GLOBAL_SETTLEMENT_ABI_V2,
            "global economic effect plan",
        )?;
        self.validate_resource_bounds()?;
        self.validate_effect_rows()?;
        self.validate_conservation_rows()?;
        self.validate_commitments()?;
        self.validate_issue_burn_projection()?;
        self.validate_fee_projection()?;
        if canonical_bytes_v2(self)?.len() > MAX_ECONOMIC_EFFECT_PLAN_CANONICAL_BYTES_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "effect plan canonical encoding bytes",
            ));
        }
        Ok(())
    }

    fn validate_resource_bounds(&self) -> AbiResultV2<()> {
        let counts_and_limits = [
            (
                "effect plan rows",
                self.rows.len(),
                MAX_ECONOMIC_EFFECT_ROWS_PER_PLAN_V2,
            ),
            (
                "effect plan asset conservation",
                self.asset_conservation.len(),
                MAX_ASSET_CONSERVATION_ROWS_PER_PLAN_V2,
            ),
            (
                "effect plan fee conservation",
                self.fee_conservation.len(),
                MAX_FEE_CONSERVATION_ROWS_PER_PLAN_V2,
            ),
            (
                "effect plan lane writes",
                self.lane_writes.len(),
                MAX_LANE_WRITES_PER_PLAN_V2,
            ),
            (
                "effect plan occurrence consumptions",
                self.occurrence_consumptions.len(),
                MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
            ),
            (
                "effect plan external outbox enqueue",
                self.external_outbox_enqueue.len(),
                MAX_EXTERNAL_OUTBOX_ENQUEUES_PER_PLAN_V2,
            ),
        ];
        for (label, count, limit) in counts_and_limits {
            if count > limit {
                return Err(AbiErrorV2::InvalidBounds(label));
            }
        }
        let total = self
            .rows
            .len()
            .saturating_add(self.asset_conservation.len())
            .saturating_add(self.fee_conservation.len())
            .saturating_add(self.lane_writes.len())
            .saturating_add(self.occurrence_consumptions.len())
            .saturating_add(self.external_outbox_enqueue.len());
        if total > MAX_ECONOMIC_EFFECT_PLAN_ITEMS_V2 {
            return Err(AbiErrorV2::InvalidBounds("effect plan total items"));
        }
        Ok(())
    }

    fn validate_effect_rows(&self) -> AbiResultV2<()> {
        for row in &self.rows {
            row.validate()?;
        }
        if self
            .rows
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV2::InvalidOrder("effect plan rows"));
        }
        Ok(())
    }

    fn validate_conservation_rows(&self) -> AbiResultV2<()> {
        for row in &self.asset_conservation {
            row.validate()?;
        }
        if self
            .asset_conservation
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset conservation"));
        }
        for row in &self.fee_conservation {
            row.validate()?;
        }
        if self
            .fee_conservation
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("fee conservation"));
        }
        Ok(())
    }

    fn validate_commitments(&self) -> AbiResultV2<()> {
        for row in &self.lane_writes {
            row.validate()?;
        }
        if self
            .lane_writes
            .windows(2)
            .any(|pair| pair[0].lane_id.as_str() >= pair[1].lane_id.as_str())
        {
            return Err(AbiErrorV2::InvalidOrder("lane writes"));
        }
        let consumption_tokens = self
            .occurrence_consumptions
            .iter()
            .map(|root| root.as_str().to_owned())
            .collect::<Vec<_>>();
        validate_sorted_unique_tokens_v2(
            &consumption_tokens,
            "effect plan occurrence consumptions",
            true,
        )?;
        for root in &self.occurrence_consumptions {
            root.validate("effect plan occurrence consumption", false)?;
        }
        for row in &self.external_outbox_enqueue {
            row.validate()?;
        }
        if self
            .external_outbox_enqueue
            .windows(2)
            .any(|pair| pair[0].effect_id >= pair[1].effect_id)
        {
            return Err(AbiErrorV2::InvalidOrder("external outbox enqueue"));
        }
        Ok(())
    }

    fn validate_issue_burn_projection(&self) -> AbiResultV2<()> {
        let mut issued = BTreeMap::<&str, u128>::new();
        let mut burned = BTreeMap::<&str, u128>::new();
        for row in &self.rows {
            let target = match row.kind {
                EconomicEffectKindV2::ISSUE => Some((&mut issued, row.delta_atoms.unsigned_abs())),
                EconomicEffectKindV2::BURN => Some((&mut burned, row.delta_atoms.unsigned_abs())),
                _ => None,
            };
            if let Some((values, amount)) = target {
                let total = values
                    .get(row.asset.as_str())
                    .copied()
                    .unwrap_or(0)
                    .checked_add(amount)
                    .ok_or(AbiErrorV2::Conservation("issue or burn overflow"))?;
                values.insert(row.asset.as_str(), total);
            }
        }
        for row in &self.asset_conservation {
            if row.authorized_issue_atoms != issued.remove(row.asset.as_str()).unwrap_or(0)
                || row.authorized_burn_atoms != burned.remove(row.asset.as_str()).unwrap_or(0)
            {
                return Err(AbiErrorV2::Conservation("issue or burn projection"));
            }
        }
        if !issued.is_empty() || !burned.is_empty() {
            return Err(AbiErrorV2::Conservation("missing issue or burn asset row"));
        }
        Ok(())
    }

    fn validate_fee_projection(&self) -> AbiResultV2<()> {
        let mut allocations = BTreeMap::<&str, u128>::new();
        for row in &self.rows {
            if row.kind != EconomicEffectKindV2::FEE_ALLOCATION {
                continue;
            }
            let amount = u128::try_from(row.delta_atoms)
                .map_err(|_| AbiErrorV2::Conservation("negative fee allocation"))?;
            let total = allocations
                .get(row.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(amount)
                .ok_or(AbiErrorV2::Conservation("fee allocation overflow"))?;
            allocations.insert(row.asset.as_str(), total);
        }
        for row in &self.fee_conservation {
            if row.current_allocations_atoms != allocations.remove(row.asset.as_str()).unwrap_or(0)
            {
                return Err(AbiErrorV2::Conservation("fee projection"));
            }
        }
        if !allocations.is_empty() {
            return Err(AbiErrorV2::Conservation("missing fee conservation row"));
        }
        Ok(())
    }

    pub fn effect_plan_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("global-economic-effect-plan-v2", self)
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

impl ValidateCanonicalV2 for GlobalEconomicEffectPlanV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
