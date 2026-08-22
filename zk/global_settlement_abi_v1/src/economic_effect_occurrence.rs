//! Injective route-effect identities retained across epoch aggregation.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::{EconomicEffectRowV1, GlobalEconomicEffectPlanV1};

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicEffectOccurrenceV1 {
    pub schema: String,
    pub effect_occurrence_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub route_release_id: RootV1,
    pub effect_index: u64,
    pub effect_row: EconomicEffectRowV1,
}

#[derive(Serialize)]
struct EconomicEffectOccurrenceContentV1<'a> {
    schema: &'static str,
    command_occurrence_id: &'a RootV1,
    route_release_id: &'a RootV1,
    effect_index: u64,
    effect_row: &'a EconomicEffectRowV1,
}

impl EconomicEffectOccurrenceV1 {
    pub fn build(
        command_occurrence_id: RootV1,
        route_release_id: RootV1,
        effect_index: u64,
        effect_row: EconomicEffectRowV1,
    ) -> AbiResultV1<Self> {
        let effect_occurrence_id = hash_global_v1(
            "global-economic-effect-occurrence-v1",
            &EconomicEffectOccurrenceContentV1 {
                schema: GLOBAL_SETTLEMENT_ABI_V1,
                command_occurrence_id: &command_occurrence_id,
                route_release_id: &route_release_id,
                effect_index,
                effect_row: &effect_row,
            },
        )?;
        let result = Self {
            schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
            effect_occurrence_id,
            command_occurrence_id,
            route_release_id,
            effect_index,
            effect_row,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        self.effect_occurrence_id
            .validate("economic effect occurrence id", false)?;
        self.command_occurrence_id
            .validate("economic effect command occurrence id", false)?;
        self.route_release_id
            .validate("economic effect route release id", false)?;
        self.effect_row.validate()?;
        if self.effect_occurrence_id != self.derived_effect_occurrence_id()? {
            return Err(AbiErrorV1::InvalidBinding(
                "economic effect occurrence content id",
            ));
        }
        Ok(())
    }

    pub fn derived_effect_occurrence_id(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "global-economic-effect-occurrence-v1",
            &EconomicEffectOccurrenceContentV1 {
                schema: GLOBAL_SETTLEMENT_ABI_V1,
                command_occurrence_id: &self.command_occurrence_id,
                route_release_id: &self.route_release_id,
                effect_index: self.effect_index,
                effect_row: &self.effect_row,
            },
        )
    }
}

pub fn derive_route_effect_occurrences_v1(
    command_occurrence_id: &RootV1,
    route_release_id: &RootV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<Vec<EconomicEffectOccurrenceV1>> {
    command_occurrence_id.validate("route effect command occurrence id", false)?;
    route_release_id.validate("route effect release id", false)?;
    effect_plan.validate()?;
    if effect_plan.occurrence_consumptions.as_slice() != std::slice::from_ref(command_occurrence_id)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "route effect consumed occurrence",
        ));
    }
    let occurrences = effect_plan
        .rows
        .iter()
        .enumerate()
        .map(|(index, row)| {
            let effect_index = u64::try_from(index)
                .map_err(|_| AbiErrorV1::InvalidBounds("route effect index"))?;
            EconomicEffectOccurrenceV1::build(
                command_occurrence_id.clone(),
                route_release_id.clone(),
                effect_index,
                row.clone(),
            )
        })
        .collect::<AbiResultV1<Vec<_>>>()?;
    if occurrences
        .iter()
        .map(|item| &item.effect_occurrence_id)
        .collect::<BTreeSet<_>>()
        .len()
        != occurrences.len()
    {
        return Err(AbiErrorV1::InvalidOrder(
            "route effect occurrence identities",
        ));
    }
    Ok(occurrences)
}
