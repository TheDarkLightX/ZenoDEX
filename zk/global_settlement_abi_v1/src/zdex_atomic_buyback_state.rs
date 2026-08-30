//! Complete tokenomics substate used by the same-occurrence ZDEX buyback core.
//!
//! One root owns the ZDEX supply, every fee allocation state, and the buyback
//! cadence for the same quote-asset registry. This module grants no receipt,
//! lane-composition, route-composition, or publication authority.

use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::zdex_buyback_spend::ZDEXBuybackSpendStateV1;
use crate::zdex_fee_allocation_types::ZDEXFeeStateV1;
use crate::zdex_tokenomics_lane_types::ZDEXTokenomicsLaneStateV1;

pub const ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1: &str =
    "zenodex/zdex-atomic-buyback-tokenomics-state/v1";

pub fn zdex_atomic_buyback_tokenomics_state_schema_root_v1() -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Schema<'a> {
        schema: &'a str,
    }

    hash_global_v1(
        "zdex-tokenomics-state-schema-v1",
        &Schema {
            schema: ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1,
        },
    )
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXAtomicBuybackTokenomicsStateV1 {
    pub schema: String,
    pub tokenomics: ZDEXTokenomicsLaneStateV1,
    pub buyback_spend_states: Vec<ZDEXBuybackSpendStateV1>,
}

impl ZDEXAtomicBuybackTokenomicsStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.tokenomics.validate()?;
        if self.buyback_spend_states.len() != self.tokenomics.fee_allocation_states.len() {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback cadence registry width",
            ));
        }
        for (cadence, fee) in self
            .buyback_spend_states
            .iter()
            .zip(&self.tokenomics.fee_allocation_states)
        {
            cadence.validate()?;
            if cadence.quote_asset_id != fee.fee_asset_id {
                return Err(AbiErrorV1::InvalidBinding(
                    "atomic buyback cadence asset registry",
                ));
            }
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-atomic-buyback-tokenomics-state-v1", self)
    }

    pub fn fee_state_for(&self, quote_asset_id: &RootV1) -> AbiResultV1<&ZDEXFeeStateV1> {
        self.validate()?;
        self.tokenomics
            .fee_allocation_states
            .iter()
            .find(|state| &state.fee_asset_id == quote_asset_id)
            .ok_or(AbiErrorV1::InvalidBinding(
                "atomic buyback quote asset fee state",
            ))
    }

    pub fn cadence_state_for(
        &self,
        quote_asset_id: &RootV1,
    ) -> AbiResultV1<&ZDEXBuybackSpendStateV1> {
        self.validate()?;
        self.buyback_spend_states
            .iter()
            .find(|state| &state.quote_asset_id == quote_asset_id)
            .ok_or(AbiErrorV1::InvalidBinding(
                "atomic buyback quote asset cadence state",
            ))
    }

    pub fn with_buyback_result(
        &self,
        fee_state: &ZDEXFeeStateV1,
        cadence_state: &ZDEXBuybackSpendStateV1,
    ) -> AbiResultV1<Self> {
        self.validate()?;
        fee_state.validate()?;
        cadence_state.validate()?;
        if fee_state.fee_asset_id != cadence_state.quote_asset_id {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback fee and cadence assets",
            ));
        }

        let mut found_fee = false;
        let fee_allocation_states = self
            .tokenomics
            .fee_allocation_states
            .iter()
            .map(|state| {
                if state.fee_asset_id == fee_state.fee_asset_id {
                    found_fee = true;
                    fee_state.clone()
                } else {
                    state.clone()
                }
            })
            .collect();
        let mut found_cadence = false;
        let buyback_spend_states = self
            .buyback_spend_states
            .iter()
            .map(|state| {
                if state.quote_asset_id == cadence_state.quote_asset_id {
                    found_cadence = true;
                    cadence_state.clone()
                } else {
                    state.clone()
                }
            })
            .collect();
        if !found_fee || !found_cadence {
            return Err(AbiErrorV1::InvalidBinding(
                "atomic buyback post-state asset registry",
            ));
        }

        let mut tokenomics = self.tokenomics.clone();
        tokenomics.fee_allocation_states = fee_allocation_states;
        let post_state = Self {
            schema: self.schema.clone(),
            tokenomics,
            buyback_spend_states,
        };
        post_state.validate()?;
        Ok(post_state)
    }
}
