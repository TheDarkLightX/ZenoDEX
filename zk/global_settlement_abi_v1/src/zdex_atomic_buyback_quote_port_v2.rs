use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::zdex_fee_allocation_types::FEE_BUYBACK_PRINCIPAL_V1;
use crate::zdex_purchase_burn_types::zdex_pool_reserve_principal_v1;

pub const ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2: &str =
    "zenodex/zdex-atomic-buyback-quote-port/v2";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXAtomicBuybackQuotePortV2 {
    pub schema: String,
    pub profile_root: RootV1,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub global_pre_state_root: RootV1,
    pub producer_module_release_id: RootV1,
    pub consumer_module_release_id: RootV1,
    pub producer_quote_pre_state_root: RootV1,
    pub producer_quote_post_state_root: RootV1,
    pub producer_quote_effect_plan_root: RootV1,
    pub selected_pool_id: RootV1,
    pub quote_asset_id: RootV1,
    pub amount_atoms: u128,
}

impl ZDEXAtomicBuybackQuotePortV2 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2 {
            return Err(AbiErrorV1::InvalidBinding("ZDEX quote port schema"));
        }
        for root in [
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.global_pre_state_root,
            &self.producer_module_release_id,
            &self.consumer_module_release_id,
            &self.producer_quote_pre_state_root,
            &self.producer_quote_post_state_root,
            &self.producer_quote_effect_plan_root,
            &self.selected_pool_id,
            &self.quote_asset_id,
        ] {
            root.validate("ZDEX quote port root", false)?;
        }
        if self.amount_atoms == 0 || self.amount_atoms > i128::MAX.unsigned_abs() {
            return Err(AbiErrorV1::InvalidBounds("ZDEX quote port amount"));
        }
        if self.producer_module_release_id == self.consumer_module_release_id {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX quote port distinct module releases",
            ));
        }
        if self.producer_quote_pre_state_root == self.producer_quote_post_state_root {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX quote phase state transition",
            ));
        }
        Ok(())
    }

    pub fn source_principal(&self) -> &'static str {
        FEE_BUYBACK_PRINCIPAL_V1
    }

    pub fn destination_principal(&self) -> AbiResultV1<String> {
        self.validate()?;
        zdex_pool_reserve_principal_v1(&self.selected_pool_id, &self.quote_asset_id)
    }

    pub fn port_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-atomic-buyback-quote-port-v2", self)
    }
}
