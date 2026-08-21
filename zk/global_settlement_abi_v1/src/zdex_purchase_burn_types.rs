use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1,
};

pub const PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1: &str = "protocol_buy_and_burn";
pub const AMM_PURCHASE_OUTPUT_ROLE_V1: &str = "AMM_PURCHASE_OUTPUT";
pub const ZDEX_BURN_INPUT_ROLE_V1: &str = "ZDEX_BURN_INPUT";
pub const AMM_POOL_CUSTODY_DOMAIN_V1: &str = "zenoledger:amm-pool";
pub const PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1: &str = "zenoledger:protocol-buyback";
pub const PROTOCOL_BURN_CUSTODY_DOMAIN_V1: &str = "zenoledger:protocol-burn";
pub const PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1: &str = "zenoledger:protocol-supply";
pub const ZDEX_SUPPLY_PRINCIPAL_V1: &str = "protocol:zdex-supply";

fn port_schema_root_v1(port_name: &str) -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct PortSchema<'a> {
        schema: &'static str,
        port_name: &'a str,
    }
    hash_global_v1(
        "zdex-purchase-burn-port-schema-v1",
        &PortSchema {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            port_name,
        },
    )
}

pub fn zdex_amm_purchase_port_schema_root_v1() -> AbiResultV1<RootV1> {
    port_schema_root_v1("ZDEX_AMM_PURCHASE_OUTPUT_V1")
}

pub fn zdex_burn_port_schema_root_v1() -> AbiResultV1<RootV1> {
    port_schema_root_v1("ZDEX_AUTHORIZED_BURN_SUBSTATE_INPUT_V1")
}

fn validate_positive_effect_amount_v1(value: u128, field: &'static str) -> AbiResultV1<()> {
    if value == 0 || value > i128::MAX.unsigned_abs() {
        return Err(AbiErrorV1::InvalidBounds(field));
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXAMMPurchaseJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub spot_module_release_id: RootV1,
    pub issue_burn_policy_root: RootV1,
    pub buyback_budget_occurrence_root: RootV1,
    pub quote_asset_id: RootV1,
    pub zdex_asset_id: RootV1,
    pub quote_source_bucket_id: String,
    pub quote_pool_bucket_id: String,
    pub zdex_pool_bucket_id: String,
    pub burn_bucket_id: String,
    pub quote_amount_in_atoms: u128,
    pub purchased_zdex_atoms: u128,
    pub quote_source_pre_atoms: u128,
    pub quote_source_post_atoms: u128,
    pub quote_pool_pre_atoms: u128,
    pub quote_pool_post_atoms: u128,
    pub zdex_pool_pre_atoms: u128,
    pub zdex_pool_post_atoms: u128,
    pub burn_bucket_pre_atoms: u128,
    pub burn_bucket_post_atoms: u128,
    pub quote_owned_atoms: u128,
    pub quote_supply_atoms: u128,
    pub zdex_owned_atoms: u128,
    pub zdex_supply_atoms: u128,
    pub pre_spot_lane_root: RootV1,
    pub post_spot_lane_root: RootV1,
    pub effect_plan_root: RootV1,
}

impl ZDEXAMMPurchaseJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "ZDEX purchase chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.spot_module_release_id,
            &self.issue_burn_policy_root,
            &self.buyback_budget_occurrence_root,
            &self.quote_asset_id,
            &self.zdex_asset_id,
            &self.pre_spot_lane_root,
            &self.post_spot_lane_root,
            &self.effect_plan_root,
        ] {
            root.validate("ZDEX purchase root", false)?;
        }
        for token in [
            &self.quote_source_bucket_id,
            &self.quote_pool_bucket_id,
            &self.zdex_pool_bucket_id,
            &self.burn_bucket_id,
        ] {
            validate_token_v1(token, "ZDEX purchase bucket")?;
        }
        if self.quote_asset_id == self.zdex_asset_id
            || self.quote_source_bucket_id == self.quote_pool_bucket_id
            || self.zdex_pool_bucket_id == self.burn_bucket_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX purchase distinct resources",
            ));
        }
        validate_positive_effect_amount_v1(
            self.quote_amount_in_atoms,
            "ZDEX purchase quote amount",
        )?;
        validate_positive_effect_amount_v1(
            self.purchased_zdex_atoms,
            "ZDEX purchase output amount",
        )?;
        if self
            .quote_source_post_atoms
            .checked_add(self.quote_amount_in_atoms)
            != Some(self.quote_source_pre_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase quote source projection",
            ));
        }
        if self
            .quote_pool_pre_atoms
            .checked_add(self.quote_amount_in_atoms)
            != Some(self.quote_pool_post_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase quote pool projection",
            ));
        }
        if self
            .zdex_pool_post_atoms
            .checked_add(self.purchased_zdex_atoms)
            != Some(self.zdex_pool_pre_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase output pool projection",
            ));
        }
        if self.burn_bucket_pre_atoms != 0
            || self.burn_bucket_post_atoms != self.purchased_zdex_atoms
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase transient burn bucket projection",
            ));
        }
        if self
            .quote_source_pre_atoms
            .checked_add(self.quote_pool_pre_atoms)
            .is_none_or(|selected| selected > self.quote_owned_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase quote buckets exceed owned amount",
            ));
        }
        if self
            .zdex_pool_pre_atoms
            .checked_add(self.burn_bucket_pre_atoms)
            .is_none_or(|selected| selected > self.zdex_owned_atoms)
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX purchase output buckets exceed owned amount",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-amm-purchase-journal-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXBurnJournalV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub route_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub issue_burn_policy_root: RootV1,
    pub buyback_budget_occurrence_root: RootV1,
    pub authorized_quote_input_atoms: u128,
    pub purchase_occurrence_root: RootV1,
    pub route_context_root: RootV1,
    pub zdex_asset_id: RootV1,
    pub burn_bucket_id: String,
    pub burned_zdex_atoms: u128,
    pub burn_bucket_pre_atoms: u128,
    pub burn_bucket_post_atoms: u128,
    pub zdex_owned_pre_atoms: u128,
    pub zdex_owned_post_atoms: u128,
    pub zdex_supply_pre_atoms: u128,
    pub zdex_supply_post_atoms: u128,
    pub pre_tokenomics_burn_substate_root: RootV1,
    pub post_tokenomics_burn_substate_root: RootV1,
    pub effect_plan_root: RootV1,
}

impl ZDEXBurnJournalV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "ZDEX burn chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.route_release_id,
            &self.command_occurrence_id,
            &self.tokenomics_module_release_id,
            &self.issue_burn_policy_root,
            &self.buyback_budget_occurrence_root,
            &self.purchase_occurrence_root,
            &self.route_context_root,
            &self.zdex_asset_id,
            &self.pre_tokenomics_burn_substate_root,
            &self.post_tokenomics_burn_substate_root,
            &self.effect_plan_root,
        ] {
            root.validate("ZDEX burn root", false)?;
        }
        validate_token_v1(&self.burn_bucket_id, "ZDEX burn bucket")?;
        validate_positive_effect_amount_v1(
            self.authorized_quote_input_atoms,
            "ZDEX authorized quote input",
        )?;
        validate_positive_effect_amount_v1(self.burned_zdex_atoms, "ZDEX burn amount")?;
        if self
            .zdex_owned_post_atoms
            .checked_add(self.burned_zdex_atoms)
            != Some(self.zdex_owned_pre_atoms)
        {
            return Err(AbiErrorV1::Conservation("ZDEX burn owned projection"));
        }
        if self
            .zdex_supply_post_atoms
            .checked_add(self.burned_zdex_atoms)
            != Some(self.zdex_supply_pre_atoms)
        {
            return Err(AbiErrorV1::Conservation("ZDEX burn supply projection"));
        }
        if self.burn_bucket_pre_atoms != self.burned_zdex_atoms || self.burn_bucket_post_atoms != 0
        {
            return Err(AbiErrorV1::Conservation(
                "ZDEX burn transient bucket projection",
            ));
        }
        Ok(())
    }

    pub fn journal_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-authorized-burn-journal-v1", self)
    }
}
