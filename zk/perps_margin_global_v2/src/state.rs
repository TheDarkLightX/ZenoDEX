//! Owned V2 perps state and occurrence-bound terminal claims.
//!
//! The economic fields remain the reviewed V1 arithmetic value.  This wrapper
//! adds the account-to-claim index required to compose that value into the V2
//! global terminal table.  It owns its inputs and grants no authority.

use std::collections::BTreeSet;

use serde::Serialize;
use zenodex_global_settlement_abi_v1::{
    PerpsMarginAccountV1, PerpsMarginStateV1, RootV1, MAX_PERPS_MARGIN_ACCOUNTS_V1,
};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, hash_global_v2, validate_token_v2, AbiErrorV2, AbiResultV2, LaneIdV2,
    RootV2,
};

pub const PERPS_MARGIN_MODULE_SCHEMA_V2: &str = "zenodex/perps-margin-module/v2";
pub const PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2: &str =
    "zenodex/perps-margin-terminal-obligation-id/v2";
pub const PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2: &str =
    "perps-margin-terminal-obligation-id-v2";
pub const MAX_PERPS_MARGIN_ACCOUNTS_V2: usize = MAX_PERPS_MARGIN_ACCOUNTS_V1;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PerpsMarginClaimBindingV2 {
    pub account_id: String,
    pub obligation_id: String,
}

impl PerpsMarginClaimBindingV2 {
    pub fn new(
        account_id: impl Into<String>,
        obligation_id: impl Into<String>,
    ) -> AbiResultV2<Self> {
        let value = Self {
            account_id: account_id.into(),
            obligation_id: obligation_id.into(),
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.account_id, "perps margin claim account id")?;
        RootV2::parse(
            self.obligation_id.clone(),
            "perps margin claim obligation id",
            false,
        )
        .map(|_| ())
    }
}

#[derive(Serialize)]
pub struct PerpsMarginClaimBindingCanonicalV2<'a> {
    pub account_id: &'a str,
    pub obligation_id: &'a str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PerpsMarginStateV2 {
    /// This is an owned internal arithmetic snapshot.  It is never serialized
    /// directly because its V1 schema must not escape the V2 boundary.
    pub economic_state: PerpsMarginStateV1,
    pub active_claims: Vec<PerpsMarginClaimBindingV2>,
}

#[derive(Serialize)]
pub struct PerpsMarginStateCanonicalV2<'a> {
    pub schema: &'static str,
    pub module_release_id: &'a RootV1,
    pub market_id: &'a str,
    pub collateral_asset: &'a str,
    pub index_price_e8: u128,
    pub maintenance_margin_bps: u64,
    pub depeg_buffer_bps: u64,
    pub max_position_abs: u128,
    pub market_status: zenodex_global_settlement_abi_v1::PerpsMarginMarketStatusV1,
    pub accounts: &'a [PerpsMarginAccountV1],
    pub active_claims: Vec<PerpsMarginClaimBindingCanonicalV2<'a>>,
}

impl PerpsMarginStateV2 {
    pub fn new(
        economic_state: PerpsMarginStateV1,
        active_claims: Vec<PerpsMarginClaimBindingV2>,
    ) -> AbiResultV2<Self> {
        let value = Self {
            economic_state,
            active_claims,
        };
        value.validate()?;
        Ok(value)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        self.economic_state
            .validate()
            .map_err(|_| AbiErrorV2::InvalidBinding("perps margin V1 economic snapshot"))?;
        if self.active_claims.len() > MAX_PERPS_MARGIN_ACCOUNTS_V2 {
            return Err(AbiErrorV2::InvalidBounds("perps margin active claim count"));
        }
        for binding in &self.active_claims {
            binding.validate()?;
        }
        if self
            .active_claims
            .windows(2)
            .any(|pair| pair[0].account_id >= pair[1].account_id)
        {
            return Err(AbiErrorV2::InvalidOrder(
                "perps margin active claims by account",
            ));
        }
        let obligation_ids = self
            .active_claims
            .iter()
            .map(|binding| binding.obligation_id.as_str())
            .collect::<BTreeSet<_>>();
        if obligation_ids.len() != self.active_claims.len() {
            return Err(AbiErrorV2::InvalidBinding(
                "perps margin active claim obligation uniqueness",
            ));
        }
        let positive_accounts = self
            .economic_state
            .accounts
            .iter()
            .filter(|account| account.collateral_atoms > 0)
            .map(|account| account.account_id.as_str())
            .collect::<BTreeSet<_>>();
        let bound_accounts = self
            .active_claims
            .iter()
            .map(|binding| binding.account_id.as_str())
            .collect::<BTreeSet<_>>();
        if positive_accounts != bound_accounts {
            return Err(AbiErrorV2::InvalidBinding(
                "perps margin active claims positive account coverage",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("perps-margin-state-v2", &self.to_canonical())
    }

    pub fn claim_id(&self, account_id: &str) -> AbiResultV2<Option<String>> {
        validate_token_v2(account_id, "perps margin claim lookup account id")?;
        Ok(self
            .active_claims
            .iter()
            .find(|binding| binding.account_id == account_id)
            .map(|binding| binding.obligation_id.clone()))
    }

    pub fn to_canonical(&self) -> PerpsMarginStateCanonicalV2<'_> {
        PerpsMarginStateCanonicalV2 {
            schema: PERPS_MARGIN_MODULE_SCHEMA_V2,
            module_release_id: &self.economic_state.module_release_id,
            market_id: &self.economic_state.market_id,
            collateral_asset: &self.economic_state.collateral_asset,
            index_price_e8: self.economic_state.index_price_e8,
            maintenance_margin_bps: self.economic_state.maintenance_margin_bps,
            depeg_buffer_bps: self.economic_state.depeg_buffer_bps,
            max_position_abs: self.economic_state.max_position_abs,
            market_status: self.economic_state.market_status,
            accounts: &self.economic_state.accounts,
            active_claims: self
                .active_claims
                .iter()
                .map(|binding| PerpsMarginClaimBindingCanonicalV2 {
                    account_id: &binding.account_id,
                    obligation_id: &binding.obligation_id,
                })
                .collect(),
        }
    }

    pub fn canonical_bytes(&self) -> AbiResultV2<Vec<u8>> {
        self.validate()?;
        canonical_bytes_v2(&self.to_canonical())
    }
}

pub fn margin_claim_id_v2(
    state: &PerpsMarginStateV1,
    account_id: &str,
    occurrence_id: &RootV2,
) -> AbiResultV2<RootV2> {
    state
        .validate()
        .map_err(|_| AbiErrorV2::InvalidBinding("perps margin claim V1 state"))?;
    validate_token_v2(account_id, "perps margin claim account id")?;
    occurrence_id.validate("perps margin claim opening occurrence id", false)?;
    let module_release_id = RootV2::parse(
        state.module_release_id.as_str().to_owned(),
        "perps margin claim module release id",
        false,
    )?;
    validate_token_v2(&state.market_id, "perps margin claim market id")?;
    validate_token_v2(
        &state.collateral_asset,
        "perps margin claim collateral asset",
    )?;

    #[derive(Serialize)]
    struct ClaimIdBodyV2<'a> {
        schema: &'static str,
        lane_id: LaneIdV2,
        module_release_id: &'a RootV2,
        market_id: &'a str,
        collateral_asset: &'a str,
        account_id: &'a str,
        opening_occurrence_id: &'a RootV2,
    }

    hash_global_v2(
        PERPS_MARGIN_TERMINAL_OBLIGATION_ID_DOMAIN_V2,
        &ClaimIdBodyV2 {
            schema: PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V2,
            lane_id: LaneIdV2::PERPS_MARKET,
            module_release_id: &module_release_id,
            market_id: &state.market_id,
            collateral_asset: &state.collateral_asset,
            account_id,
            opening_occurrence_id: occurrence_id,
        },
    )
}
