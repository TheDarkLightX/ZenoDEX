use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_economic_command_body_v1, hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1,
    RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::state::{TerminalObligationStatusV1, TerminalObligationV1};

pub const PERPS_MARGIN_MODULE_SCHEMA_V1: &str = "zenodex/perps-margin-module/v1";
pub const PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1: &str = "zenodex/perps-margin-module-input/v1";
pub const PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1: &str = "zenodex/perps-margin-private-port/v1";
pub const PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V1: &str =
    "zenodex/perps-margin-terminal-obligation-id/v1";
pub const MAX_PERPS_MARGIN_ACCOUNTS_V1: usize = 64;
pub const PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1: &str = "perps_margin_deposit";
pub const PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1: &str = "perps_margin_withdraw";
pub const PERPS_MARGIN_CLOSE_COMMAND_KIND_V1: &str = "perps_margin_close";
pub const PERPS_MARGIN_CUSTODY_DOMAIN_V1: &str = "perps_margin";
pub const BPS_SCALE_V1: u128 = 10_000;
const BPS_SCALE_U64_V1: u64 = 10_000;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum PerpsMarginAccountStatusV1 {
    OPEN,
    CLOSED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PerpsMarginMarketStatusV1 {
    ACTIVE,
    DRAIN_ONLY,
    HALTED,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PerpsMarginRejectCodeV1 {
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    MARKET_DRAIN_ONLY,
    HALTED_MARKET,
    MARKET_MISMATCH,
    ASSET_MISMATCH,
    UNAUTHORIZED_SUBJECT,
    ORACLE_AUTHORITY_MISSING,
    ORACLE_PRICE_MISMATCH,
    UNEXPECTED_ORACLE_AUTHORITY,
    ACCOUNT_MISSING,
    ACCOUNT_OWNER_MISMATCH,
    ACCOUNT_CLOSED,
    ACCOUNT_LIMIT,
    NONCE_MISMATCH,
    NONCE_OVERFLOW,
    ZERO_AMOUNT,
    INVALID_CLOSE_AMOUNT,
    EFFECT_DELTA_OVERFLOW,
    BALANCE_OVERFLOW,
    INSUFFICIENT_COLLATERAL,
    MAINTENANCE_BREACH,
    POSITION_OPEN,
    COLLATERAL_REMAINS,
    ARITHMETIC_OVERFLOW,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginAccountV1 {
    pub account_id: String,
    pub owner: String,
    pub position_base: i128,
    pub entry_price_e8: u128,
    pub collateral_atoms: u128,
    pub nonce: u64,
    pub status: PerpsMarginAccountStatusV1,
}

impl PerpsMarginAccountV1 {
    fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.account_id, "perps margin account id")?;
        validate_token_v1(&self.owner, "perps margin account owner")?;
        if self.position_base == 0 && self.entry_price_e8 != 0 {
            return Err(AbiErrorV1::InvalidBinding(
                "flat perps margin account entry price",
            ));
        }
        if self.position_base != 0 && self.entry_price_e8 == 0 {
            return Err(AbiErrorV1::InvalidBinding(
                "open perps margin position entry price",
            ));
        }
        if self.status == PerpsMarginAccountStatusV1::CLOSED
            && (self.position_base != 0 || self.entry_price_e8 != 0 || self.collateral_atoms != 0)
        {
            return Err(AbiErrorV1::InvalidBinding(
                "closed perps margin account is not flat and empty",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginStateV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub market_id: String,
    pub collateral_asset: String,
    pub index_price_e8: u128,
    pub maintenance_margin_bps: u64,
    pub depeg_buffer_bps: u64,
    pub max_position_abs: u128,
    pub market_status: PerpsMarginMarketStatusV1,
    pub accounts: Vec<PerpsMarginAccountV1>,
}

impl PerpsMarginStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARGIN_MODULE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("perps margin module release id", false)?;
        validate_token_v1(&self.market_id, "perps margin market id")?;
        validate_token_v1(&self.collateral_asset, "perps margin collateral asset")?;
        if self.index_price_e8 == 0 {
            return Err(AbiErrorV1::InvalidBounds("perps margin index price"));
        }
        if self.maintenance_margin_bps == 0
            || self.maintenance_margin_bps > BPS_SCALE_U64_V1
            || self.depeg_buffer_bps > BPS_SCALE_U64_V1
        {
            return Err(AbiErrorV1::InvalidBounds("perps margin bps"));
        }
        let risk_bps = self
            .maintenance_margin_bps
            .checked_add(self.depeg_buffer_bps)
            .ok_or(AbiErrorV1::InvalidBounds("perps margin bps overflow"))?;
        if risk_bps > BPS_SCALE_U64_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "perps margin maintenance plus depeg bps",
            ));
        }
        if self.max_position_abs == 0 {
            return Err(AbiErrorV1::InvalidBounds("perps margin max position"));
        }
        self.max_position_abs
            .checked_mul(self.index_price_e8)
            .and_then(|value| value.checked_mul(u128::from(risk_bps)))
            .ok_or(AbiErrorV1::InvalidBounds(
                "perps margin maintenance envelope overflow",
            ))?;
        if self
            .accounts
            .windows(2)
            .any(|pair| pair[0].account_id >= pair[1].account_id)
        {
            return Err(AbiErrorV1::InvalidOrder("perps margin accounts"));
        }
        if self.accounts.len() > MAX_PERPS_MARGIN_ACCOUNTS_V1 {
            return Err(AbiErrorV1::InvalidBounds("perps margin account count"));
        }
        let mut positive_position = 0_u128;
        let mut negative_position = 0_u128;
        for account in &self.accounts {
            account.validate()?;
            if account.position_base.unsigned_abs() > self.max_position_abs {
                return Err(AbiErrorV1::InvalidBounds("perps margin account position"));
            }
            if account.position_base != 0 && account.entry_price_e8 != self.index_price_e8 {
                return Err(AbiErrorV1::InvalidBinding(
                    "perps margin open position index",
                ));
            }
            if account.position_base >= 0 {
                positive_position = positive_position
                    .checked_add(account.position_base.unsigned_abs())
                    .ok_or(AbiErrorV1::InvalidBounds(
                        "perps margin positive position total",
                    ))?;
            } else {
                negative_position = negative_position
                    .checked_add(account.position_base.unsigned_abs())
                    .ok_or(AbiErrorV1::InvalidBounds(
                        "perps margin negative position total",
                    ))?;
            }
        }
        if positive_position != negative_position {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin peer-to-peer net position",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("perps-margin-state-v1", self)
    }

    pub fn account(&self, account_id: &str) -> Option<&PerpsMarginAccountV1> {
        self.accounts
            .iter()
            .find(|account| account.account_id == account_id)
    }

    pub fn terminal_obligations(&self) -> AbiResultV1<Vec<TerminalObligationV1>> {
        let mut obligations = self
            .accounts
            .iter()
            .map(|account| {
                let obligation_id = hash_global_v1(
                    "perps-margin-terminal-obligation-id-v1",
                    &PerpsMarginTerminalObligationIdBodyV1 {
                        schema: PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V1,
                        lane_id: LaneIdV1::PERPS_MARKET,
                        module_release_id: &self.module_release_id,
                        market_id: &self.market_id,
                        account_id: &account.account_id,
                    },
                )?;
                Ok(TerminalObligationV1 {
                    obligation_id: obligation_id.as_str().to_owned(),
                    lane_id: LaneIdV1::PERPS_MARKET,
                    claimant: account.owner.clone(),
                    asset: self.collateral_asset.clone(),
                    amount_atoms: account.collateral_atoms,
                    status: if account.status == PerpsMarginAccountStatusV1::OPEN {
                        TerminalObligationStatusV1::OPEN
                    } else {
                        TerminalObligationStatusV1::DRAINED
                    },
                })
            })
            .collect::<AbiResultV1<Vec<_>>>()?;
        obligations.sort_by(|left, right| left.obligation_id.cmp(&right.obligation_id));
        Ok(obligations)
    }

    pub fn terminal_obligations_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "perps-margin-terminal-obligations-v1",
            &self.terminal_obligations()?,
        )
    }
}

#[derive(Serialize)]
struct PerpsMarginTerminalObligationIdBodyV1<'a> {
    schema: &'static str,
    lane_id: LaneIdV1,
    module_release_id: &'a RootV1,
    market_id: &'a str,
    account_id: &'a str,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub subject_id: String,
    pub grant_root: RootV1,
    pub oracle_authority_root: RootV1,
    pub oracle_occurrence_root: RootV1,
    pub oracle_price_e8: u128,
}

impl PerpsMarginContextV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "perps margin context chain")?;
        self.deployment_root
            .validate("perps margin context deployment", false)?;
        self.profile_root
            .validate("perps margin context profile", false)?;
        self.module_release_id
            .validate("perps margin context module release", false)?;
        self.command_occurrence_id
            .validate("perps margin context occurrence", false)?;
        validate_token_v1(&self.subject_id, "perps margin context subject")?;
        self.grant_root
            .validate("perps margin context grant", false)?;
        self.oracle_authority_root
            .validate("perps margin context oracle authority", true)?;
        self.oracle_occurrence_root
            .validate("perps margin context oracle occurrence", true)?;
        let presence = [
            !self.oracle_authority_root.is_zero(),
            !self.oracle_occurrence_root.is_zero(),
            self.oracle_price_e8 != 0,
        ];
        if presence.iter().any(|present| *present) && !presence.iter().all(|present| *present) {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin Oracle binding must be wholly absent or present",
            ));
        }
        Ok(())
    }

    pub fn has_oracle_authority(&self) -> bool {
        !self.oracle_authority_root.is_zero()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginCommandV1 {
    pub command_kind: String,
    pub account_id: String,
    pub market_id: String,
    pub owner: String,
    pub asset: String,
    pub amount_atoms: u128,
    pub nonce: u64,
}

impl PerpsMarginCommandV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.command_kind, "perps margin command kind")?;
        validate_token_v1(&self.account_id, "perps margin command account")?;
        validate_token_v1(&self.market_id, "perps margin command market")?;
        validate_token_v1(&self.owner, "perps margin command owner")?;
        validate_token_v1(&self.asset, "perps margin command asset")
    }

    pub fn command_body_hash(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_economic_command_body_v1(&self.command_kind, self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginPrivatePortV1 {
    pub schema: String,
    pub producer_module_schema: String,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub command_body_hash: RootV1,
    pub market_id: String,
    pub account_id: String,
    pub module_effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
    pub oracle_authority_root: RootV1,
    pub oracle_occurrence_root: RootV1,
    pub oracle_price_e8: u128,
}

impl PerpsMarginPrivatePortV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1
            || self.producer_module_schema != PERPS_MARGIN_MODULE_SCHEMA_V1
        {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("perps margin private port release", false)?;
        self.command_occurrence_id
            .validate("perps margin private port occurrence", false)?;
        self.command_body_hash
            .validate("perps margin private port command body", false)?;
        validate_token_v1(&self.market_id, "perps margin private port market")?;
        validate_token_v1(&self.account_id, "perps margin private port account")?;
        self.module_effect_plan_root
            .validate("perps margin private port effect plan", false)?;
        self.terminal_obligations_root
            .validate("perps margin private port terminal obligations", false)?;
        self.oracle_authority_root
            .validate("perps margin private port oracle authority", true)?;
        self.oracle_occurrence_root
            .validate("perps margin private port oracle occurrence", true)?;
        let presence = [
            !self.oracle_authority_root.is_zero(),
            !self.oracle_occurrence_root.is_zero(),
            self.oracle_price_e8 != 0,
        ];
        if presence.iter().any(|present| *present) && !presence.iter().all(|present| *present) {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin private-port Oracle binding is partial",
            ));
        }
        Ok(())
    }

    pub fn port_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("perps-margin-private-port-v1", self)
    }
}

#[derive(Serialize)]
struct PerpsMarginReceiptBodyV1<'a> {
    statement_root: &'a RootV1,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

pub(crate) fn perps_margin_receipt_root_v1(
    statement_root: &RootV1,
    pre_state_root: &RootV1,
    post_state_root: &RootV1,
    effects: &GlobalEconomicEffectPlanV1,
    private_port: &PerpsMarginPrivatePortV1,
) -> AbiResultV1<RootV1> {
    let effect_plan_root = effects.effect_plan_root()?;
    let private_port_root = private_port.port_root()?;
    hash_global_v1(
        "perps-margin-receipt-v1",
        &PerpsMarginReceiptBodyV1 {
            statement_root,
            pre_state_root,
            post_state_root,
            effect_plan_root: &effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &private_port.terminal_obligations_root,
        },
    )
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginAcceptedV1 {
    pub statement_root: RootV1,
    pub post_state: PerpsMarginStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub module_journal: LaneModuleTransitionJournalV1,
    pub private_port: PerpsMarginPrivatePortV1,
    pub terminal_obligations: Vec<TerminalObligationV1>,
}

impl PerpsMarginAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.statement_root
            .validate("perps margin accepted statement", false)?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        self.private_port.validate()?;
        if self.terminal_obligations != self.post_state.terminal_obligations()? {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin accepted terminal obligations",
            ));
        }
        if self.module_journal.lane_id != LaneIdV1::PERPS_MARKET
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.private_port.module_release_id != self.module_journal.module_release_id
            || self.private_port.command_occurrence_id != self.module_journal.command_occurrence_id
            || self.private_port.module_effect_plan_root != self.effects.effect_plan_root()?
            || self.private_port.market_id != self.post_state.market_id
            || self
                .post_state
                .account(&self.private_port.account_id)
                .is_none()
            || self.module_journal.private_port_root != self.private_port.port_root()?
            || self.module_journal.terminal_obligations_root != self.terminal_obligations_root()?
            || self.private_port.terminal_obligations_root != self.terminal_obligations_root()?
            || self.module_journal.receipt_root
                != perps_margin_receipt_root_v1(
                    &self.statement_root,
                    &self.module_journal.pre_lane_root,
                    &self.module_journal.post_lane_root,
                    &self.effects,
                    &self.private_port,
                )?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin accepted module journal",
            ));
        }
        Ok(())
    }

    pub fn terminal_obligations_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "perps-margin-terminal-obligations-v1",
            &self.terminal_obligations,
        )
    }

    pub fn receipt_root(&self) -> &RootV1 {
        &self.module_journal.receipt_root
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginRejectedV1 {
    pub code: PerpsMarginRejectCodeV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl PerpsMarginRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state_root
            .validate("perps margin rejected pre-state", false)?;
        self.post_state_root
            .validate("perps margin rejected post-state", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "perps margin rejection must be an exact no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PerpsMarginResultV1 {
    Accepted(Box<PerpsMarginAcceptedV1>),
    Rejected(Box<PerpsMarginRejectedV1>),
}
