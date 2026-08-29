use serde::Serialize;

use crate::canonical::{hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::release::{LaneIdV1, ALL_LANE_IDS_V1};

pub const LANE_CAPABILITY_REGISTRY_SCHEMA_V1: &str = "zenodex/lane-capability-registry/v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneCapabilityDispositionV1 {
    REQUIRED_UNRESOLVED,
    DISABLED_PENDING_COMPLETE_PROFILE,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LaneCapabilitySetV1 {
    pub lane_id: LaneIdV1,
    pub disposition: LaneCapabilityDispositionV1,
    pub capability_ids: &'static [&'static str],
}

pub static LANE_CAPABILITY_REGISTRY_V1: &[LaneCapabilitySetV1] = &[
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::ASSET_TRANSFER,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "account_lifecycle",
            "native_asset_accounting",
            "generic_transfer",
            "managed_issue",
            "managed_burn",
            "transaction_fee",
            "tau_originated_asset_registration",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::SPOT_LIQUIDITY,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "pool_create",
            "exact_in_swap",
            "exact_out_swap",
            "governed_route",
            "atomic_batch",
            "lp_issue",
            "lp_burn",
            "pool_close",
            "fee_allocation",
            "residue_terminal_disposition",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::FARM_INCENTIVES,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "lp_stake",
            "stake_activation",
            "emission_accrual",
            "emission_claim",
            "farm_cancellation",
            "farm_terminal_drain",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "fee_routing",
            "staking_claim",
            "host_compensation_claim",
            "treasury_claim",
            "reserve_lifecycle",
            "atomic_purchase_and_burn",
            "retained_supply_hyperdeflation",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::ZUSD_MONETARY,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "vault_open",
            "collateral_deposit",
            "collateral_withdraw",
            "zusd_mint",
            "zusd_repay",
            "vault_owner_close",
            "multi_vault_redemption",
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "stability_pool_claim",
            "liquidation",
            "recovery_mode",
            "all_claims_terminal_drain",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::PERPS_MARKET,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "margin_deposit",
            "margin_withdraw",
            "position_open",
            "position_adjust",
            "funding_accrual",
            "fee_allocation",
            "liquidation",
            "insurance_reserve",
            "auto_deleveraging",
            "bankruptcy_resolution",
            "terminal_closeout",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::ORACLE_MARKET,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "query_create",
            "tip_escrow",
            "reporter_bond",
            "report_submit",
            "report_finality",
            "reporter_reward",
            "report_dispute",
            "reward_clawback",
            "reporter_slash",
            "oracle_terminal_drain",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::SEALED_AUCTION,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "bid_commitment",
            "bond_accounting_location",
            "bid_reveal",
            "deterministic_clearing",
            "payment_settlement",
            "inventory_settlement",
            "refund",
            "slash",
            "auction_cancel",
            "auction_expiry",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::STRATEGY_ESCROW,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "value_reservation",
            "strategy_activation",
            "strategy_trigger",
            "strategy_replace",
            "strategy_cancel",
            "strategy_expiry",
            "strategy_recovery",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::PROOF_REWARDS,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "reward_reserve",
            "verified_result_binding",
            "claimant_binding",
            "claim_nullifier",
            "reward_payout",
            "task_terminal_state",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::EXTERNAL_CUSTODY,
        disposition: LaneCapabilityDispositionV1::DISABLED_PENDING_COMPLETE_PROFILE,
        capability_ids: &[
            "registered_external_lock",
            "registered_external_burn",
            "registered_external_release",
            "registered_external_mint",
            "external_finality",
            "external_timeout",
            "external_refund",
            "outbox_acknowledgment",
            "destination_idempotency",
        ],
    },
    LaneCapabilitySetV1 {
        lane_id: LaneIdV1::GOVERNANCE_MIGRATION,
        disposition: LaneCapabilityDispositionV1::REQUIRED_UNRESOLVED,
        capability_ids: &[
            "asset_registry_change",
            "parameter_change",
            "release_activation",
            "treasury_action",
            "schema_migration",
            "writer_epoch_rotation",
            "autonomous_governance_command_submission",
        ],
    },
];

pub fn validate_lane_capability_registry_v1() -> AbiResultV1<()> {
    if LANE_CAPABILITY_REGISTRY_V1.len() != ALL_LANE_IDS_V1.len()
        || LANE_CAPABILITY_REGISTRY_V1
            .iter()
            .map(|row| row.lane_id)
            .ne(ALL_LANE_IDS_V1)
    {
        return Err(AbiErrorV1::InvalidOrder("lane capability registry"));
    }
    let mut total = 0usize;
    let mut disabled = Vec::new();
    for row in LANE_CAPABILITY_REGISTRY_V1 {
        if row.capability_ids.is_empty() {
            return Err(AbiErrorV1::InvalidBounds("lane capability ids"));
        }
        for (index, capability_id) in row.capability_ids.iter().enumerate() {
            validate_token_v1(capability_id, "lane capability id")?;
            if row.capability_ids[..index].contains(capability_id) {
                return Err(AbiErrorV1::InvalidOrder("lane capability ids"));
            }
        }
        total = total.saturating_add(row.capability_ids.len());
        if row.disposition == LaneCapabilityDispositionV1::DISABLED_PENDING_COMPLETE_PROFILE {
            disabled.push(row.lane_id);
        }
    }
    if total != 103 || disabled != [LaneIdV1::EXTERNAL_CUSTODY] {
        return Err(AbiErrorV1::InvalidBinding(
            "lane capability registry disposition",
        ));
    }
    Ok(())
}

pub fn resolve_lane_capability_v1(
    lane_id: LaneIdV1,
    capability_id: &str,
) -> AbiResultV1<&'static str> {
    validate_lane_capability_registry_v1()?;
    validate_token_v1(capability_id, "lane capability id")?;
    let lane = &LANE_CAPABILITY_REGISTRY_V1[ALL_LANE_IDS_V1
        .iter()
        .position(|candidate| *candidate == lane_id)
        .ok_or(AbiErrorV1::InvalidBinding("unknown lane capability"))?];
    lane.capability_ids
        .iter()
        .copied()
        .find(|candidate| *candidate == capability_id)
        .ok_or(AbiErrorV1::InvalidBinding("unknown lane capability"))
}

#[derive(Serialize)]
struct RegistryRowV1<'a> {
    capability_ids: &'a [&'static str],
    disposition: LaneCapabilityDispositionV1,
    lane_id: LaneIdV1,
}

#[derive(Serialize)]
struct RegistryBodyV1<'a> {
    lanes: Vec<RegistryRowV1<'a>>,
    schema: &'static str,
}

pub fn lane_capability_registry_root_v1() -> AbiResultV1<RootV1> {
    validate_lane_capability_registry_v1()?;
    let lanes = LANE_CAPABILITY_REGISTRY_V1
        .iter()
        .map(|row| RegistryRowV1 {
            capability_ids: row.capability_ids,
            disposition: row.disposition,
            lane_id: row.lane_id,
        })
        .collect();
    hash_global_v1(
        "lane-capability-registry-v1",
        &RegistryBodyV1 {
            lanes,
            schema: LANE_CAPABILITY_REGISTRY_SCHEMA_V1,
        },
    )
}
