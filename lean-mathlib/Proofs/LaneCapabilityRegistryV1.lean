import Init

/-!
The closed 103-capability vocabulary owned by the twelve
`GlobalSettlementABI V1` lanes.  A capability is represented by a lane and a
bounded ordinal into that lane's exact name list.  The representation makes a
capability outside the registry unconstructable.

Nonclaims: this file proves vocabulary size and lane ownership only.  It does
not implement any transition, select unresolved economic policy, establish
runtime refinement, authenticate a command, verify a receipt, mount a release,
or authorize value movement.
-/

namespace Proofs
namespace LaneCapabilityRegistryV1

inductive LaneId where
  | assetTransfer
  | spotLiquidity
  | farmIncentives
  | zdexTokenomics
  | zusdMonetary
  | perpsMarket
  | oracleMarket
  | sealedAuction
  | strategyEscrow
  | proofRewards
  | externalCustody
  | governanceMigration
  deriving DecidableEq, Repr

def allLaneIds : List LaneId :=
  [ .assetTransfer, .spotLiquidity, .farmIncentives, .zdexTokenomics,
    .zusdMonetary, .perpsMarket, .oracleMarket, .sealedAuction,
    .strategyEscrow, .proofRewards, .externalCustody, .governanceMigration ]

def capabilityNames : LaneId → List String
  | .assetTransfer =>
      [ "account_lifecycle", "native_asset_accounting", "generic_transfer",
        "managed_issue", "managed_burn", "transaction_fee",
        "tau_originated_asset_registration" ]
  | .spotLiquidity =>
      [ "pool_create", "exact_in_swap", "exact_out_swap", "governed_route",
        "atomic_batch", "lp_issue", "lp_burn", "pool_close",
        "fee_allocation", "residue_terminal_disposition" ]
  | .farmIncentives =>
      [ "lp_stake", "stake_activation", "emission_accrual",
        "emission_claim", "farm_cancellation", "farm_terminal_drain" ]
  | .zdexTokenomics =>
      [ "fee_routing", "staking_claim", "host_compensation_claim",
        "treasury_claim", "reserve_lifecycle", "atomic_purchase_and_burn",
        "retained_supply_hyperdeflation" ]
  | .zusdMonetary =>
      [ "vault_open", "collateral_deposit", "collateral_withdraw", "zusd_mint",
        "zusd_repay", "vault_owner_close", "multi_vault_redemption",
        "stability_pool_deposit", "stability_pool_withdraw",
        "stability_pool_claim", "liquidation", "recovery_mode",
        "all_claims_terminal_drain" ]
  | .perpsMarket =>
      [ "margin_deposit", "margin_withdraw", "position_open", "position_adjust",
        "funding_accrual", "fee_allocation", "liquidation",
        "insurance_reserve", "auto_deleveraging", "bankruptcy_resolution",
        "terminal_closeout" ]
  | .oracleMarket =>
      [ "query_create", "tip_escrow", "reporter_bond", "report_submit",
        "report_finality", "reporter_reward", "report_dispute",
        "reward_clawback", "reporter_slash", "oracle_terminal_drain" ]
  | .sealedAuction =>
      [ "bid_commitment", "bond_accounting_location", "bid_reveal",
        "deterministic_clearing", "payment_settlement", "inventory_settlement",
        "refund", "slash", "auction_cancel", "auction_expiry" ]
  | .strategyEscrow =>
      [ "value_reservation", "strategy_activation", "strategy_trigger",
        "strategy_replace", "strategy_cancel", "strategy_expiry",
        "strategy_recovery" ]
  | .proofRewards =>
      [ "reward_reserve", "verified_result_binding", "claimant_binding",
        "claim_nullifier", "reward_payout", "task_terminal_state" ]
  | .externalCustody =>
      [ "registered_external_lock", "registered_external_burn",
        "registered_external_release", "registered_external_mint",
        "external_finality", "external_timeout", "external_refund",
        "outbox_acknowledgment", "destination_idempotency" ]
  | .governanceMigration =>
      [ "asset_registry_change", "parameter_change", "release_activation",
        "treasury_action", "schema_migration", "writer_epoch_rotation",
        "autonomous_governance_command_submission" ]

def capabilityCount (lane : LaneId) : Nat := (capabilityNames lane).length

theorem capability_names_match_counts (lane : LaneId) :
    capabilityCount lane =
      match lane with
      | .assetTransfer => 7
      | .spotLiquidity => 10
      | .farmIncentives => 6
      | .zdexTokenomics => 7
      | .zusdMonetary => 13
      | .perpsMarket => 11
      | .oracleMarket => 10
      | .sealedAuction => 10
      | .strategyEscrow => 7
      | .proofRewards => 6
      | .externalCustody => 9
      | .governanceMigration => 7 := by
  cases lane <;> rfl

def totalCapabilityCount : Nat :=
  (allLaneIds.map capabilityCount).foldl Nat.add 0

theorem total_capability_count_is_103 : totalCapabilityCount = 103 := by
  decide

structure Capability where
  lane : LaneId
  ordinal : Fin (capabilityCount lane)
  deriving Repr

def Capability.name (capability : Capability) : String :=
  (capabilityNames capability.lane).get capability.ordinal

theorem every_lane_has_a_capability (lane : LaneId) : 0 < capabilityCount lane := by
  cases lane <;> decide

theorem external_capability_count_is_nine :
    capabilityCount .externalCustody = 9 := rfl

theorem proof_reward_capability_count_is_six :
    capabilityCount .proofRewards = 6 := rfl

end LaneCapabilityRegistryV1
end Proofs
