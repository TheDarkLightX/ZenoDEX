"""Typed research contract for the partially selected G1 economic policy.

Only the ZDEX denomination, supply envelope, and liability-first waterfall are
selected here.  Participant compensation and genesis distribution remain open
and keep launch disabled.
"""

from __future__ import annotations

from typing import Final, TypedDict


class ScaledModelingAllocation(TypedDict):
    id: str
    allocation_bps: int
    whole_tokens: int


class ParticipantObligation(TypedDict):
    id: str
    participant_class: str
    value_class: str
    payment_description: str
    affected_profile_decisions: tuple[str, ...]
    affected_commands: tuple[str, ...]
    must_have_explicit_economic_owner: bool
    default_if_unselected: str

ZDEX_SYMBOL: Final = "ZDEX"
ZDEX_WHOLE_SUPPLY: Final = 2_000_000_000
ZDEX_DECIMALS: Final = 18
ZDEX_UNIT_SCALE: Final = 10**ZDEX_DECIMALS
ZDEX_GENESIS_SUPPLY_ATOMS: Final = ZDEX_WHOLE_SUPPLY * ZDEX_UNIT_SCALE
ZDEX_SUPPLY_CEILING_ATOMS: Final = ZDEX_GENESIS_SUPPLY_ATOMS
ZDEX_ABSOLUTE_FLOOR_ATOMS: Final = 1
ZDEX_LAUNCH_ACTIVE_FLOOR_WHOLE: Final = 200_000_000
ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS: Final = (
    ZDEX_LAUNCH_ACTIVE_FLOOR_WHOLE * ZDEX_UNIT_SCALE
)

RESEARCH_SOURCE_PATHS: Final[tuple[str, ...]] = (
    "internal/tokenomics/ZENO_DISTRIBUTION_AND_TREASURY_PLAN_V0.md",
    "internal/tokenomics/ZENO_ECONOMIC_GAMES_BOUNDARY_V0.json",
    "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json",
    "docs/PERMISSIONLESS_HOSTING.md",
    "docs/ORDER_INTENTS.md",
)

PROFILE_DECISION_IDS: Final[frozenset[str]] = frozenset(
    {
        "asset_issue_burn_policy",
        "spot_lp_fee_dust_withdrawal_policy",
        "zusd_monetary_lifecycle_policy",
        "oracle_lifecycle_policy",
        "perps_risk_and_terminal_policy",
        "protocol_buy_burn_policy",
        "proof_reward_reserve_policy",
        "sealed_bid_inventory_and_lifecycle_policy",
        "tau_escrow_outage_rejoin_policy",
    }
)

COMPENSATION_SELECTION_FIELDS: Final[tuple[str, ...]] = (
    "compensation_asset",
    "funding_source",
    "amount_and_rounding_rule",
    "budget_and_epoch_cap",
    "eligibility_witness",
    "claimant_identity",
    "custody_account",
    "claim_and_nullifier_scope",
    "bond_and_slashing_rule",
    "failure_retry_and_exhaustion_rule",
    "conflict_sybil_and_self_dealing_controls",
    "terminal_disposition",
    "tax_counsel_and_legal_activation",
    "release_root",
)

GENESIS_DISTRIBUTION_SELECTION_FIELDS: Final[tuple[str, ...]] = (
    "recipient_and_beneficial_owner_set",
    "allocation_atoms_per_recipient",
    "allocation_purpose",
    "eligibility_and_snapshot_rule",
    "claim_or_direct_delivery_mechanism",
    "vesting_cliff_unlock_and_remainder_rule",
    "transfer_and_resale_restrictions",
    "custody_and_key_recovery",
    "anti_sybil_wash_and_related_party_controls",
    "tax_accounting_compensation_and_counsel_review",
    "unclaimed_expired_and_terminal_disposition",
    "genesis_distribution_root",
)

SCALED_MODELING_ALLOCATIONS: Final[tuple[ScaledModelingAllocation, ...]] = (
    {
        "id": "founder_original_rd",
        "allocation_bps": 1_500,
        "whole_tokens": 300_000_000,
    },
    {
        "id": "core_team_future_contributors",
        "allocation_bps": 1_000,
        "whole_tokens": 200_000_000,
    },
    {
        "id": "dao_protocol_treasury",
        "allocation_bps": 2_500,
        "whole_tokens": 500_000_000,
    },
    {
        "id": "ecosystem_lp_solver_operator_proof_incentives",
        "allocation_bps": 2_500,
        "whole_tokens": 500_000_000,
    },
    {
        "id": "community_retroactive_airdrop_testnet_users",
        "allocation_bps": 1_000,
        "whole_tokens": 200_000_000,
    },
    {
        "id": "security_audits_bounties_insurance_reserve",
        "allocation_bps": 500,
        "whole_tokens": 100_000_000,
    },
    {
        "id": "liquidity_bootstrap_market_making",
        "allocation_bps": 500,
        "whole_tokens": 100_000_000,
    },
    {
        "id": "strategic_partners_investors_chain_partners",
        "allocation_bps": 500,
        "whole_tokens": 100_000_000,
    },
)

PAYMENT_PRIORITY_TIERS: Final = (
    {
        "priority": 0,
        "id": "exact_user_property_and_accrued_liabilities",
        "rule": "PAY_OR_RESERVE_EXACTLY_BEFORE_ANY_DISCRETIONARY_USE",
    },
    {
        "priority": 1,
        "id": "selected_solvency_and_safety_minimums",
        "rule": "FUND_TO_RELEASE_BOUND_TARGET_WITH_EXACT_CAP",
    },
    {
        "priority": 2,
        "id": "prefunded_contracted_service_compensation",
        "rule": "PAY_ONLY_FROM_ROLE_SPECIFIC_BUDGET_AND_ELIGIBILITY_WITNESS",
    },
    {
        "priority": 3,
        "id": "capped_operations_security_and_hosting",
        "rule": "PAY_APPROVED_RECEIPT_OR_SERVICE_CLAIM_WITH_EPOCH_CAP",
    },
    {
        "priority": 4,
        "id": "eligible_surplus_buy_and_burn",
        "rule": "ASSIGN_ALL_REMAINING_ELIGIBLE_SURPLUS_WHEN_BUYBURN_IS_ACTIVE",
    },
    {
        "priority": 5,
        "id": "pending_policy_or_guarded_execution_carry",
        "rule": "CARRY_WITH_NAMED_OWNER_UNTIL_POLICY_OR_EXECUTION_RESOLVES",
    },
)

MECHANISM_IMPROVEMENTS: Final = (
    {
        "id": "close_unnamed_fee_remainder",
        "finding": "The historical fee split names only 7,500 of 10,000 basis points.",
        "closure": "REJECT_GLOBAL_SPLIT_AND_REQUIRE_COMPLETE_PER_LANE_PRIORITY_WATERFALL",
    },
    {
        "id": "disable_burn_indexed_insider_acceleration",
        "finding": "Burn-linked insider unlocks create a benefit from manufacturing eligible burn volume.",
        "closure": "HELD_FOR_LAUNCH_PENDING_ELIGIBLE_BURN_AND_MANIPULATION_PROFIT_GATES",
    },
    {
        "id": "isolate_work_reward_budgets",
        "finding": "One broad ecosystem bucket cannot prove that each service role remains funded or capped.",
        "closure": "REQUIRE_ROLE_SPECIFIC_SUB_BUDGET_ROOTS_AND_NO_CROSS_PROGRAM_BORROWING",
    },
    {
        "id": "separate_host_payment_from_authority",
        "finding": "A paid interface or API host can misreport service attribution or imply trusted settlement.",
        "closure": "AUTHENTICATED_SERVICE_CLAIM_WITH_ZERO_SETTLEMENT_ORDERING_OR_CUSTODY_AUTHORITY",
    },
    {
        "id": "hold_activity_rewards_against_wash_and_legal_risk",
        "finding": "Usage-based rewards can subsidize wash volume and remain legally unresolved.",
        "closure": "DISABLED_UNTIL_COUNSEL_ACTIVATION_AND_OBJECTIVE_ANTI_WASH_RECEIPT_GATE",
    },
)

VOLUME_GROWTH_INCENTIVE_STACK: Final = (
    {
        "rank": 1,
        "id": "loss_bounded_future_fee_credit",
        "target": "repeat genuine trading and retention",
        "status": "PROPOSED_UNSELECTED",
        "instrument": "NONTRANSFERABLE_EXPIRING_CREDIT_AGAINST_FUTURE_PROTOCOL_FEES",
        "parameter_bounds": {
            "earn_bps_minimum": 0,
            "earn_bps_maximum_exclusive": 10_000,
            "redemption_bps_minimum": 0,
            "redemption_bps_maximum_exclusive": 10_000,
            "total_incentive_bps_maximum_exclusive": 10_000,
        },
        "formulas": (
            "credit_redeemed_atoms <= floor(current_gross_protocol_fee_atoms * selected_redemption_bps / 10000)",
            "current_cash_protocol_fee_atoms = current_gross_protocol_fee_atoms - credit_redeemed_atoms",
            "new_credit_atoms <= floor(current_cash_protocol_fee_atoms * selected_earn_bps / 10000)",
            "0 <= selected_earn_bps < 10000",
            "0 <= selected_redemption_bps < 10000",
        ),
        "manipulation_bound": (
            "same_event_protocol_funded_incentive_value_atoms <= floor(" 
            "irreversible_cash_protocol_fee_atoms * selected_total_incentive_bps / 10000), "
            "with selected_total_incentive_bps < 10000"
        ),
        "why_it_targets_the_goal": (
            "A user must return and pay another fee to consume the credit; the "
            "credit cannot be sold, withdrawn, or redeemed for ZDEX or cash."
        ),
        "residual_risks": (
            "reduced buyburn revenue",
            "program stacking unless every same-event benefit shares one cap",
            "retention may be subsidized without producing incremental demand",
        ),
    },
    {
        "rank": 2,
        "id": "executable_depth_reverse_auction",
        "target": "lower slippage and reliable two-sided liquidity",
        "status": "PROPOSED_UNSELECTED",
        "instrument": "SEALED_MINIMUM_SUBSIDY_BID_FOR_TIME_WEIGHTED_EXECUTABLE_DEPTH",
        "parameter_bounds": {
            "payment_atoms_maximum": "SELECTED_PROGRAM_BUDGET_ATOMS",
            "minimum_slash_atoms": "BOUNDED_DEFAULT_GAIN_ATOMS",
        },
        "formulas": (
            "winner = lowest admitted subsidy for the required depth, range, duration, and uptime",
            "payment_atoms <= selected_program_budget_atoms",
            "slash_atoms >= bounded_default_gain_atoms",
        ),
        "manipulation_bound": (
            "Payment depends on capital-at-risk and executable depth receipts, "
            "rather than reported trade volume or address count."
        ),
        "why_it_targets_the_goal": (
            "Deeper executable liquidity reduces user slippage and supports "
            "organic volume without paying for circular trades."
        ),
        "residual_risks": (
            "adverse selection and impermanent loss",
            "collusion among subsidy bidders",
            "oracle and executable-range measurement",
        ),
    },
    {
        "rank": 3,
        "id": "net_surplus_performance_milestone",
        "target": "team and operator growth alignment",
        "status": "PROPOSED_UNSELECTED",
        "instrument": "LAGGED_CAPPED_VESTING_MILESTONE_FROM_REALIZED_NET_SURPLUS",
        "parameter_bounds": {
            "bonus_bps_minimum": 0,
            "bonus_bps_maximum_exclusive": 10_000,
        },
        "formulas": (
            "net_surplus_atoms = realized_protocol_revenue_atoms - all_tier0_through_tier3_atoms",
            "eligible_increment_atoms = max(0, net_surplus_atoms - release_bound_baseline_atoms)",
            "bonus_value_atoms <= floor(eligible_increment_atoms * selected_bonus_bps / 10000)",
            "selected_bonus_bps < 10000",
        ),
        "manipulation_bound": (
            "A self-funded actor contributes at least the realized protocol "
            "revenue while receiving strictly less bonus value."
        ),
        "why_it_targets_the_goal": (
            "The milestone rewards durable fee surplus after every participant "
            "and operating obligation, while raw volume has zero direct weight."
        ),
        "residual_risks": (
            "baseline gaming",
            "cost deferral across epochs",
            "related-party revenue attribution",
            "legal treatment of performance vesting",
        ),
    },
)


def _participant(
    participant_id: str,
    participant_class: str,
    value_class: str,
    payment_description: str,
    affected_decisions: tuple[str, ...],
    affected_commands: tuple[str, ...],
) -> ParticipantObligation:
    return {
        "id": participant_id,
        "participant_class": participant_class,
        "value_class": value_class,
        "payment_description": payment_description,
        "affected_profile_decisions": affected_decisions,
        "affected_commands": affected_commands,
        "must_have_explicit_economic_owner": True,
        "default_if_unselected": "AFFECTED_FEATURE_DISABLED",
    }


PARTICIPANT_OBLIGATIONS: Final[tuple[ParticipantObligation, ...]] = (
    _participant(
        "spot_trader_and_order_user",
        "trader or standing-order user",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive exact swap output, unused input, cancellation refund, and any selected rebate without hidden fee or dust loss.",
        ("spot_lp_fee_dust_withdrawal_policy",),
        ("spot_swap",),
    ),
    _participant(
        "liquidity_provider",
        "liquidity provider",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive the selected LP-owned fee share, proportional reserves, refunds, and complete terminal-pool drain.",
        ("spot_lp_fee_dust_withdrawal_policy",),
        ("lp_add", "lp_remove"),
    ),
    _participant(
        "zusd_borrower_and_redeemer",
        "zUSD borrower, repayer, or redeemer",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive exact zUSD or collateral claims, collateral surplus, and refunds after selected fees and debt settlement.",
        ("zusd_monetary_lifecycle_policy",),
        ("zusd_borrow", "zusd_repay", "zusd_redeem"),
    ),
    _participant(
        "stability_pool_depositor",
        "Stability Pool depositor",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive reconciled remaining deposit, liquidation collateral gains, selected rewards, and terminal withdrawal rights.",
        ("zusd_monetary_lifecycle_policy",),
        (
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "zusd_redistribute",
        ),
    ),
    _participant(
        "liquidator_and_keeper",
        "liquidator or automation keeper",
        "SERVICE_COMPENSATION",
        "Receive a prefunded, bounded reward for an eligible liquidation or maintenance action under a selected anti-race rule.",
        ("zusd_monetary_lifecycle_policy", "perps_risk_and_terminal_policy"),
        ("zusd_liquidate", "perp_liquidate"),
    ),
    _participant(
        "oracle_reporter_aggregator_disputer_and_watcher",
        "oracle reporter, aggregator, disputer, or watcher",
        "SERVICE_COMPENSATION",
        "Receive selected work compensation and valid bond refunds; admitted faults follow the selected slash and beneficiary rule.",
        ("oracle_lifecycle_policy",),
        ("oracle_submit", "oracle_dispute"),
    ),
    _participant(
        "perps_trader_and_funding_counterparty",
        "perpetuals trader or funding counterparty",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive reconciled margin, PnL, funding, close proceeds, and terminal settlement.",
        ("perps_risk_and_terminal_policy",),
        ("perp_open", "perp_close", "perp_funding"),
    ),
    _participant(
        "insurance_and_bad_debt_backstop",
        "insurance or bad-debt backstop provider",
        "SERVICE_COMPENSATION",
        "Receive selected compensation for funded risk capacity while preserving exact loss priority, caps, and withdrawal rights.",
        ("perps_risk_and_terminal_policy", "zusd_monetary_lifecycle_policy"),
        ("perp_liquidate", "zusd_liquidate", "zusd_redistribute"),
    ),
    _participant(
        "sealed_bid_seller",
        "seller-auction seller",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive clearing proceeds, unsold inventory, eligible bond proceeds, cancellation recovery, and terminal drain.",
        ("sealed_bid_inventory_and_lifecycle_policy",),
        (
            "seller_auction_commit",
            "seller_auction_reveal",
            "seller_auction_settle",
            "seller_auction_cancel",
            "seller_auction_expire",
        ),
    ),
    _participant(
        "sealed_bid_bidder_and_private_swap_party",
        "auction bidder or private-swap party",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive filled inventory or reciprocal assets plus all eligible payment, bond, cancel, and expiry refunds.",
        ("sealed_bid_inventory_and_lifecycle_policy",),
        (
            "private_swap_commit",
            "private_swap_reveal",
            "private_swap_settle",
            "private_swap_cancel",
            "private_swap_expire",
        ),
    ),
    _participant(
        "tau_depositor_and_withdrawer",
        "Tau escrow depositor or withdrawer",
        "ECONOMIC_PROPERTY_OR_LIABILITY",
        "Receive one-to-one admitted deposit credit or a durable pending withdrawal that resolves, retries, or refunds under the selected outage policy.",
        ("tau_escrow_outage_rejoin_policy",),
        (
            "tau_escrow_deposit",
            "tau_withdrawal",
            "tau_withdrawal_ack",
            "fallback_activate",
            "tau_rejoin",
        ),
    ),
    _participant(
        "tau_relayer_and_destination_operator",
        "Tau relayer or destination operator",
        "SERVICE_COMPENSATION",
        "Receive bounded compensation for authenticated external delivery or acknowledgment without acquiring settlement authority.",
        ("tau_escrow_outage_rejoin_policy",),
        ("tau_escrow_deposit", "tau_withdrawal", "tau_withdrawal_ack"),
    ),
    _participant(
        "proof_prover_and_proof_miner",
        "prover or proof miner",
        "SERVICE_COMPENSATION",
        "Receive a prefunded reward only for release-selected proof work with duplicate-claim rejection and reserve exhaustion handling.",
        ("proof_reward_reserve_policy",),
        ("zrpf_prover_reward",),
    ),
    _participant(
        "validator_finality_operator",
        "ZenoLedger validator or finality operator",
        "SERVICE_COMPENSATION",
        "Receive selected operating compensation for persisted and validated finality work under explicit equivocation and replacement rules.",
        ("asset_issue_burn_policy",),
        (),
    ),
    _participant(
        "solver_batcher_and_sequencer",
        "solver, batcher, or sequencer",
        "SERVICE_COMPENSATION",
        "Receive bounded compensation for an admitted execution service under canonical selection, censorship, and self-dealing controls.",
        ("spot_lp_fee_dust_withdrawal_policy", "sealed_bid_inventory_and_lifecycle_policy"),
        ("spot_swap", "seller_auction_settle", "private_swap_settle"),
    ),
    _participant(
        "interface_api_and_static_host",
        "web interface, API, static mirror, or Tau-facing host",
        "OPERATING_EXPENSE_OR_SERVICE_COMPENSATION",
        "Receive a governed operating payment or authenticated service payment without correctness, ordering, custody, or settlement authority.",
        ("asset_issue_burn_policy", "tau_escrow_outage_rejoin_policy"),
        (),
    ),
    _participant(
        "security_auditor_and_bounty_researcher",
        "security auditor or bounty researcher",
        "OPERATING_EXPENSE_OR_SERVICE_COMPENSATION",
        "Receive a prefunded milestone or accepted-disclosure payment under duplicate, severity, embargo, and conflict rules.",
        ("asset_issue_burn_policy",),
        (),
    ),
    _participant(
        "core_contributor_contractor_and_operations_provider",
        "core contributor, contractor, legal provider, or operations provider",
        "OPERATING_EXPENSE_OR_SERVICE_COMPENSATION",
        "Receive budgeted compensation against approved work, receipts, milestones, caps, and applicable vesting or clawback terms.",
        ("asset_issue_burn_policy",),
        (),
    ),
    _participant(
        "liquidity_bootstrapper_and_market_maker",
        "liquidity bootstrapper or market maker",
        "SERVICE_COMPENSATION_OR_DISTRIBUTION_PROGRAM",
        "Receive only a selected and capped liquidity-program allocation or fee under depth, duration, anti-wash, and related-party controls.",
        ("asset_issue_burn_policy", "spot_lp_fee_dust_withdrawal_policy"),
        ("lp_add", "lp_remove", "spot_swap"),
    ),
    _participant(
        "community_testnet_and_usage_award_recipient",
        "community, testnet, or usage-based award recipient",
        "DISTRIBUTION_PROGRAM",
        "Receive tokens only through a separately budgeted, counsel-activated program with objective receipts and anti-sybil controls.",
        ("asset_issue_burn_policy",),
        (),
    ),
    _participant(
        "founder_team_partner_and_capital_recipient",
        "founder, team member, partner, or capital provider",
        "GENESIS_OR_VESTED_DISTRIBUTION_PROGRAM",
        "Receive tokens only through an exact genesis-bound allocation with selected vesting, beneficial ownership, custody, tax, and legal treatment.",
        ("asset_issue_burn_policy",),
        (),
    ),
    _participant(
        "protocol_treasury_reserve_and_buyburn_executor",
        "protocol treasury, named reserve owner, or buy-and-burn executor",
        "RESERVE_AND_TERMINAL_OWNERSHIP",
        "Receive only explicitly assigned residuals, operate capped budgets, and route a selected residual lane through the guarded buy-and-burn kernel.",
        ("asset_issue_burn_policy", "protocol_buy_burn_policy"),
        ("protocol_buy_and_burn",),
    ),
)

MECHANISM_REVIEW: Final = {
    "game_surface": {
        "players": tuple(entry["participant_class"] for entry in PARTICIPANT_OBLIGATIONS),
        "actions": (
            "earn or receive an economic entitlement",
            "submit work or service evidence",
            "claim from a prefunded program",
            "fund a reserve or operating budget",
            "allocate genesis supply",
            "buy and burn acquired ZDEX",
            "refund, retry, exhaust, migrate, or terminally drain a program",
        ),
        "authoritative_state": (
            "per-asset balances, escrows, claims, reserves, liabilities, reward budgets, allocation roots, nullifiers, and ZDEX supply"
        ),
    },
    "attack_query": (
        "Can any actor redirect an entitlement, self-award a reward, double claim, "
        "leave a participant unpaid, manufacture eligibility, or sweep an "
        "unselected amount into buy-and-burn or treasury custody?"
    ),
        "bounded_model": {
        "domain": "NONNEGATIVE_CHECKED_INTEGER_ATOMS_PER_ASSET_AND_EPOCH",
        "waterfall": (
            "available[a,e] = protocol_revenue[a,e] + prefunded_release[a,e] + "
            "admitted_slash[a,e] + carry_in[a,e]"
        ),
        "closure": (
            "available[a,e] = tier0_property_and_liability[a,e] + tier1_safety[a,e] + "
            "tier2_service[a,e] + tier3_operations[a,e] + tier4_buyburn[a,e] + "
            "tier5_named_carry[a,e]"
        ),
        "eligible_surplus": (
            "eligible_surplus[a,e] = available[a,e] - tier0[a,e] - tier1[a,e] - "
            "tier2[a,e] - tier3[a,e]"
        ),
        "active_buyburn": "tier4_buyburn[a,e] = eligible_surplus[a,e]",
        "inactive_buyburn": "tier5_named_carry[a,e] = eligible_surplus[a,e]",
        "reward_bound": (
            "reward_paid[a,e] <= prefunded_release[a,e] + admitted_slash[a,e]"
        ),
        "genesis_reconciliation": (
            "sum(selected_genesis_allocation_atoms) = 2000000000 * 10^18"
        ),
        "burn_envelope": (
            "burn_atoms <= floor((supply_before_atoms - active_floor_atoms) / 2)"
        ),
        "protocol_observable_locked_atoms": (
            "genesis_vesting_atoms + reward_reserve_atoms + program_locked_atoms + "
            "active_service_bond_atoms + other_release_bound_nontransferable_atoms"
        ),
        "protocol_observable_liquid_atoms": (
            "total_supply_atoms - protocol_observable_locked_atoms"
        ),
        "protocol_observable_liquid_delta": (
            "-burn_atoms - (locked_after_atoms - locked_before_atoms)"
        ),
        "strict_protocol_observable_float_deflation": (
            "burn_atoms > locked_before_atoms - locked_after_atoms"
        ),
    },
    "evidence_lane": (
        "exact canonical policy artifact",
        "independent per-asset waterfall oracle",
        "stateful claim, replay, exhaustion, cancellation, and terminal histories",
        "named self-award, double-claim, underpayment, and buyburn-sweep mutants",
        "counsel-activated genesis and reward-program release root",
        "Lean conservation and bounded burn proofs",
    ),
    "promotion_boundary": (
        "This record selects only ZDEX denomination, supply, burn bounds, and "
        "liability-first ordering. It selects no allocation, fee split, reward "
        "amount, funding source, participant program, counsel conclusion, launch, "
        "writer, settlement, or release authority."
    ),
    "payment_priority_tiers": PAYMENT_PRIORITY_TIERS,
    "mechanism_improvements": MECHANISM_IMPROVEMENTS,
    "recommended_volume_incentive_stack": VOLUME_GROWTH_INCENTIVE_STACK,
    "burn_indexed_unlock_candidate": {
        "status": "HELD_UNSELECTED",
        "historical_candidate_unlock_bps_of_eligible_burn": 2_500,
        "candidate_formula": (
            "extra_unlock_atoms <= min(selected_epoch_cap_atoms, "
            "floor(eligible_burn_atoms * selected_unlock_bps / 10000))"
        ),
        "required_gates": (
            "original cliff is preserved",
            "only finalized protocol-revenue-funded burns are eligible",
            "treasury-funded, insider-funded, related-party, subsidized, manual, and refunded flows are excluded",
            "eligible value uses a lagged release-bound TWAP",
            "epoch and annual acceleration caps are selected",
            "unlock occurs after a selected lag in a subsequent transition",
            "buyback route cannot be selected or supplied by an undisclosed beneficiary",
            "bounded manipulation-profit oracle reports nonpositive profit",
            "counsel activates the exact vesting amendment and disclosure",
        ),
        "supply_effect": (
            "Within the paired burn and accelerated-unlock event, 2500 bps means "
            "four eligible burned atoms permit at most one atom of earlier "
            "unlock, so that pair reduces protocol-observable liquid supply by "
            "at least three atoms."
        ),
        "residual_risk": (
            "Permissionless addresses do not prove independent beneficial ownership; "
            "related-party and subsidy classification requires explicit premises. "
            "Independent base vesting or reward releases can still increase "
            "protocol-observable liquid supply."
        ),
    },
}
