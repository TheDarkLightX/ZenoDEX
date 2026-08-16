"""Research-only input registry for the nine open G1 profile decisions."""

from __future__ import annotations

TYPES_PATH = "src/core/m6_safe_mount_types_v1.py"
TRANSITION_PATH = "src/core/m6_safe_mount_transition_v1.py"
SOURCE_PATHS = (TYPES_PATH, TRANSITION_PATH)

INPUT_STATUS = "SOURCE_PINNED_RESEARCH_INPUT_NOT_POLICY"
MECHANISM_SECTIONS = frozenset(
    {
        "attack_query",
        "bounded_model",
        "evidence_lane",
        "game_surface",
        "promotion_boundary",
    }
)

DECISION_INPUTS: dict[str, dict[str, object]] = {
    "asset_issue_burn_policy": {
        "source_symbols": {
            TYPES_PATH: (
                "AssetPolicyV1",
                "M6PromotionSubjectV1",
                "validate_economic_state_v1",
            ),
        },
        "observed_research_behavior": (
            "AssetPolicyV1 names asset, issue authority, burn authority, custody domain, and terminal drain without selecting their values.",
            "M6PromotionSubjectV1 binds a managed-asset-policy root rather than embedding a launch policy.",
            "The V1 state validator rejects non-zUSD supply without a mounted issuance kernel and reconciles zUSD supply, debt, balances, and pending withdrawals.",
        ),
        "game_surface": {
            "players": ("issuer", "burner", "asset holder", "custody adapter", "governance operator"),
            "actions": ("issue", "burn", "credit", "debit", "migrate", "terminal drain"),
            "information_sets": ("selected asset policy", "ledger supply", "custody claims", "external finality evidence"),
            "timing": "genesis, every value transition, authority rotation, and terminal migration",
            "authoritative_state": "per-asset supply, balances, custody, reserves, escrows, and claims",
            "loss_surface": "unauthorized issuance, supply underflow, unbacked custody claims, or stranded terminal balances",
        },
        "attack_query": "Can any caller create or destroy one atom, reset a supply floor, or strand custody without the one selected authority and terminal owner?",
        "bounded_model": {
            "integer_variables": ("amount_atoms", "supply_atoms", "custody_atoms", "claim_atoms"),
            "bounds": "integer widths, asset scales, and supply ceilings remain unselected",
            "assumptions": ("one issue authority and one burn authority per managed asset", "all value deltas reconcile by asset"),
            "exclusions": ("no launch asset list", "no inferred decimals", "no inferred genesis allocation"),
        },
        "evidence_lane": ("per-asset differential oracle", "stateful issue/burn histories", "Lean conservation", "mounted no-bypass audit"),
        "promotion_boundary": "These source types identify required policy fields. They do not authorize an asset, issuer, burner, scale, or supply floor.",
    },
    "spot_lp_fee_dust_withdrawal_policy": {
        "source_symbols": {
            TRANSITION_PATH: ("_apply_spot_swap", "_apply_lp_add", "_apply_lp_remove"),
        },
        "observed_research_behavior": (
            "The V1 spot handler checks a constant-product integer-floor output for the caller-supplied input and output amounts.",
            "The optional fee amount is caller-supplied and credited to the protocol; no fee-rate profile selects it.",
            "LP mint and burn use an explicitly documented one-share-per-atom placeholder because the complete pool-share pricing policy is absent.",
        ),
        "game_surface": {
            "players": ("trader", "liquidity provider", "fee beneficiary", "pool", "rounding owner"),
            "actions": ("swap", "add liquidity", "remove liquidity", "collect fee", "drain final pool"),
            "information_sets": ("pre-trade reserves", "declared amounts", "fee policy", "LP supply", "rounding residue"),
            "timing": "quote, admission, atomic reserve update, LP exit, and final-pool drain",
            "authoritative_state": "pool reserves, user balances, LP shares, fee buckets, and dust",
            "loss_surface": "fee evasion, reserve extraction, dilution, rounding capture, or unreachable final reserves",
        },
        "attack_query": "Can a trader or LP choose fee, output, share ratio, ordering, or dust disposition to extract value or leave an unowned remainder?",
        "bounded_model": {
            "integer_variables": ("reserve_in", "reserve_out", "amount_in", "amount_out", "fee_atoms", "lp_share_atoms", "dust_atoms"),
            "bounds": "fee rates, minimum liquidity, reserve ceilings, and dust thresholds remain unselected",
            "assumptions": ("integer floor arithmetic", "atomic reserve and balance updates"),
            "exclusions": ("the V1 one-to-one LP placeholder is not a launch recommendation", "no inferred fee beneficiary"),
        },
        "evidence_lane": ("independent AMM arithmetic oracle", "boundary-value reserve vectors", "stateful LP entry/exit", "terminal-drain mutation tests"),
        "promotion_boundary": "The observed arithmetic is a research implementation input. Exact fees, LP math, dust ownership, and withdrawal rules require an approved profile.",
    },
    "zusd_monetary_lifecycle_policy": {
        "source_symbols": {
            TYPES_PATH: ("validate_economic_state_v1",),
            TRANSITION_PATH: (
                "_apply_zusd_borrow",
                "_apply_zusd_repay",
                "_apply_zusd_redeem",
                "_apply_zusd_liquidate",
                "_apply_stability_deposit",
                "_apply_stability_withdraw",
                "_apply_zusd_redistribute",
            ),
        },
        "observed_research_behavior": (
            "Borrowing uses amount_atoms <= collateral_atoms as a conservative placeholder because the oracle and minimum-collateral-ratio policy is absent.",
            "Mint, repay, redeem, and liquidation update zUSD supply and debt with exact integer deltas and no selected fee schedule.",
            "Stability Pool deposits and withdrawals use one-to-one claim atoms without selected gain, loss, offset, or terminal distribution rules.",
        ),
        "game_surface": {
            "players": ("borrower", "redeemer", "liquidator", "stability provider", "fee beneficiary", "bad-debt owner"),
            "actions": ("borrow", "repay", "redeem", "liquidate", "offset", "redistribute", "withdraw"),
            "information_sets": ("collateral", "debt", "oracle occurrence", "fees", "pool claims", "system mode"),
            "timing": "vault creation, risk change, oracle update, liquidation, redistribution, recovery, and terminal drain",
            "authoritative_state": "zUSD supply, vault debt, collateral custody, Stability Pool claims, reserves, and protocol liabilities",
            "loss_surface": "unbacked minting, stale-price liquidation, fee leakage, bad-debt orphaning, or Stability Pool claim loss",
        },
        "attack_query": "Can any vault or liquidation sequence create zUSD without matched debt and backing, use stale risk data, or shift loss to an unnamed owner?",
        "bounded_model": {
            "integer_variables": ("collateral_atoms", "debt_atoms", "zusd_supply_atoms", "fee_atoms", "pool_claim_atoms", "bad_debt_atoms"),
            "bounds": "collateral ratios, fees, redemption limits, liquidation thresholds, and recovery parameters remain unselected",
            "assumptions": ("zUSD mint and burn stay inside the monetary kernel", "supply and debt reconcile after every accepted command"),
            "exclusions": ("emergency zUSD shutdown", "the placeholder collateral comparison is not launch MCR policy"),
        },
        "evidence_lane": ("independent Liquity-style accounting oracle", "stateful vault and Stability Pool histories", "Lean liability conservation", "oracle-gated liquidation tests"),
        "promotion_boundary": "The V1 handlers expose lifecycle and accounting obligations. They do not select collateral, fee, redemption, liquidation, redistribution, or Stability Pool economics.",
    },
    "oracle_lifecycle_policy": {
        "source_symbols": {
            TYPES_PATH: ("FreshnessBoundsV1", "OracleContextV1"),
            TRANSITION_PATH: ("_apply_oracle_submit", "_apply_oracle_dispute"),
        },
        "observed_research_behavior": (
            "Oracle submission escrows a caller-supplied zUSD bond and replaces one stored integer price.",
            "Oracle dispute always returns UNSUPPORTED_OPERATION because observation, bond ownership, deadline, and outcome policy are absent.",
            "The execution context carries freshness bounds and oracle heights, while the business handler does not select reporter admission or aggregation semantics.",
        ),
        "game_surface": {
            "players": ("reporter", "disputer", "aggregator", "price consumer", "bond beneficiary", "recovery operator"),
            "actions": ("submit", "aggregate", "dispute", "finalize", "mark stale", "recover"),
            "information_sets": ("source reports", "occurrence order", "bonds", "freshness", "consumer action class", "outage state"),
            "timing": "report occurrence, dispute window, aggregation, consumption, outage, and recovery",
            "authoritative_state": "admitted reports, bonds, disputes, aggregate price, occurrence identity, and freshness context",
            "loss_surface": "manipulated or stale risk increase, bond theft, split-brain aggregates, or unsafe outage recovery",
        },
        "attack_query": "Can reporters or consumers reorder, replay, censor, dispute, or age observations to authorize a profitable stale or manipulated transition?",
        "bounded_model": {
            "integer_variables": ("price_e8", "bond_atoms", "observed_height", "oracle_height", "age_blocks", "reporter_count"),
            "bounds": "reporter set, quorum, dispute window, aggregation rule, freshness thresholds, and recovery delay remain unselected",
            "assumptions": ("risk-increasing commands require an admitted fresh occurrence", "report and dispute identities are replay scoped"),
            "exclusions": ("a stored latest price alone is not an aggregation policy", "no inferred fallback price"),
        },
        "evidence_lane": ("occurrence-stream model", "oracle manipulation game", "ESSO outage/recovery", "differential aggregation oracle", "consumer freshness mutation tests"),
        "promotion_boundary": "The source records a bounded placeholder lifecycle. Reporter, dispute, aggregation, freshness, outage, and recovery authority remain unselected.",
    },
    "perps_risk_and_terminal_policy": {
        "source_symbols": {
            TRANSITION_PATH: ("_apply_perp_open", "_apply_perp_close", "_apply_perp_funding", "_apply_perp_liquidate"),
        },
        "observed_research_behavior": (
            "Perp open accepts a caller-supplied entry price and moves zUSD margin without a selected initial-margin rule.",
            "Perp close permits only zero PnL because exit-price and oracle policy are absent.",
            "Funding is a simple transfer and liquidation consumes the sender's position while allocating a caller-supplied insurance amount; full liquidation and bad-debt policy are absent.",
        ),
        "game_surface": {
            "players": ("trader", "counterparty pool", "liquidator", "funding payer", "insurance owner", "bad-debt owner"),
            "actions": ("open", "fund", "reduce", "close", "liquidate", "insure", "terminal settle"),
            "information_sets": ("position", "margin", "entry and mark occurrence", "funding epoch", "insurance", "market mode"),
            "timing": "open, funding occurrence, risk update, partial or full liquidation, recovery, and terminal close",
            "authoritative_state": "positions, entry prices, margin, PnL, funding, insurance, and bad debt",
            "loss_surface": "caller-authored PnL, under-margin opening, stale liquidation, insurance overdraw, or orphaned bad debt",
        },
        "attack_query": "Can a trader or liquidator choose price, PnL, funding, margin, insurance, or close order to externalize a liability or bypass oracle gating?",
        "bounded_model": {
            "integer_variables": ("size_atoms", "margin_atoms", "price_e8", "pnl_atoms", "funding_atoms", "insurance_atoms", "bad_debt_atoms"),
            "bounds": "market list, leverage, margin ratios, funding clamp, liquidation penalty, insurance cap, and terminal limits remain unselected",
            "assumptions": ("integer settlement", "every closed position drains margin and liabilities"),
            "exclusions": ("zero-PnL close is a fail-closed research subset", "caller-supplied entry price is not oracle admission"),
        },
        "evidence_lane": ("independent perps accounting oracle", "stateful funding/liquidation histories", "oracle manipulation sweep", "insurance and bad-debt conservation proof"),
        "promotion_boundary": "The current handlers demonstrate a restricted lifecycle. They do not select production markets, margin, funding, liquidation, insurance, or terminal settlement.",
    },
    "protocol_buy_burn_policy": {
        "source_symbols": {TRANSITION_PATH: ("_apply_protocol_buy_and_burn",)},
        "observed_research_behavior": (
            "Protocol buy-and-burn always returns UNSUPPORTED_OPERATION.",
            "The source names missing protocol-asset identity, purchase evidence, and owning burn kernel as authority blockers.",
        ),
        "game_surface": {
            "players": ("treasury", "route or auction", "protocol-token holder", "burn authority", "reserve beneficiary"),
            "actions": ("fund budget", "purchase", "apply price guard", "custody acquired tokens", "burn", "recover"),
            "information_sets": ("budget", "route liquidity", "oracle occurrence", "circulating supply", "protected floor", "reserve state"),
            "timing": "budget activation, execution window, acquisition finality, burn, failure recovery, and reserve termination",
            "authoritative_state": "buyback reserve, acquired-token custody, protocol-token supply, burn receipt, and residual budget",
            "loss_surface": "treasury extraction, manipulated purchase, floor violation, fake burn, or stranded reserve",
        },
        "attack_query": "Can an operator redirect budget, trade against a manipulated route, claim an unproven purchase, or burn below the protected supply floor?",
        "bounded_model": {
            "integer_variables": ("budget_atoms", "acquired_atoms", "burn_atoms", "price_e8", "supply_atoms", "floor_atoms"),
            "bounds": "funding source, route, guard, budget, cadence, and floor remain unselected",
            "assumptions": ("purchase and burn are one governed lifecycle", "burn authority is unique"),
            "exclusions": ("no implicit treasury ownership", "no fallback route", "no inferred token floor"),
        },
        "evidence_lane": ("treasury conservation oracle", "price-manipulation scenarios", "burn-supply proof", "route and custody replay tests"),
        "promotion_boundary": "The command remains unreachable in the research subset. No buyback funding, route, token, price guard, floor, or burn authority is selected.",
    },
    "proof_reward_reserve_policy": {
        "source_symbols": {TRANSITION_PATH: ("_apply_prover_reward",)},
        "observed_research_behavior": (
            "The V1 handler transfers a caller-specified asset and amount from the protocol reserve to a named prover reward atom.",
            "The handler does not select proof eligibility, schedule, cap, claim identity, nullifier scope, or exhaustion behavior.",
        ),
        "game_surface": {
            "players": ("prover", "proof verifier", "reward reserve owner", "claimant", "governance operator"),
            "actions": ("prove", "verify eligibility", "claim", "consume nullifier", "exhaust or drain reserve"),
            "information_sets": ("verified proof identity", "release profile", "schedule", "remaining reserve", "prior claims"),
            "timing": "proof verification, claim admission, atomic reserve debit, replay, exhaustion, and terminal drain",
            "authoritative_state": "reward reserve, verified proof identity, claim amount, claimant, nullifier, and terminal reserve owner",
            "loss_surface": "self-award, duplicate claim, proof substitution, reserve overdraw, or stranded remainder",
        },
        "attack_query": "Can a caller name itself or another prover, replay a proof, substitute a release, choose an amount, or race exhaustion to overdraw the reserve?",
        "bounded_model": {
            "integer_variables": ("reserve_atoms", "reward_atoms", "claim_count", "proof_work_units"),
            "bounds": "funding, eligibility, schedule, cap, and exhaustion thresholds remain unselected",
            "assumptions": ("only a release-selected verifier can establish proof eligibility", "each claim consumes one scoped nullifier"),
            "exclusions": ("proof mining has no fork-choice or settlement authority", "the V1 direct transfer is not a reward schedule"),
        },
        "evidence_lane": ("proof-substitution negatives", "nullifier replay histories", "reserve conservation oracle", "exhaustion boundary tests"),
        "promotion_boundary": "The source exposes reserve accounting only. Eligibility, reward amount, schedule, claimant identity, nullifier, and exhaustion policy remain unselected.",
    },
    "sealed_bid_inventory_and_lifecycle_policy": {
        "source_symbols": {
            TRANSITION_PATH: (
                "_apply_seller_auction_commit",
                "_apply_seller_auction_settle",
                "_apply_seller_auction_expire",
                "_apply_private_swap_commit",
                "_apply_private_swap_settle",
                "_apply_private_swap_expire",
            ),
        },
        "observed_research_behavior": (
            "Both seller-auction and two-party private-swap research lifecycles implement commit, reveal, settle, cancel, and expire phases with integer heights.",
            "Seller settlement derives a uniform clearing price, uses deterministic pro-rata remainder ordering, refunds revealed bonds, and slashes non-reveals.",
            "Seller inventory must already exist under an auction-derived ledger owner, while the command language does not select its deposit authority or fee owner.",
            "Private settlement requires exactly two reciprocal full-amount reveals and refunds both bonds after atomic balance exchange.",
        ),
        "game_surface": {
            "players": ("seller", "bidder", "private trader", "settlement operator", "bond beneficiary", "inventory custodian"),
            "actions": ("fund inventory", "commit", "reveal", "cancel", "expire", "settle", "refund", "slash"),
            "information_sets": ("commitments", "reveals", "deadlines", "inventory", "bonds", "tie order", "clearing data"),
            "timing": "inventory funding, commit height, reveal window, settlement window, cancellation, and expiry",
            "authoritative_state": "inventory custody, bond escrows, commitments, reveals, fills, payments, rounding, refunds, and slashes",
            "loss_surface": "unfunded inventory, reveal theft, ordering manipulation, ambiguous cancellation, bond misallocation, or incomplete terminal drain",
        },
        "attack_query": "Can a bidder, seller, operator, or observer exploit ordering, partial information, deadlines, ties, cancellation, or inventory custody to extract or strand value?",
        "bounded_model": {
            "integer_variables": ("bond_atoms", "quantity_atoms", "price_e8", "inventory_atoms", "payment_atoms", "rounding_remainder_e8", "height"),
            "bounds": "asset list, bond schedule, fees, phase lengths, inventory authority, lot rules, and terminal thresholds remain unselected",
            "assumptions": ("commitments are domain separated", "canonical ordering resolves equal remainders"),
            "exclusions": ("existing auction-custody balances do not prove funded inventory ingress", "no inferred fee or slash beneficiary"),
        },
        "evidence_lane": ("stateful commit/reveal grammar fuzzing", "independent apportionment oracle", "deadline BVA", "escrow terminal-drain mutations", "metadata side-channel review"),
        "promotion_boundary": "The bounded workflows are research inputs. Inventory ingress, fees, bonds, deadlines, cancellation, privacy, and terminal ownership require an approved profile.",
    },
    "tau_escrow_outage_rejoin_policy": {
        "source_symbols": {
            TYPES_PATH: ("TauFinalityBoundDepositWitnessV1", "WithdrawalAcknowledgmentV1", "MigrationAuthorityProofV1"),
            TRANSITION_PATH: (
                "_apply_tau_escrow_deposit",
                "_apply_tau_withdrawal",
                "_apply_tau_withdrawal_ack",
                "_apply_fallback_activate",
                "_apply_tau_rejoin",
            ),
        },
        "observed_research_behavior": (
            "Tau deposit requires typed authority evidence matching transaction, finality, profile, beneficiary, asset, amount, and optional height.",
            "Withdrawal atomically debits an internal balance, creates a liability and outbox effect, and later acknowledgment removes the liability using typed receipt evidence.",
            "Fallback and rejoin require typed migration evidence, exact checkpoints, compatible profile roots, and authority-epoch changes.",
            "The transition does not select outage timing, retry cadence, destination idempotency implementation, or stale-profile rotation policy.",
        ),
        "game_surface": {
            "players": ("Tau depositor", "withdrawer", "relayer", "destination adapter", "validator", "recovery operator"),
            "actions": ("deposit", "request withdrawal", "deliver", "acknowledge", "retry", "enter fallback", "rejoin"),
            "information_sets": ("Tau finality", "profile root", "ledger head", "outbox identity", "destination receipt", "outage checkpoint"),
            "timing": "external finality, internal credit, withdrawal commit, delivery attempts, acknowledgment, outage, catch-up, and rejoin",
            "authoritative_state": "Tau escrow claim, internal balance, withdrawal liability, outbox, acknowledgment, migration phase, and authority epoch",
            "loss_surface": "double deposit, double withdrawal, false acknowledgment, lost retry, stale-profile rejoin, or Tau-driven ledger reorganization",
        },
        "attack_query": "Can a relayer, destination, stale Tau profile, or recovery operator replay evidence, acknowledge undelivered value, bypass the outbox ancestor, or replace ZenoLedger finality?",
        "bounded_model": {
            "integer_variables": ("amount_atoms", "tau_finality_height", "tau_receipt_height", "authority_epoch", "retry_count"),
            "bounds": "finality depth, freshness, retry budget, outage trigger, rejoin delay, and profile-rotation window remain unselected",
            "assumptions": ("ZenoLedger remains sovereign economic truth", "acknowledgment is a later core transition", "destination delivery is idempotent"),
            "exclusions": ("Tau evidence cannot select the ZenoLedger head", "no inferred timeout refund", "no inferred stale-profile fallback"),
        },
        "evidence_lane": ("outage/rejoin ESSO model", "deposit and acknowledgment replay histories", "destination idempotency fault tests", "authority-epoch migration tests", "no-bypass audit"),
        "promotion_boundary": "The source supplies typed research transitions. Deposit finality, retry, outage, acknowledgment, destination, and rejoin policy remain unselected.",
    },
}
