# ZDEX Volume, Holding, and Hyperdeflation Mechanism Report V1

Status: `RESEARCH_ONLY_ADVISORY`

Reviewed subject: `54882837b6bc1a215da66706fa10ae283607e80f`

Review date: `2026-08-16`

This report refines the unselected incentive candidates in
`PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json`. It changes no selected
economic parameter, grants no mint or distribution authority, and cannot
activate a participant payment, buyback, vesting change, writer, or release.

## Decision

The strongest candidate is a source-lineaged, fully reserved
**Contribution-Locked Burn Flywheel (CLBF)**:

1. Give every finalized protocol-fee lot one immutable, single-use source ID.
2. Preserve all third-party property and pay or reserve accrued liabilities,
   safety requirements, participant compensation, and capped operations first.
3. Allow a small bounded portion of the remaining surplus to reserve delayed,
   nontransferable future-fee credits for users who continuously lock ZDEX.
4. Assign the rest of the eligible surplus to guarded buy-and-burn.
5. Make credits mature later, expire, and remain unusable for cash or ZDEX.
6. Return expired credit reserves to named buyback carry.
7. Make address splitting unable to increase aggregate credits.
8. Give raw volume, transaction count, wallet count, and passive ownership zero
   reward weight.

The proposed `beta` range assigns 80% to 95% of pre-growth surplus to
buy-and-burn; its hard research ceiling still assigns at least 75%. Every range
in this report remains `UNSELECTED`.

Guarded burn-indexed insider vesting remains a later optional candidate. It is
harder to secure because beneficial ownership, hedges, external positions, and
the value of early liquidity are only partially observable.

## Game Surface

### Players

- traders and repeat users;
- LPs and Stability Pool depositors;
- oracle reporters, aggregators, disputers, and watchers;
- validators, provers, keepers, liquidators, solvers, and route builders;
- web, API, static-mirror, and Tau-facing hosts;
- relayers and destination operators;
- security, legal, operations, and core contributors;
- treasury and program administrators;
- genesis recipients, founders, team members, and other locked holders;
- ZDEX holders with external spot, lending, option, or perpetual positions;
- buyback counterparties and ordering actors;
- coalitions controlling several nominally separate roles.

### Actions

- trade, self-trade, cycle through related accounts, or route through a related
  LP, solver, host, or keeper;
- provide liquidity, executable quotes, reporting, proof, validation, hosting,
  or other services;
- create, lock, transfer, wrap, hedge, claim, redeem, expire, or forfeit a
  reward;
- fund a program, classify a fee lot, execute a buyback, or sell into it;
- influence an oracle, benchmark, route, batch boundary, baseline, expense
  epoch, or vesting input;
- take an external position that profits from induced ZDEX price movement.

### Information and observability

ZenoLedger can observe finalized fees, commands, locks, service receipts,
canonical benchmarks, buyback outputs, burns, claims, and declared lot lineage.

It generally cannot establish:

- real-world beneficial ownership;
- off-ledger side payments;
- centralized-exchange or cross-chain positions;
- every economically related trader, LP, host, solver, and keeper;
- whether locked exposure was hedged;
- all external profit from manipulating ZDEX or an oracle.

Address uniqueness therefore provides no sufficient anti-manipulation premise.
DEX wash trading can use self-trades, two-account cycles, or longer cycles.

### Timing

The safe order is:

```text
finalize economic activity
-> accrue property, liabilities, reserves, services, and operations
-> verify service receipts
-> close selected dispute and reversal windows
-> compute finalized per-asset net surplus
-> assign each source lot exactly once
-> reserve any admitted delayed credits
-> execute a bounded buyback
-> burn exactly the acquired ZDEX
-> mature delayed credits or vesting effects in later transitions
```

Same-epoch fee generation, buyback, and vesting acceleration are excluded from
this candidate.

## Attack Query

For any economically controlled coalition `C`, define:

```text
profit_C =
    cash_rewards
  + present_value(fee_credits)
  + value(accelerated_liquidity)
  + recaptured_lp_host_solver_keeper_payments
  + oracle_derivative_price_impact_external_gains
  + treasury_subsidy
  - irreversible_protocol_fees
  - nonrecaptured_lp_fees
  - slippage_gas_adverse_selection_capital_cost
  - forfeitures
  - expected_slashing
```

The bounded refutation query is:

```text
exists admissible coalition actions such that profit_C > 0
```

Every solver result must state which external-gain terms are bounded. A model
covering fee rewards alone cannot establish safety against oracle, perpetual,
or external-market manipulation.

## Bounded Model

### Per-asset priority waterfall

Cross-asset sums require an exact release-selected conversion receipt. All
third-party property is reconciled separately and never enters a discretionary
revenue pool:

```text
P0[a,e] =
    exact user and LP property
  + accrued third-party entitlements
  + refundable service bonds
  + backstop and market-maker risk principal

for each typed source lot l:
  amount[l] = sum(assigned[l,d] for d in allowed_destinations[l])
  assigned[l,d] > 0 implies d in allowed_destinations[l]
  consumed[l] implies no later assignment from l
```

where:

```text
P0 = separately conserved third-party property and accrued liabilities
P1 = selected solvency, insurance, and safety requirements
P2 = prefunded participant and service compensation
P3 = capped operations, security, legal, and hosting expenses
G  = capped growth-incentive reserve
X  = guarded buyback allocation
C  = named carry
```

The allowed destinations are closed by lot type:

```text
user_or_lp_property -> P0 until authenticated settlement or refund
refundable_service_bond -> P0 until return or admitted slash
backstop_risk_principal -> P0 until withdrawal or contractual loss allocation
market_maker_liquidity -> P0 custody through trade accounting and withdrawal
service_prefund -> its named P2 service or same-source refund/carry only
operations_prefund -> its named P3 purpose or same-source refund/carry only
slashing_proceeds -> selected victim, safety reserve, or slash carry only
credit_reserve -> redemption, then expiry into buyback carry only
buyback_carry -> guarded X execution or buyback carry only
genesis_lot -> selected genesis recipient or genesis carry only
unrestricted_protocol_revenue -> admitted P1, P2, P3, G, X, or revenue carry
```

Stability Pool principal, LP principal, LP-owned fees, backstop and market-maker
risk capital, service bonds, and already accrued entitlements remain in `P0`.
Only the exact portion consumed by an admitted slash may become typed slashing
proceeds. `P2` includes separately selected program rewards for Stability Pool
depositors plus selected compensation for oracle participants, validators,
provers, keepers, liquidators, solvers, relayers, and other enabled services.
Every service budget must be funded before eligible work begins.

Let `R` contain only finalized protocol-revenue lots whose selected policy
allows the listed destinations. Purpose-bound prefunding, third-party property,
slashing proceeds, credit reserves, genesis lots, and buyback carry are excluded
from `R`:

```text
require P0 is exactly reconciled in its own custody accounts
require allocations_from_R_to(P1 + P2 + P3) <= R
pre_growth_surplus = R - allocations_from_R_to(P1 + P2 + P3)
0 <= G <= floor(beta * pre_growth_surplus)
eligible_surplus = pre_growth_surplus - G
X = eligible_surplus
```

Unsafe or incomplete buyback execution moves `X` to a named buyback carry
account. It does not become treasury property.

No global balance makes restricted lots fungible. A released or expired credit
reserve is tagged as non-external value and cannot fund another incentive.

### Hosting compensation

A web interface, API, static mirror, or Tau-facing host is a service provider.
Hosting neither selects the ZenoLedger head nor receives settlement, mint,
oracle, custody, or publication authority.

Three compatible funding lanes are available for later selection:

1. A reference interface may be procured from a capped `P3` operations budget
   against authenticated availability, integrity, support, and release receipts.
2. An independent interface may charge its own separately quoted and clearly
   disclosed interface fee. The fee must remain distinct from protocol and LP
   fees, and the signed order must bind the exact amount.
3. Community or self-hosted mirrors may operate without protocol compensation.

The recommended launch baseline is a capped reference-interface budget plus
permissionless alternative hosts. A host-specific fee can be added as an
explicit opt-in policy. Host compensation must not depend on self-reported raw
volume.

For comparison, Uniswap documents an open interface that can be hosted through
IPFS and community gateways. Its support page states that Uniswap Labs' own
interface fee has been 0% since 2025-12-27. The published UNIfication design
proposed treasury funding for growth and development alongside protocol-fee UNI
burns. ZenoDEX can separate these same functions while binding every payment to
an exact owner and receipt.

### Participant funding crosswalk

This crosswalk covers the exact 22-row G1 registry. It classifies ownership and
the candidate accounting route. Amounts, assets, caps, claimant credentials,
and release roots remain unselected.

| Registry participant | Route | Named source | Accrual and claimant witness | Exhaustion rule | Terminal path |
|---|---|---|---|---|---|
| `spot_trader_and_order_user` | P0 | user balance or order escrow | accepted trade/order plus authenticated owner | entitlement persists; reject is no-op | fill, cancel, or refund to user |
| `liquidity_provider` | P0 | pool custody and LP-owned fee lots | position/share witness | claim persists | withdrawal, fee claim, named dust |
| `zusd_borrower_and_redeemer` | P0 | collateral, debt, and redemption custody | accepted monetary transition plus owner | claim/debt persists | repay, redeem, close, or collateral return |
| `stability_pool_depositor` | P0; optional P2 | pool principal and accrued liquidation lots; separate reward prefund | share and liquidation receipt | reward program disables if unfunded | withdraw principal, claim entitlement, reward carry |
| `liquidator_and_keeper` | P0 bond; P2 compensation | refundable bond custody and named liquidation/keeper budget | finalized successful service plus claimant capability | no reward beyond budget | bond return, payout, admitted slash, or service carry |
| `oracle_reporter_aggregator_disputer_and_watcher` | P0 bond; P2 compensation | refundable oracle bond custody and named role budgets | admitted report/dispute/service receipt plus registry witness | affected oracle role disables if unfunded | bond return, payout, admitted slash beneficiary, or carry |
| `perps_trader_and_funding_counterparty` | P0 | margin, PnL, and funding custody | accepted position transition plus owner | entitlement persists | close, liquidation reconciliation, or claim |
| `insurance_and_bad_debt_backstop` | P0 provider principal; P1 protocol reserve; optional P2 | provider risk-principal custody, protocol-owned insurance reserve, and named service budget | admitted contribution/service plus claimant witness | incentive disables if unfunded | provider withdrawal/loss allocation, payout, slash, or carry |
| `sealed_bid_seller` | P0 | seller escrow and auction proceeds | lifecycle state plus seller owner | escrow persists through valid lifecycle | settle, cancel, expire, or refund |
| `sealed_bid_bidder_and_private_swap_party` | P0 | bid/swap escrow | commitment/reveal/lifecycle plus owner | escrow persists | settle, cancel, expire, or refund |
| `tau_depositor_and_withdrawer` | P0 | Tau escrow custody | authenticated ingress/withdrawal evidence plus owner | withdrawal remains pending during outage | acknowledgment, release, fallback, or refund |
| `tau_relayer_and_destination_operator` | P0 bond; P2 or P3 compensation | refundable bond custody and named relayer/operator prefund | authenticated delivery/acknowledgment receipt plus registry capability | affected service disables if unfunded | bond return, payout, retry, admitted slash, or carry |
| `proof_prover_and_proof_miner` | P0 bond; P2 compensation | refundable proof bond custody and named proof-reward reserve | release-selected proof admission plus claimant/nullifier | reward lane disables or direct execution continues | bond return, payout, admitted slash, expiry, or carry |
| `validator_finality_operator` | P0 bond; P2 or P3 compensation | refundable validator bond custody and named operations budget | registry membership plus valid finalized participation receipt | validator profile cannot activate without funded operations | bond return, payout, replacement, admitted slash, or carry |
| `solver_batcher_and_sequencer` | P0 bond; user-granted improvement or P2 | refundable solver bond, verified output improvement, or named budget | accepted execution receipt plus selected solver identity | zero reward when improvement/budget is absent | bond return, user remainder, solver payout, admitted slash, or carry |
| `interface_api_and_static_host` | P0 bond; P3, P2, or opt-in interface fee | refundable service bond, named host budget, or signed user fee quote | release, integrity, availability, or signed-order receipt plus host ID | canonical paid service disables if unfunded | bond return, payout, refund, admitted slash, carry, or independent operation |
| `security_auditor_and_bounty_researcher` | P3 or P2 | named audit/bounty budget | accepted deliverable or vulnerability receipt plus claimant | no paid work/reward beyond budget | payout, rejection, disclosure close, or carry |
| `core_contributor_contractor_and_operations_provider` | P3 or P2 | named contract/operations budget | accepted milestone/service receipt plus claimant | no authorized paid work beyond budget | payout, refund, termination, or carry |
| `liquidity_bootstrapper_and_market_maker` | P0 liquidity/bond; P2 or selected distribution | provider liquidity and bond custody, named depth budget, or separately selected genesis program | executable-depth receipt and bonded provider | program disables if unfunded | principal/bond return, payout, admitted slash, taper, expiry, or carry |
| `community_testnet_and_usage_award_recipient` | G or selected genesis program | named prefund or selected genesis lot | counsel-approved snapshot/receipt plus claimant/nullifier | disabled while unselected or exhausted | claim, expiry, unclaimed disposition, or carry |
| `founder_team_partner_and_capital_recipient` | genesis only | selected genesis lot | release root, beneficiary, cliff, and vesting witness | mint/transfer disabled while unselected | vest, forfeit, revoke where legal, or unclaimed disposition |
| `protocol_treasury_reserve_and_buyburn_executor` | P1, X, or typed C | named reserve, eligible revenue, or matching carry | opaque release capability plus current-head execution receipt | fail closed and retain same-type carry | reserve custody, exact burn, refund, or carry |

Every row still requires the 14 selection fields in the partial-policy artifact.
The table supplies no amount, payment, claimant, legal, settlement, or release
authority.

Any third-party bond or risk principal used by any row remains `P0` property
until its refund, loss-allocation, or admitted-slash transition. A service
budget, protocol-owned reserve, and participant-owned bond require distinct
custody lots even when one actor is associated with all three.

### Contribution-Locked Burn Flywheel

For finalized protocol-fee lot `l`:

```text
G_l <= floor(beta * pre_growth_surplus_l)
burn_allocation_l = pre_growth_surplus_l - G_l
```

For user `i`, a credit may be created only from irreversible cash protocol
fees:

```text
credit_created_i <= floor(alpha * irreversible_cash_protocol_fee_i)
credit_created_i <= available_named_credit_reserve
```

At a later eligible transaction:

```text
credit_redeemed_i <= min(
    matured_credit_balance_i,
    floor(rho * current_gross_protocol_fee_i),
    remaining_named_credit_reserve
)

current_cash_protocol_fee_i =
    current_gross_protocol_fee_i - credit_redeemed_i

credit_reserve_after_i =
    credit_reserve_before_i - credit_redeemed_i

current_fee_settlement_funding_i =
    current_cash_protocol_fee_i + credit_redeemed_i
  = current_gross_protocol_fee_i
```

The reserve debit discharges a previously recorded liability. It is tagged as
non-external value, cannot create a new credit, and cannot count as organic
revenue or activity. The proof is per asset; cross-asset redemption is forbidden
without a selected exact conversion receipt.

Required construction rules:

- credits are nontransferable;
- credits cannot be redeemed for cash or ZDEX;
- there is no fixed per-address award;
- credit creation is linear in irreversible protocol fees;
- maturity and expiry are fixed by consensus height or epoch;
- ZDEX remains continuously locked from earning through maturity;
- early unlock cancels pending credits;
- the reserve is an exact liability;
- a fee lot cannot fund another reward program;
- oracle failure disables new credit creation when lock-value conversion is
  required.

A stronger lock requirement is:

```text
conservative_lock_value_i >= m * outstanding_credit_i
```

The conversion uses a release-selected long-window conservative lower price.

For a coalition starting and ending with no credit balance:

```text
sum(credit_redemptions)
  <= sum(credits_created)
  <= alpha * sum(irreversible_cash_protocol_fees)
```

Therefore, inside the declared model:

```text
wash_profit
  <= -(1 - alpha) * sum(irreversible_cash_protocol_fees)
     - trading_drag
  <= 0
```

Sybil splitting preserves the sum because the rule is linear and has no
per-identity base term.

Source-lot single use alone does not close cross-program stacking. Hidden
coalition membership cannot be a runtime input. For every economic event `q`,
either benefit routes are mutually exclusive by construction or the runtime
conservatively treats every recipient as one coalition. All protocol-funded
benefits are converted to the fee asset using release-selected receipts:

```text
total_event_linked_protocol_benefit[q] =
    fee_credit_value
  + event_linked_host_or_service_payments_to_all_recipients
  + protocol_funded_solver_payments_to_all_recipients
  + vesting_acceleration_value
  + other_protocol_funded_event_benefit

total_event_linked_protocol_benefit[q]
  <= floor(kappa * finalized_external_protocol_fee[q])

0 <= kappa < 1
```

Verified solver improvement can use a separate user-granted value source only
when the runtime proves the realized net improvement and preserves the reference
output for the user after reward. Any additional protocol-funded solver benefit
remains inside the event cap. An unpriced benefit or missing conversion receipt
rejects the composed incentive. Oracle, derivative, buyback-counterparty, and
other external gains remain in the broader bounded attack query.

Proposed unselected ranges:

| Parameter | Research range | Hard research ceiling |
|---|---:|---:|
| `beta`, growth reserve share | 5% to 20% | 25% |
| `alpha`, credit earned per irreversible fee | 5% to 15% | below 100% |
| `rho`, redemption share of a future gross fee | 10% to 25% | below 100% |
| maturity | 30 to 90 days | unselected |
| expiry | 180 to 365 days | unselected |
| continuous lock class | 90, 180, or 365 days | unselected |
| lock-value multiple `m` | 2x to 10x | unselected |
| aggregate credit liability | 1% to 5% of trailing finalized revenue | unselected |

The 5% to 20% `beta` range assigns 80% to 95% of pre-growth surplus to buyback.
The 25% hard ceiling assigns 75%. Depth and impact gates can delay actual burn.
Expired reserves may later augment buyback after their liabilities close.

The arithmetic establishes an identity-independent direct farming-loss bound
over the stated payoff terms. Increased retention and long-term unhedged
exposure remain behavioral hypotheses.

### Hyperdeflation envelope

The selected G1 constants are:

```text
S0 = 2,000,000,000 * 10^18 atoms
F  =   200,000,000 * 10^18 atoms
```

The selected Zeno cap is:

```text
B_e <= floor((S_e - F) / 2)
S_(e+1) = S_e - B_e
```

Let `x_e = S_e - F`. When the cap is saturated:

```text
x_(e+1) = ceil(x_e / 2)
S_n = F + ceil((S0 - F) / 2^n)
```

Consequences:

- excess supply can contract geometrically;
- at `S = F + 1 atom`, the cap is zero;
- maximum cumulative launch-profile burn is 1,800,000,000 ZDEX minus one atom;
- the one-atom absolute floor remains unreachable while the 200-million active
  floor is selected;
- actual burns remain limited by revenue and executable acquisition capacity.

The Zeno cap is a supply invariant, not an acceptable execution-size limit. An
admitted burn must also satisfy:

```text
B_e <= min(
    acquired_ZDEX_e,
    floor((S_e - F) / 2),
    supply_rate_cap_e,
    executable_depth_cap_e,
    price_impact_cap_e
)
```

Proposed unselected execution ranges:

- 1 to 25 basis points of active supply per execution epoch;
- 5 to 50 basis points maximum measured price impact;
- a 24-hour to 7-day execution window;
- unexecuted funds remain named buyback carry.

A solver-competed or sealed batch is preferable to a large predictable market
order. The execution receipt must bind a precommitted benchmark, maximum price,
depth envelope, input budget, and finalized output. The acquired ZDEX and burned
ZDEX must be equal in the atomic transition.

Burning permanently reduces total supply. Locking temporarily reduces
protocol-observable liquid supply. Public claims must keep these quantities
separate.

### Other ranked mechanism families

#### 2. Verified execution-improvement sharing

For canonical reference output `O_ref`, realized solver output `O_j`, and
admitted output-asset costs:

```text
O_net_j = checked_sub(O_j, admitted_extra_costs)
require O_net_j >= O_ref
improvement_j = O_net_j - O_ref
solver_reward_j = floor(sigma * improvement_j)
user_output_j = O_net_j - solver_reward_j
```

Required:

```text
0 <= solver_reward_j <= improvement_j
user_output_j >= O_ref
```

The reward comes from verified user-granted execution improvement in the output
asset. It requires no ZDEX mint and consumes no burn surplus. Proposed
`sigma = 10% to 25%`, with a 33% hard research ceiling.

#### 3. Executable-depth reverse procurement

The protocol buys a declared market-quality service:

```text
service = (
  pair, two_sided_band, minimum_executable_depth, maximum_spread,
  uptime, response_latency, fill_behavior, epoch
)
```

Providers submit sealed required-subsidy bids. Payment occurs after verified
performance and cannot exceed the named prefunded budget. When bad performance
can be admitted and detected only probabilistically, the economic condition is:

```text
DefectGain_i
  <= DetectionProbability_i * SlashAmount_i + FutureValueLost_i
```

All terms use exact integers or rationals with cross-multiplied checks. When the
service receipt deterministically rejects bad performance before payment, the
admitted bad-performance payment is zero. A large bond without a detection and
slashing premise supplies no safety theorem.

Payment uses attempted-fill receipts and low-percentile executable depth rather
than average TVL or reported volume. Classical second-price truthfulness applies
only under the narrow single-parameter independent-private-cost assumptions.

#### 4. Cumulative net-surplus milestones

For selected operators or contributors, consensus state remains nonnegative.
Store cumulative revenue, cumulative recognized costs, and the prior high-water
mark as checked integers:

```text
cum_revenue_e = cum_revenue_(e-1) + finalized_external_protocol_revenue_e

cum_cost_e = cum_cost_(e-1)
  + accrued_user_liabilities_e
  + accrued_safety_requirements_e
  + accrued_service_costs_e
  + accrued_operations_e
  + refunds_e
  + reserve_topups_e

positive_cumulative_surplus_e =
  max(0, cum_revenue_e - cum_cost_e)

H_e = max(H_(e-1), positive_cumulative_surplus_e)
delta_H_e = H_e - H_(e-1)

bonus_e <= min(
  named_prefunded_bonus_budget,
  epoch_cap,
  floor(theta * delta_H_e)
)
```

A cumulative high-water mark prevents simple epoch baseline resets. Expenses
are recognized when accrued. Proposed `theta = 5% to 10%`, with a 15% hard
research ceiling and a 90 to 180-day finality lag.

#### 5. Guarded burn-indexed vesting acceleration

For finalized eligible burn `B` and delayed extra unlock `U`:

```text
U_e <= min(epoch_cap, floor(gamma * B_(e-L)))
delta_protocol_observable_liquid <= -B + U
```

If `gamma <= 1/4`:

```text
delta_protocol_observable_liquid <= -3B/4
```

The historical 25% candidate therefore preserves a local net decline inside
the paired burn-and-unlock model. A stronger later form also caps `U` by delayed
finalized net-surplus value, annual and lifetime limits, and forfeitable unvested
tokens.

Proposed later ranges:

- `gamma = 5% to 10%`, with a 25% hard ceiling;
- 90 to 180-day lag and lookback;
- 25 to 100 basis points annual cap on the subject allocation;
- 2% to 5% lifetime extra-unlock cap;
- optional permanent cancellation of 1/4 to 1 unvested atom per accelerated
  atom, implemented with exact integer rounding.

Only release-bound protocol-revenue source lots can feed this input.
Treasury-tagged, manual, same-epoch, and self-declared sources are excluded by
typed lineage. Independent batch execution and a conservative net-surplus value
cap are required.

The mathematical model assumes that a beneficiary may also supply the buyback,
hedge the lock, and receive off-ledger subsidies. Related-party declarations and
screening remain legal and operational controls; they are not the safety proof.
Delay, forfeiture, value caps, and the global coalition-profit bound must remain
safe under this adversarial ownership assumption.

This mechanism stays below CLBF because beneficial-owner opacity and external
position gains prevent a strong general manipulation claim.

## Named Failure Witnesses

### `WASH_VOLUME_MINTED_REWARD`

An attacker pays fee `f`, recaptures other fees, and receives raw-volume reward
`r`:

```text
r > irreversible_cost(f) + drag  =>  profit > 0
```

Closure: no minted, transferable, or identity-weighted raw-volume reward.

### `CROSS_PROGRAM_STACKING`

Several programs reward one event:

```text
credit_value  = 40f/100
host_reward   = 30f/100
solver_reward = 30f/100
vesting_value = 25f/100
total_benefit = 125f/100
```

Closure: one immutable fee-lot lineage and one global marginal-benefit cap.

### `BUYBACK_COUNTERPARTY_UNLOCK`

A related party sells ZDEX into the buyback and gains early vesting liquidity.

Closure: assume the buyback counterparty and vesting beneficiary are the same
economic actor. Use delay, conservative net-surplus value cap, forfeiture, and
annual/lifetime acceleration caps under that worst case. Related-party screening
is a supplementary legal and operational control with no mathematical authority.

### `CHEAP_PRICE_MORE_UNLOCK`

For fixed quote spend `X`:

```text
B approximately X / price
U approximately gamma * X / price
```

A temporary price depression increases token-denominated burn and unlock.

Closure: conservative value cap, long-window route controls, execution caps,
and delayed vesting.

### `ORACLE_PERP_DOUBLE_DIP`

A coalition profits from an external short or perpetual while inducing a
buyback, burn, unlock, or oracle move.

Closure: explicit external-position bounds, oracle/perps separation, delayed
effects, and fail-closed suspension. Fee-only bounds make no claim here.

### `RELATED_PARTY_FEE_RECAPTURE`

A trader controls an LP, host, solver, or keeper receiving other parts of the
same fee.

Closure: global coalition model and irreversible-cost accounting. Address
filters alone provide no closure.

### `TREASURY_SUBSIDY_LAUNDERING`

Treasury capital creates activity that is later labeled organic revenue.

Closure: immutable treasury-origin tags and exclusion from reward and milestone
inputs.

### `BASELINE_SUPPRESSION` and `EXPENSE_DEFERRAL`

A recipient depresses a comparison window or shifts expenses between epochs.

Closure: cumulative high-water accounting and accrual-time recognition.

### `DEPTH_QUOTE_CANCEL`

A provider posts large quotes during observations and cancels before fills.

Closure: attempted-fill receipts and low-percentile executable depth.

### `SECOND_PRICE_SHILL`

A provider controls another bid to alter payment.

Closure: no independence claim from addresses; collusion model, bidder bond,
budget cap, and fallback procurement rule.

### `MERCENARY_LIQUIDITY_CLIFF`

Depth disappears when subsidies end.

Closure: staggered epochs, bounded budgets, declining support, and explicit exit
criteria.

### `BURN_LIQUIDITY_DEATH_SPIRAL`

```text
burn and free-float decline
-> executable depth declines
-> slippage and volatility rise
-> genuine use and fee revenue fall
-> participant funding and future burn weaken
```

Closure: depth, impact, cadence, reserve, and participant-funding gates precede
burn execution.

Additional mandatory witnesses are `UNLOCK_SELL_PRESSURE`,
`CREDIT_DOUBLE_COUNT`, `CREDIT_UNFUNDED_LIABILITY`, `LOCK_WRAPPER_OR_HEDGE`,
`GENESIS_FARM_AND_DUMP`, and `LEGAL_ACTIVATION_AMBIGUITY`.

## Recommended Deployment Sequence

### Minimal launch candidate

Subject to complete G1 selection, counsel, proofs, runtime implementation, and
release gates:

1. Give every enabled participant an exact named funding source and terminal
   path.
2. Disable any service lacking a prefunded compensation source.
3. Route eligible surplus to guarded buy-and-burn.
4. Assign zero reward weight to raw volume, transaction count, wallet count,
   and passive holdings.
5. Pay solvers only from verified execution improvement when the user contract
   selects it.
6. Procure required executable depth from fixed budgets and receipt-backed
   service contracts.
7. Keep burn-indexed vesting disabled.
8. Optionally canary a very small fully reserved future-fee-credit program.
9. Keep genesis and activity-based initial distribution disabled until counsel
   and the release constitution select them.

### Ambitious later candidate

1. Activate CLBF with source-lot lineage and continuous ZDEX lock classes.
2. Procure strategic depth through receipt-backed reverse auctions.
3. Add cumulative net-surplus milestones for selected service classes.
4. Consider burn-indexed vesting only after external-position models,
   conservative value caps, delayed independent buyback execution,
   annual/lifetime limits, and global stacking proofs pass.
5. Stage mechanisms independently before composition so that causal effects and
   global benefit bounds remain identifiable.

## Evidence Lane

### Boundary-value analysis

Test at least:

- `S = F-1`, `F`, `F+1`, and `F+2`;
- burn cap minus one, exact cap, and plus one;
- zero and one-atom fees, credits, reserves, burns, and carry;
- maturity and expiry height minus one, exact, and plus one;
- high-water equality and one-atom improvement;
- minimum depth and uptime neighbors;
- bidder counts zero, one, two, and three;
- maximum-integer neighbors, multiplication overflow, division dust;
- oracle, epoch, release, and authority transitions.

### Stateful histories

- honest repeat user earning, locking, redeeming, expiring, and canceling credit;
- attacker controlling trader, LP, host, solver, and keeper;
- related-account cycles and treasury-funded activity;
- buyback front-running and related-counterparty attacks;
- oracle manipulation plus a perpetual or external position;
- depth-provider cancellation and default;
- baseline suppression and expense deferral;
- failed buyback with named carry;
- accelerated unlock followed by immediate sale;
- restart, replay, migration, and cross-epoch evidence.

### Named semantic mutants

Kill at least:

- raw-volume reward weight;
- reward equal to or above the irreversible fee;
- LP fee misclassified as protocol revenue;
- fixed per-address payment;
- concave identity cap that rewards splitting;
- missing credit reserve;
- expired reserve counted twice;
- one source lot funding two programs;
- resettable milestone baseline;
- omitted accrued expense;
- current-epoch spot price used for vesting;
- ceiling substituted for the burn cap;
- active-floor bypass;
- average rather than low-percentile depth;
- canceled quote counted as executable;
- shill second bid;
- vesting cliff bypass.

### Formal targets

Existing local artifacts supply scoped inputs only:

- `docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json`, its checker,
  and its tests bind the selected 2B/E18 supply envelope and keep all 22
  compensation rows open. They do not select CLBF or prove its economics.
- `internal/tokenomics/ZENO_BURN_INDEXED_UNLOCK_ACCELERATOR_V0.json`,
  `tools/check_burn_indexed_unlock_accelerator.py`, and
  `tests/tools/test_check_burn_indexed_unlock_accelerator.py` check a historical
  activation-disabled 25% candidate and one declared manipulation bound. They
  do not model opaque beneficial ownership, external positions, or composed
  rewards.
- `tests/core/test_perp_incentive_hazards.py` contains a concrete bounded witness
  where a naive volume reward turns an oracle-manipulation round trip profitable
  and a separate bounded rebate sweep. It is a fixed research model.
- `lean-mathlib/Proofs/RevenueSurfaceSafety.lean` proves small real-number
  fee/reward and burn/emission inequalities. It assumes its measured inputs and
  supplies no runtime, oracle, source-lot, integer-codec, or CLBF refinement.
- `lean-mathlib/Proofs/ZenoDEXSTierDisasterMath.lean` proves compact natural-
  number source, reserve-first, and payout-cap laws. It is not the proposed
  typed-lot runtime.
- `lean-mathlib/Proofs/FeeDustCarryConservation.lean` proves an exact historical
  three-bucket split and dust bound. It does not prove this waterfall or repair
  the historical unnamed 2,500 basis points.

ESSO or an equivalent state-machine lane covers source-lot lifecycle, credit
reserve and lock lifecycle, buyback carry and burn, depth procurement and
default, delayed vesting, restart, and replay.

Z3 and CVC5 both ask:

```text
exists bounded coalition strategy with profit_C > 0
```

Promotion requires agreement and `UNSAT` over the declared bounds. `UNKNOWN`,
timeout, disagreement, or an omitted payoff term fails the gate.

Lean targets:

1. active-floor preservation and burn recurrence;
2. per-asset waterfall conservation;
3. source-lot single use;
4. exact credit-reserve liability;
5. wash non-profitability under `alpha < 1`;
6. Sybil-split additivity;
7. solver reward bounded by verified improvement;
8. depth payment bounded by its named budget;
9. `U <= gamma*B` implies `delta_liquid <= -(1-gamma)*B`;
10. cumulative high-water monotonicity;
11. total event-linked protocol benefit bounded by the finalized external
    protocol fee, or mutually exclusive by construction;
12. rejected transitions are exact no-ops.

Runtime evidence compares complete state, liabilities, reserves, credits,
locks, burns, participant claims, carry, nullifiers, and outbox effects through
the real node entrypoint.

### Acceptance predicate

```text
MechanismEligible(P) =
    every payment has a named prefunded source
  && missing-budget services are disabled
  && no post-genesis mint
  && per-asset conservation holds
  && all third-party property and refundable bonds remain exact P0 custody
  && all liabilities precede surplus
  && every credit is fully reserved
  && every typed lot uses only an allowed destination
  && every source lot is single-use
  && credit-reserve discharge cannot create another incentive
  && no raw-volume or address-count weight
  && every event has mutually exclusive benefits or observable kappa < 1 cap
  && burn floor, rate, depth, and impact gates hold
  && bounded attack queries are UNSAT in Z3 and CVC5
  && required Lean theorems compile
  && runtime projection and replay pass
  && exact legal, governance, and release roots are selected
```

Canary metrics include retention, repeat cash fees, spreads, slippage,
low-percentile executable depth, finalized net surplus, participant-funding
coverage, and credit-expiry behavior. Metrics evaluate outcomes. They receive no
settlement or payout authority.

## Promotion Boundary

### Scoped mathematical conclusions

- The selected Zeno recurrence preserves the active floor and geometrically
  contracts excess supply when saturated.
- Linear fee credits below irreversible fees rule out profitable closed-loop
  direct reward farming inside the declared payoff model.
- Linear credit creation gives Sybil-split additivity.
- Enforced typed, single-use source lineage prevents direct fee-lot double
  allocation and restricted-fund fungibility.
- `U <= gamma*B` bounds the paired liquid-supply effect of burn-indexed vesting.
- A solver reward can be budget-balanced from verified execution improvement.
- Locks reduce protocol-observable liquid supply during the lock. They do not
  reduce total supply.

### Behavioral hypotheses

- delayed fee savings may improve retention;
- continuous locks may reduce readily sellable float;
- better execution and executable depth may attract organic order flow;
- buy-and-burn may influence holder expectations.

These require shadow and canary evidence.

### Open legal and governance questions

- genesis distribution and transfer activation;
- founder, team, contributor, host, and participant compensation;
- activity-linked distribution;
- vesting acceleration and forfeiture;
- fee-credit characterization;
- market-buyback conduct;
- tax, employment, securities, and market-abuse treatment by jurisdiction.

### Exact nonclaims

This report does not establish:

- legal or tax clearance;
- an approved genesis distribution;
- beneficial-owner identity;
- price appreciation, demand, retention, or genuine-volume growth;
- long-term unhedged holding by users who lock ZDEX;
- any burn schedule, burn rate, or hyperdeflation rate;
- safe buyback execution before the depth, impact, route, and runtime gates;
- adequacy of any participant, safety, operations, or hosting budget;
- an unbounded equilibrium theorem;
- safety against every external derivative position;
- truthful reverse-auction bidding outside its exact assumptions;
- oracle truth or liveness;
- production mounting, settlement authority, or release readiness.

All proposed ranges and mechanism activations remain unselected.

## References

- Victor and Weintraud, *Detecting and Quantifying Wash Trading on Decentralized
  Cryptocurrency Exchanges*: <https://arxiv.org/abs/2102.07001>
- CFTC, Coinbase matched-trading order summary:
  <https://www.cftc.gov/PressRoom/PressReleases/8369-21>
- CoW Protocol solver and surplus documentation:
  <https://github.com/cowprotocol/docs-v1/blob/main/tutorials/submit-limit-orders-via-api/general-overview.md>
- CoW Protocol CIP-38:
  <https://forum.cow.fi/t/cip-38-solver-computed-fees-rank-by-surplus/2061>
- Vickrey, *Counterspeculation, Auctions, and Competitive Sealed Tenders*:
  <https://cramton.umd.edu/market-design-papers/vickrey-counterspeculation-auctions-and-competitive-sealed-tenders.pdf>
- Uniswap interface and IPFS hosting:
  <https://blog.uniswap.org/uniswap-interface-ipfs>
- Uniswap Labs interface fee disclosure, checked 2026-08-16:
  <https://support.uniswap.org/hc/en-us/articles/20131678274957-What-are-Uniswap-Labs-fees>
- Uniswap UNIfication design:
  <https://blog.uniswap.org/unification>

## Result

- Changed: advisory mechanism study only.
- Invariant/authority impact: none; deterministic gates and the selected
  ZenoLedger publication path retain authority.
- Evidence: local source-pinned G1 policy, historical tokenomics candidates,
  bounded integer analysis, named attack witnesses, and primary external
  references.
- Commands not run for this study: no solver, Lean, ESSO, runtime, production,
  or release gate proves the proposed mechanisms.
- Residual risk: beneficial ownership, external positions, oracle truth,
  behavioral response, liquidity response, and legal classification remain
  unresolved.
- Next safest step: freeze the source-lot accounting ABI and build exact models
  for the minimal launch, CLBF, and burn-indexed-vesting variants before
  selecting any numerical parameter.
