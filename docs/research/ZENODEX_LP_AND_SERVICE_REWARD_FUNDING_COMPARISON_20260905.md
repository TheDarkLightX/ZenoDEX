# LP and service reward funding comparison

Date: 2026-09-05. Status: `RESEARCH_COMPARISON_AND_DESIGN_CANDIDATES`.
Authority: none. No allocation percentages, token rights, monetary issuance,
release activation, or investment recommendation are selected here.

The useful starting point for finite, deflationary zDEX is the existing
ZenoDEX revenue and service-budget work: ordinary fees compensate LPs and
required work; separately identified, bounded funds can buy additional
liquidity services. Governance chooses how a funded budget is allocated.
Token issuance is a different funding mechanism and is unnecessary for these
first two mechanisms. This is a design recommendation for comparison, not a
finding that a particular allocation is economically sustainable.

## 1. Game Surface

### Recovered ZenoDEX decisions and unresolved differences

The inspected local subject was HEAD
`552b4e88f9bf5474c0d9a2dd06c302acb0ea2704`, with concurrent implementation
candidates kept outside this research change. Source hashes below identify the
actual files read. Historical evidence counts in those documents were not
replayed during this comparison.

| Existing source | Reusable mechanism or constraint | Evidence boundary |
| --- | --- | --- |
| [FIRE revenue atlas](../FIRE_REVENUE_SURFACE_ATLAS.md) | Fees and captured surplus fund rewards; staking allocates funds. Direct costs precede discretionary allocations. Bootstrap subsidy is explicit. | Its fee/value measurements and bounded model results do not establish launch prices or actual market demand. |
| [Perps incentives](../derivatives/PERP_INCENTIVES_V1.md) | Pay for depth and keeper work, assume the adversary also owns LP/staking shares, cap rebates against non-recapturable revenue, preserve exact rounding. | This draft includes scoped runtime examples; it does not establish every cross-lane incentive. |
| [zDEX hyperdeflation contract](ZDEX_HYPERDEFLATION_V1_20260821.md) and [fee core](../../src/core/zdex_fee_allocation_v1.py) | Six destinations: buyback, qualified hosts, treasury, proof rewards, cover reserve, LP rebates. Unassigned value and rounding residue remain owned reserves. | Candidate percentages and host policy are expressly unapproved. An allocation does not itself implement its claimant/terminal path. |
| [Whole-value claim anchors](ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md) | Purchase zDEX through the selected Spot occurrence and burn exactly its received atoms; host compensation remains a distinct governed allocation. | These are continuity anchors inside a proposed release claim, not production qualification. |
| [Oracle budget](../ZENO_ORACLE_TOKEN_BUDGET_V1.md) | Separate query rewards, reporter/dispute bonds, slashes and fee allocations. | Budget checks do not prove report truth, operating viability or the final Oracle token policy. |
| [zUSD lifecycle](../derivatives/ZUSD_V1.md) | Borrow/redemption fees, collateral/debt ownership and Stability Pool liquidation transfers are distinct. | zUSD is explicitly not an exact Liquity clone. Borrower-interest policy cannot be inferred from Liquity V2. |
| [Treasury Rebalancer](../PROOF_BACKED_TREASURY_REBALANCER.md) | Public surplus capture and protocol-owned liquidity already have an explicit inventory/loss-budget design. | This is a non-live design, with separate refinement and external-execution obligations. |

One recorded policy difference needs resolution before importing locked-token
fee rights. The FIRE atlas's commitment-vault proposal distributes revenue by
commitment shares. In contrast,
[ZenoDEXYieldLikeFundingSafety](../../lean-mathlib/Proofs/ZenoDEXYieldLikeFundingSafety.lean)
explicitly excludes `holdToEarn` and `profitShareRight`; its source model
requires `noProfitShare = true`. The
[theorem/runtime matrix](ZENODEX_THEOREM_RUNTIME_MATRIX_V1.md) calls the shared
waterfall connection partial. These are different recorded contracts. A name
such as “service reward” does not resolve the economic distinction, and the
Lean Boolean premise does not prove that a real recipient performed a service.
This review does not select either policy or infer a legal classification.

### Official protocol comparison

Sources were consulted on 2026-09-05. This is documentation/source research,
without independent deployed-contract-state verification. Current and
historical mechanisms are distinguished; promotional return/volume claims
are not used as evidence of effectiveness.

| Protocol | LP return funding | Incentive-token functions and limits |
| --- | --- | --- |
| Uniswap | Traders pay swap fees; active LP liquidity earns its assigned share. Separately, external incentive programs can fund a specified reward token and duration. | UNI confers governance. Current official docs describe protocol-fee-funded UNI burning on v2 and selected v3 pools, and explicitly exclude an individual pro-rata claim on revenue. The docs also retain governance mint authority, although they report no active inflation. This is not an immutable finite-supply analogue. [LP fees](https://support.uniswap.org/hc/en-us/articles/20901935681677-What-is-a-liquidity-provider-LP-fee), [UNI](https://developers.uniswap.org/docs/ecosystem/governance/uni), [v3 incentives](https://developers.uniswap.org/docs/protocols/v3/concepts/liquidity-mining) |
| Curve | LP trading fees coexist with newly minted CRV directed by gauges and, where funded, additional incentives. | Locking CRV produces nontransferable, decaying veCRV: governance/gauge votes, eligible CRV reward boosts and protocol-fee distributions. CRV emissions follow a declining schedule, distinct from fee revenue. [Yield](https://docs.curve.finance/user/yield/overview), [veCRV](https://docs.curve.finance/user/vecrv/what-is-vecrv), [gauge mechanism](https://docs.curve.finance/developer/gauges/overview) |
| Aerodrome / Velodrome | Current docs distinguish staked liquidity receiving AERO/VELO emissions from unstaked liquidity retaining a fee share. Relevant staked-liquidity fees flow to voting positions. | Locked-token NFT positions direct emissions and receive selected-pool fee/voting-incentive distributions. External voting incentives are sponsor transfers. Weekly rebases reduce voting-position dilution but do not remove underlying token issuance. Lock duration affects voting power; token voting locks do not themselves lock ordinary LP capital. [Aerodrome](https://aerodrome.finance/docs), [Velodrome](https://velodrome.finance/docs) |
| PancakeSwap | Farm participants can receive LP trading fees plus CAKE rewards. Tokenomics 3.0 combines continued emissions with fee-funded burns and a net-deflation target. | Current governance docs use wallet CAKE voting power; archived veCAKE rights must not be presented as current. A supply cap and a burn target do not mean that no new rewards are minted. The consulted current sources establish governance/burning mechanisms, not a personal fee claim for merely holding CAKE. [Farming](https://docs.pancakeswap.finance/earn/yield-farming), [tokenomics](https://docs.pancakeswap.finance/protocol/cake-tokenomics), [governance](https://docs.pancakeswap.finance/protocol/voting) |

Curve's terminology needs particular care: its fee “burner” converts collected
assets into the distribution asset, currently crvUSD in the described system.
That operation is not a CRV-supply burn. [Curve fee architecture](https://docs.curve.finance/developer/fees/overview)

The observable token functions above can motivate demand for participation.
They do not establish how many buyers will want the rights, whether buyers
outweigh sellers, or a token-price effect. A user may already own or earn the
token they lock. A rebase or incentive payment is not external operating
revenue. Releasing previously minted treasury zDEX can increase circulating
supply while preserving total supply.

Ordinary emissions buy participation for the rewarded period; no retention
theorem follows. Uniswap's documented v3 program has a funded lifecycle and a
refundee, but closure also requires all positions to be unstaked; the nominal
end time alone does not settle every obligation. Aerodrome separately offers
launcher positions with actual withdrawal/range restrictions and an expiry.
These are different commitments from its voting-token lock. [Uniswap lifecycle](https://developers.uniswap.org/docs/protocols/v3/concepts/liquidity-mining), [Aero liquidity locks](https://aerodrome.finance/docs/launcher)

### The full service and risk budget

The actors include traders, borrowers, LPs, Stability Pool depositors, hosts,
reporters, challengers, provers, keepers, sponsors and governance participants.
Each can also belong to a coalition occupying several roles.

| Obligation | Economic source and owner to preserve | Distinction needed before a reward policy |
| --- | --- | --- |
| LP execution | Trader-paid pool fees; additional funded liquidity-service budget if approved | Fee income must be assessed alongside inventory exposure, adverse selection and execution costs. Gross fees are not net LP profit. |
| Host / availability work | Named host allocation or a separately funded service escrow | Recurring availability costs persist in low-fee epochs. An empty reserve cannot promise continued paid service. Publication authority remains separate from pay eligibility. |
| Oracle / challenges | Query/consumer fees and explicit reserve, with separately owned bonds | Successful report submission does not prove external truth. Slashing collateral is conditional security funding, not ordinary revenue or a guaranteed operating subsidy. |
| Proof generation / verification | Request fees, proof-reward allocation or explicit sponsor budget | Pay for an exact admitted work occurrence; distinguish proof validity from authenticity of economic inputs, prevent repeated payment and specify uncompleted-work refunds. |
| Keepers / liquidators | Governed execution fee, actual collected liquidation compensation or funded liveness reserve | Reimburse work without treating a refundable deposit as income. Self-generated work and rounding-to-zero penalty cases require separate controls. |
| Stability Pool risk capital | Its own principal and collateral entitlements; an explicitly assigned borrowing-fee/interest or risk-service payment where policy admits it | Debt-offset principal is consumed in exchange for collateral. The full collateral receipt is not yield. Reward accounting must distinguish principal conversion, realized liquidation gain/loss and service payments. |
| Loss/cover reserve | Specifically owned capital and authorized premium/fee inflows | A reserve backing existing claims is unavailable for discretionary rewards or burn. Exhaustion needs a recovery/terminal rule. |
| zDEX burn / optional support | Only its designated, unencumbered quote-asset budget | Purchase output and burn input must pair exactly; the same acquired zDEX atoms cannot also be paid to LPs. |

Liquity V2 is a useful comparator for the monetary lane: borrower interest
funds Stability Pool payments and protocol-incentivized external liquidity;
its governance directs the latter. Liquidation proceeds compensate depositors
whose BOLD offsets debt. Its risk documentation acknowledges that liquidation
gains can become losses. These mechanisms demonstrate a funding structure;
they do not authorize introducing interest into zUSD or establish equivalent
risk, peg behavior or liquidation policy. [BOLD/Earn](https://docs.liquity.org/v2-faq/bold-and-earn), [limited PIL governance](https://docs.liquity.org/v2-faq), [risk disclosure](https://docs.liquity.org/v2-documentation/risk-disclosure)

The AMM comparison does not supply an equivalent ZenoLedger host, recursive
proof service, Oracle market or zUSD Stability Pool merely because another
protocol also charges trading fees. Costs performed by an underlying chain
or outside infrastructure must be priced and attributed in ZenoDEX's own
deployment model. Curve's crvUSD/LLAMMA is an additional lending/liquidation
system, rather than evidence that every Curve pool provides a Stability Pool.
[Curve overview](https://docs.curve.finance/user/introduction)

## 2. Attack Query

The principal falsification question is whether a coalition can collect more
incremental subsidy than its irrecoverable cost while providing no additional
accepted service. Use the adversary-as-trader/LP/voter/sponsor as the default,
including common ownership hidden behind different addresses.

In one consistently valued experimental payoff model:

```text
incremental_coalition_gain
  = rewards + captured_external_incentives + recaptured_fees
    - fees_paid - execution_cost - inventory_or_manipulation_loss
```

Internal transfers within the coalition cancel. Self-funded sponsor payments
are not external gain. A positive result is a counterexample to that model's
claimed resistance, rather than evidence of a deployed exploit.

Named adverse scenarios for a local model:

- Volume-only allocation rewards repeated economically neutral turnover.
  LP or voting positions recapture fee flows assumed to deter it.
- A pool receives subsidy for nominal TVL supported by its own manipulated
  price, or for depth absent at execution time.
- Participants divide identities to capture multiple minimum payouts, or
  recycle capital through overlapping service commitments.
- Gauge voters capture allocations and sponsor matching for their own pools;
  the payer's willingness to subsidize is mistaken for external trading demand.
- Reporters, LPs and leveraged traders jointly benefit from a distorted
  benchmark used to measure both liquidity and risk.
- A host/prover/keeper receives repeated payment for one occurrence, or creates
  unnecessary work solely to claim a bounty.
- A burn or subsidy consumes funds already owed to withdrawers, Stability Pool
  claimants, reserve beneficiaries or unfinished service contracts.
- The campaign ends, the reward reserve empties, or an Oracle fails while an
  unimplemented claim/refund/recovery path still owns value.

Time-weighted stake and locked voting power address specific timing and
commitment questions; neither establishes coalition resistance. The current
protocol documentation does not establish universal wash-volume resistance.
Falsification must retain cross-lane positions and fee recapture instead of
excluding them by definition.

## 3. Bounded Model

### Budget laws before allocation algorithms

For each asset separately, let `B` be a dedicated budget's physical balance,
`D` actual funded deposits, `F` newly assigned settled fees, `P` paid claims and
`U` returned unallocated funds:

```text
B_next = B + D + F - P - U
0 <= outstanding_committed_claims_next <= B_next
```

Internal allocation transfers are not additional external revenue. Keep all
budget partitions disjoint; liabilities explain ownership of physical atoms
and are not another physical asset balance. Existing principal, accrued claims
and risk backing cannot be counted as free funds. A new service obligation may
consume capacity only after its entire admitted funding commitment is reserved.

For the fee allocation already implemented:

```text
fee_atoms = sum(destination_atoms) + residue_atoms
```

An economic-priority waterfall is an additional contract. The six-destination
arithmetic split alone does not prove reserve adequacy or service affordability.
Priority among required operating costs, contingent risk backing and
discretionary burn/support must be explicit and release-bound. During funding
shortfall, new discretionary commitments stop; preserved claims and the chosen
recovery policy still apply.

For zDEX, assuming no authorized issuance in the selected policy:

```text
total_zdex_next = total_zdex - burned_zdex
sum(paid_existing_zdex_rewards) <= initial_reward_inventory + actual_inflows
```

The existing per-occurrence retained-supply and epoch burn guards still apply.
These are atom identities. Quote-asset burn budgets cannot be compared directly
with zDEX emission or burn amounts. Conversion requires an exact purchase
receipt; experiments using a common numeraire need a pinned valuation method.
Finite inventory without further inflows cannot support indefinitely many
positive integer payouts. Fee-funded payouts also cannot promise positive
payments in every future epoch.

### Three implementation candidates

These alternatives extend existing designs and leave monetary policy unchanged.
They are ranked by readiness to serve as an experimental baseline, not proved
economic superiority.

1. **Fee-first services with capped campaigns.** Preserve ordinary LP fees and
   existing host/proof/oracle/keeper/risk budget ownership. Use actual assigned
   fees, a named treasury inventory or sponsor deposits for additional
   time-bounded liquidity campaigns. Each campaign names its asset, eligible
   service, cap, claimant, settlement rule, unallocated-fund owner and terminal
   path. This is the simplest comparator for a new allocation algorithm.
   Require evidence of the declared liquidity service; do not turn a passive
   zDEX balance into an entitlement by renaming it. An optional gauge vote
   could direct these funded caps without minting, subject to the unresolved
   governance/fee-rights policy.

2. **Fee-funded procurement of liquidity service.** Compare a deterministic
   capped procurement auction against the campaign baseline. Providers offer
   a quote for a specified duration and accepted depth/execution commitment;
   bids identify the exact pool, assets, capital commitment and compensation
   cap. Awards reserve existing funds, and payouts depend on committed service
   evidence. LP principal remains separately owned. Service shortfall, early
   exit, unavailable observations and unclaimed compensation need explicit
   outcomes. The auction allocates a residual budget after the chosen priority
   obligations. No bids or no funds means no new award. Payment-rule
   truthfulness, collusion resistance and benchmark integrity are open
   mathematical tasks. A high-level “lowest bid wins” rule proves none of them.

3. **Capped protocol-owned liquidity as an alternative baseline.** Apply the
   existing Treasury Rebalancer's pool/asset exposure and loss budgets to
   treasury-owned inventory. This reduces dependence on repeated external LP
   subsidy for that owned position, while moving inventory and execution risk
   onto the treasury. Fund it only from an approved unencumbered capital
   budget; do not count depositors' principal as protocol-owned capital.
   Preserve valuation, withdrawal, impairment and loss-stop rules. A finite
   treasury constrains depth, and ownership alone guarantees neither useful
   prices nor profitable liquidity.

Direct prior art narrows any novelty claim:

- Uniswap's funded v3 incentives already implement sponsored liquidity rewards
  with an owned close-out process. [Official design](https://github.com/Uniswap/v3-staker/blob/main/docs/Design.md)
- Liquity's PIL already allocates protocol revenue to liquidity through
  governance. [Official governance scope](https://docs.liquity.org/v2-faq)
- PancakeSwap's **archived** Farm Auctions sold access to incentivized farms:
  winning project bids were burned and losing bids refunded. This auctions
  subsidy access; it does not purchase a provider's verified depth commitment.
  [Archived mechanism](https://docs.pancakeswap.finance/products/farm-auctions)
- The am-AMM paper auctions temporary pool-management/fee rights; managers pay
  rent ultimately benefiting LPs. Its equilibrium claims depend on the paper's
  model. Charm's Medallion research describes strategies bidding to receive
  swap fees while paying LPs. These are fee-rights auctions, with a different
  auction object from service procurement. [am-AMM](https://arxiv.org/abs/2403.03367),
  [Medallion research](https://learn.charm.fi/charm/research/medallion)
- Olympus documents treasury-owned liquidity; its legacy liquidity bonds
  exchange for LP tokens. This supplies POL prior art, without adopting OHM's
  issuance or monetary design. [POL](https://docs.olympusdao.finance/main/overview/pol),
  [legacy bonds](https://docs.olympusdao.finance/main/legacy/bonding)

No exact-match prior art for the proposed ZenoDEX service-procurement contract
was established in this bounded search. This is an incomplete search result,
not evidence of novelty. Recovering adverse-selection losses through an
auction, dynamic fee or better execution is a possible additional revenue
source only after measured settlement. A paper's modeled LVR reduction is not
a spendable balance or a promise to cover all LP loss. [LVR model](https://arxiv.org/abs/2208.06046)

## 4. Evidence Lane

The next experiment should compare the same demand/price histories, service
requirements and capital budgets under the existing fee-first baseline,
fixed funded campaigns, the procurement candidate and capped POL. Keep
factual replay distinct from counterfactual modeling: actual user routing
responses under a changed policy are not observed by replay alone.

| Metric | Measurement contract and falsifiable outcome |
| --- | --- |
| Fee coverage | Settled external fees minus attributable execution/operating costs versus due service payments and reserve requirements, per asset. Label explicit subsidy separately; fail any overspend. |
| Burn capacity | Exact quote budget remaining after the selected obligations, realized zDEX purchase and burn atoms, and retained-supply compliance. No comparison of unlike units. |
| Useful depth / execution | Time-integrated executable size at fixed slippage bounds and both trade directions; realized user output against a pinned baseline. Hold eligible assets and observation quality constant. |
| Cost efficiency | Incremental useful depth or execution improvement per actual net subsidy, with common-numeraire sensitivity shown. Report no-benefit and negative-benefit cases. |
| Retention | Unsubsidized depth after a declared campaign horizon, distinguishing expiring locks from voluntary remaining liquidity. Replay models this conditionally; it cannot prove future behavior. |
| LP adverse selection | Fees and subsidies against inventory/rebalancing benchmark and execution costs. Report LVR separately from hold-versus-LP divergence; do not subtract both overlapping benchmarks as independent losses. |
| Coalition leakage | Maximum modeled net gain without additional admitted service across combined trader/LP/voter/sponsor/oracle roles, including self-funding cancellation and identity splitting. |
| Bootstrap / drought | Zero users, zero fees, one bidder, no bidder, depleted treasury, bursty demand and reward expiry; identify who still funds required hosts/oracles/proofs and when safe-mode rules activate. |
| Risk-service adequacy | Stability Pool debt absorbed, collateral received and realized loss; keeper execution cost; stale-report intervals; committed proof-work completion. Never label returned principal as reward. |

Executable acceptance would need independent integer reference calculations,
stateful ESSO/model checks for budget and lifecycle outcomes, and Lean proofs
of partition conservation, source bounds, authorized awards and terminal
disposition. Search/optimization tools may propose parameters or adversarial
histories; deterministic checks own their acceptance. Mathematical auction
claims need a fixed information/timing/coalition model. Economic demand and
cost calibration require observed data beyond those proofs.

This turn performed source/document inspection and official web research only.
It did not run Lean, ESSO, Julia/Morph, a simulation, new tests, a deployed-state
audit or a remote job. No tool-generated economic verdict is claimed.

Document verification checked relative link existence, all twelve recorded
local source hashes and paired Markdown fences. The style router selected
the public-claim documentation surface. Its suggested
`python3 tools/check_claims_registry.py` gate failed because the existing
registry references missing `tools/check_derivatives_authorization_matrix.py`
at `claims[123].evidence.files`. This note changes neither that registry nor
its evidence; no claim is promoted by the documentation checks.

## 5. Promotion Boundary

Before a policy can become implementable release semantics, the unresolved
choices are:

1. The allowed rights of zDEX holders/locks, reconciled with the recorded
   service-only versus profit-share difference; no inherited rights from CRV,
   AERO, VELO or CAKE.
2. Fee/service/risk priorities and cross-lane funding permissions, including
   host/oracle/proof costs during low activity. No fee rates are chosen here.
3. The reward asset and source: already funded zDEX inventory, quote-asset fees,
   external sponsor assets, or a permitted combination with separate accounts.
4. The exact measurable liquidity/risk service, beneficiary, award/payment
   mechanism, capital commitment and unavailability/exit behavior.
5. Risk reserve policy, Stability Pool loss ownership, accepted premium or
   borrowing-fee allocation, and failure/terminal treatment.
6. Bootstrap runway, renewal authority, residue/refund ownership and the
   experiment's comparison horizons.

The strongest immediate R&D target is source-bounded procurement layered over
the existing fee/service budget, evaluated against funded campaigns and POL.
It offers a concrete hypothesis: buying verified service may use a limited
budget more effectively than allocating rewards by nominal stake or votes.
This hypothesis has no novelty, superiority, equilibrium, profitable-LP,
token-appreciation, whole-program-safety or production claim in this note.

### Local source identity

SHA-256 hashes of inspected recovery anchors, not a new release manifest:

```text
ba9ac7ca950562eae24ceefee2c9468449780b1cfacf4779a410463edb403837  docs/FIRE_REVENUE_SURFACE_ATLAS.md
c01b1d40b7c0868901a2edebd233c6ff0ea05bbb0dec8ca7df04b392f545203e  docs/derivatives/PERP_INCENTIVES_V1.md
f6337aa32e9569da468e174dbc3a27831f3b5a1673c744f44b89061977bf3bc4  docs/derivatives/ZUSD_V1.md
3508a993c99130349814bdd055d8cd300a8207e44458cc42044c8f0c961d391b  docs/ZENO_ORACLE_TOKEN_BUDGET_V1.md
dcf7209eccab9e022950053ff5e1fdb85ededdb20410123697ea94ce653554f9  docs/research/ZDEX_HYPERDEFLATION_V1_20260821.md
32985ee88b0b15a0b6ef1408e60ac1767f93e20eade434090011e144ecd56990  docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md
00c80406b24d2ab25b6c51e670ad4357f4f7875689828d0d30d67918de2d0b02  docs/research/ZENODEX_THEOREM_RUNTIME_MATRIX_V1.md
56fbe3681fb0a111f483551aa4505558219c4f03c72bb600d0b874aed7e42c7f  docs/PROOF_BACKED_TREASURY_REBALANCER.md
6cef80bb0aa15b6dd036ced8dd26f0ff429e15e02926b999c0d192afd86aeb61  lean-mathlib/Proofs/ZenoDEXYieldLikeFundingSafety.lean
8f976781349e31ae9fd3c48b8534ae4fbfe74e8ce33e6b62c6a627c8109bad84  src/core/zdex_fee_allocation_v1.py
b29490205c099e5f38812a71555c65d20b5de1c333425c22ed2d4fbe392d50df  src/core/zdex_fee_allocation_types_v1.py
9cea1252da4a329af7a26d92bfd2d23b28fcbbba6ddaca98969e8c34e6377172  src/core/proof_mining_claimability_gate.py
```
