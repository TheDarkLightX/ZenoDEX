# ZenoProof General Market Business Model V1

Status: research-only, unselected, unmounted. This report defines no live fee,
reward, payment, market, verifier, token, settlement, finality, or release rule.

## Decision Summary

ZenoProof should be designed as a general verified-computation market. ZRPF is
its recurring anchor buyer. External buyers can fund proofs, counterexamples,
improvement certificates, maintenance, and private or public-good computation.

The strongest business structure to test is a phased hybrid:

1. Buyer-prefunded proof and counterexample jobs with objective settlement.
2. Exact admission-cost recovery plus a 2%-5% external success-fee experiment;
   3% is the V1 simulation point.
3. Enterprise subscriptions for an explicit reserved-capacity partition and
   support. Subscription status cannot affect proof validity or settlement,
   and a governed nonzero permissionless capacity floor remains available.
4. Public catalog verification, adaptation, and freshness services after the
   canonical reuse contract is stable.
5. Linked-assurance crowdfunding for non-rival public proofs after its
   pledge/refund lifecycle is implemented.

Seller payments come from buyers, ZRPF resource fees, or purpose-bound public
goods budgets. The fixed 30M-ZDEX proof reserve supplies temporary bonuses and
initial distribution. Recurring proof computation must survive reserve
exhaustion.

## Relationship to Boundless

[Boundless](https://docs.boundless.network/developers/proof-lifecycle) is the
closest current analogue for the ZRPF assigned-proof lane. A requester posts a
proof request whose price rises over time; a prover accepts and locks the job
with collateral; failure can slash that collateral; fulfillment ends in proof
verification. That structure supports the prefunded reverse-Dutch lock used in
this report.

ZenoProof has a wider product grammar. Its canonical work order may request a
proof under any admitted verifier profile, a counterexample, an improvement
certificate, maintenance, re-verification, or reusable catalog work. ZRPF is
the predictable internal buyer of recursive execution proofs. The general
market can serve independent buyers and sponsors. The experimental 2%-5%
external success fee in this report is a ZenoProof hypothesis; it was not
copied from Boundless pricing.

### Lessons from Boundless primary sources

The source review was refreshed on 2026-08-17 using Boundless documentation,
releases, its security repository, and four published audit PDFs. Audit status
is preserved below. A fixed historical finding is treated as a regression
lesson, rather than a claim about current Boundless code.

| Boundless evidence | Source status | ZenoProof construction rule |
| --- | --- | --- |
| A request ID was not bound to its request digest, allowing the wrong account to be charged | Critical, fixed in the April 2025 Veridise core audit | One canonical occurrence binds request ID, request digest, claim, verifier profile, payer, and payment account |
| A commutative batch root allowed proof fields to be permuted | High, fixed in the April 2025 Veridise core audit | Commit the ordered leaf manifest; tag leaves and internal nodes separately |
| A callback ran before prover payment | High, fixed in the April 2025 Veridise core audit | Commit payment and its outbox ancestor before external delivery |
| Client and prover signatures used the same message domain | Medium, fixed in the April 2025 Veridise core audit | Separate buyer, prover-lock, verifier, and publication signing domains |
| Re-submitting one request ID could execute its callback again | Medium, acknowledged in the July 2025 Hexens core audit | Derive one idempotency key from promotion subject, request occurrence, and effect index |
| An unlocked or expired-lock proof could become fulfilled without guaranteed payment | Low, acknowledged in the July 2025 Hexens core audit | Reserve maximum buyer liability before lock; missing payment rejects without fulfillment |
| Per-recipient reward caps could be split across work logs | Medium, resolved in the September 2025 OpenZeppelin PoVW audit | Apply caps across all work-log identities for one beneficial recipient and epoch |
| Pre-v2.0.2 unsubmitted PoVW work receipts lived in an ephemeral container filesystem | Fixed by the v2.0.2 persistence change; old receipts required pre-upgrade submission | Fsync a content-addressed work receipt before acknowledging reward-eligible computation; replay it after restart and migration |
| Broker requestor priority levels affect order ranking | Documented v2.0.2 feature | Paid reservations occupy a capped partition and cannot consume the permissionless floor or alter verification |
| Lock timeout is absolute from ramp start; 50% of a defaulted lock bond is burned and 50% funds a secondary-prover race | Documented auction design | Check the actual remaining work window at lock time; fund restitution, re-procurement, and insurance before any residual penalty burn |

Primary artifacts and observed PDF hashes are recorded in the generated JSON.
The current [Boundless homepage](https://boundless.network/) says the project
began with proofs and now markets distributed GPU AI compute. This supports a
limited strategic inference: workload diversity may improve fleet utilization.
It does not establish that the Boundless proof market failed. ZenoProof keeps a
general verifier-profile grammar for the same utilization reason, while every
non-ZRPF workload remains outside ZenoLedger settlement authority.

Static collateral multiples are not adopted. Boundless's auction guide uses a
10x-maximum-price example and warns that larger collateral can reduce locking.
ZenoProof therefore leaves the collateral curve unselected pending measured
default loss, replacement cost, prover capital, and detection data. An open
secondary-prover race is also unselected: urgent redundant computation must be
explicitly buyer-funded, while ordinary recovery uses a new assigned auction.

## What the Market Sells

A public proof is non-rival: disclosure lets anyone copy its bytes. Artificial
scarcity around public proof bytes has weak economics. The market can sell real,
claim-bound products:

- a funded work order for a new proof or counterexample;
- private delivery or a time-limited embargo;
- verification against a named verifier profile;
- adaptation to new inputs, assumptions, releases, or toolchains;
- maintenance and re-verification obligations;
- a claim-bound improvement certificate;
- reserved proving capacity and service guarantees.

A future transferable instrument must identify the exact right being
transferred. It cannot represent truth, verifier acceptance, ZenoLedger
finality, or ownership of a public mathematical fact. V1 therefore keeps job,
escrow, reward, and proof-admission receipts non-transferable.

| Product | Recommended allocation mechanism | Primary payer |
| --- | --- | --- |
| Assigned validity proof | Prefunded reverse-Dutch lock, deadline, performance bond | External buyer |
| ZRPF batch proof | Same lock market with a direct-execution price cap | DEX resource fees |
| Counterexample search | Canonical partition milestones plus terminal refutation bounty | Sponsor or public-good budget |
| Improvement certificate | Best verified marginal improvement at a deadline, with a total cap | Sponsor |
| Public-good proof | Linked-assurance pledge threshold and failure refunds | Multiple sponsors |
| Maintenance/re-verification | Costed subscription with slashable freshness obligation | Subscriber |
| Catalog reuse | Cache hit, verification/adaptation service, exact storage cost | Reuse requester |
| Private proof | Prefunded commit/reveal with payment locked before payload release | External buyer |

### Possible secondary-market layer

ZenoDEX could eventually trade proof-related rights. Each instrument needs a
closed entitlement and lifecycle. Candidate assets include an unassigned funded
work order, a private-access or embargo right, a reserved-capacity right, a
maintenance obligation, or a claim-bound settlement right. Their prices can
move through the ordinary ZenoDEX trading surface.

The public proof bytes remain copyable. A transferable instrument cannot confer
ownership of a public mathematical fact, change the proof's claim or
assumptions, substitute for verifier acceptance, or carry ZenoLedger finality.
V1 keeps this layer disabled and all job, reward, and proof-admission receipts
non-transferable while the entitlement, expiry, custody, and failure semantics
remain open.

## Game Surface

Players:

- external proof buyers and bounty sponsors;
- ZRPF as an anchor buyer;
- proof miners and assigned provers;
- counterexample and improvement searchers;
- verifiers, aggregators, and artifact maintainers;
- enterprise reserved-capacity customers;
- the proof-reserve and protocol-treasury controllers;
- ZenoLedger validators.

Canonical job identity binds:

```text
WorkKey = H(
  product_kind,
  claim,
  assumptions,
  public_inputs,
  requested_output,
  verifier_profile,
  release,
  deadline,
  access_policy
)
```

Changing a wallet, nonce, metadata field, proof encoding, or artifact bytes
does not create new economic work under the same `WorkKey`.

## Money Flow

For an external job:

```text
BuyerPrefund
  = SellerMaximum
  + SuccessFeeMaximum
  + ListingFee
  + VerifierBudget
  + PublicationBudget

SuccessFee = ceil(ActualSellerPayment * success_fee_bps / 10_000)

BuyerPrefund
  = SellerPayment
  + VerifierCost
  + PublicationCost
  + ListingFee
  + SuccessFee
  + BuyerRefund
```

The seller posts a separate performance bond. A valid, unique, bound result
returns the bond. Invalid or late work routes the declared bond by priority:

```text
SellerBond
  = BuyerRestitution
  + ReplacementProcurement
  + InsuranceRecovery
  + ResidualPenaltyBurn
  + SellerReturn

UnfundedLossClaims > 0 -> ResidualPenaltyBurn = 0
```

Slashed value does not become burnable protocol revenue while a restitution,
re-procurement, or insurance-recovery liability remains. A residual penalty
burn must be declared in the job terms; it is distinct from surplus buyback.

Protocol revenue is limited to:

- listing/admission cost recovery;
- external-job success fees;
- enterprise subscription fees;
- catalog verification, adaptation, storage, or freshness-service fees.

Buyer escrow, seller GMV, verifier pass-through, publication cost, refunds,
bond restitution, and internal ZRPF transfers are excluded from protocol
revenue.

ZRPF has separate accounting:

```text
ZRPFAnchorContribution = DEXResourceFees - ActualProofAndPublicationCost
```

ZRPF pays no market take to the same protocol. Positive anchor contribution
enters the protocol-wide waterfall; negative contribution consumes a declared
runway budget or triggers adaptive batching/direct execution.

The recommended payment unit for compute, verification, refunds, and bonds is
a stable quote asset such as zUSD when available. A job may name another asset
before bidding. ZDEX remains the fixed-reserve bonus asset and the buy-and-burn
target. Requiring volatile ZDEX for every compute invoice would shift price risk
to provers and make cost discovery noisier. A ZDEX bond would need a conservative
haircut and continuous sufficiency rule; a zUSD bond is simpler for launch.

### Integration with the 22-participant funding registry

The source-bound G1 registry inventories 22 participant classes. Twelve require
explicit service or operations budgets: validators; oracle participants;
liquidators and keepers; Tau relayers; solvers, batchers, and sequencers; proof
miners; security workers; interface hosts; core operations; insurance and bad
debt; liquidity bootstrap; and optional Stability Pool rewards.

The recurring source is finalized protocol revenue routed into the selected
role budget after property and refund reconciliation. Role-specific action fees,
external-I/O fees, signed interface fees, and verified solver improvements may
fund their named roles. Buyer proof-job escrow remains restricted to the job's
seller, verifier, publication, protocol-fee, and refund legs.

Launch has no fee history, so critical services need a purpose-bound prefunded
runway. The current registry selects zero of twelve role budgets. Its safe
failure rule disables the dependent function, preserves property claims, or
uses direct execution when an optional scaling service is unfunded. Proof-market
fees become one additional recurring input to this obligations-first system.

## Attack Query

The bounded analysis searches for:

```text
SellerPaid && !VerifiedBoundUnique

DuplicatePayment(WorkKey)

BuyerSellerCoalitionProfit
  = Bonus + FeeCredits
  - IrreversibleFee
  - VerificationCost
  - ComputationCost
  - ExpectedPenalty
  > 0

FrivolousDisputeGain >= Bond
or Bond >= HonestChallengeGain

ReportedProtocolRevenue
  > ListingFee + ExternalSuccessFee + Subscription + CatalogServiceFee
```

It also checks wallet splitting, overlapping counterexample partitions,
withheld maintenance, ZRPF self-fee accounting, verifier substitution, and any
attempt to attach finality to a proof-market receipt.

## Bounded Model

All payment and token quantities use exact integers.

### Objective proof settlement

Fourteen closed checks gate seller payment: proof validity, claim binding,
assumption binding, input binding, output binding, current verifier profile,
unclaimed canonical work key, non-vacuity, request-ID binding, ordered-batch
binding, role-separated signatures, committed buyer escrow, a durable work
receipt, and an unclaimed external-effect key. The checker enumerates all
16,384 boolean vectors. Every rejected vector pays zero to the seller and
preserves prefund/bond conservation.

Boundless's absolute lock deadline motivates an additional admission rule:

```text
EffectiveWorkBlocks = PrimaryDeadlineHeight - LockHeight
RequiredWorkBlocks  = EstimatedProvingBlocks + SafetyMarginBlocks

AdmitLock -> EffectiveWorkBlocks >= RequiredWorkBlocks
```

All time inputs are canonical ledger heights. Wall clocks and mixed
seconds/block conversions are excluded from settlement. Paid capacity follows:

```text
PriorityReservedSlots + PermissionlessFloorSlots <= TotalSlots
PermissionlessFloorSlots > 0
PerRequestorPriorityCap <= PriorityReservedSlots
```

This bounded partition rule prevents complete priority starvation. Queue
fairness, geographic diversity, and beneficial-owner aggregation remain open
mechanism and evidence obligations.

The buyer selects the objective verifier contract before listing. There is no
post-completion subjective veto that lets a buyer obtain a valid result and
withhold payment.

### Contribution-locked bonus

The candidate bonus is:

```text
Bonus <= ScheduledReserveCap
Bonus <= useful_value_bonus_bps * VerifiedUsefulValue / 10_000
Bonus <= external_fee_cap_bps * IrreversibleExternalFee / 10_000
       + savings_cap_bps * VerifiedProtocolSavings / 10_000
```

For ordinary external jobs, the launch candidate caps bonus at 50% of the
irreversible external success fee. With no fee credit:

```text
Bonus <= 0.5 * Fee
-> BuyerSellerCoalitionProfit <= -0.5 * Fee - other_costs <= 0
```

The exact bounded search checked 2,601 fee/bonus pairs under this half-fee cap.
No positive coalition profit appeared. The named raw-volume mutant pays a 5%
bonus against a 3% fee and yields a positive 2% round-trip profit before
compute. This is why raw volume cannot be rewarded by an emission schedule
that exceeds irreversible cost.

ZRPF savings cannot enlarge an external-job bonus in the business simulation.
Protocol-job savings use the separately source-bound ZRPF submodel and its own
verified-savings cap.

### Counterexample procurement

Winner-take-all first-valid bounties motivate many searchers to duplicate
private compute. The V1 candidate divides a bounded search domain into
registry-issued, non-overlapping partitions:

```text
TotalCounterexampleBudget = MilestonePool + TerminalPool
MilestonePayment_i
  = floor(MilestonePool * NovelCoverage_i / TotalNovelCoverage)
TerminalPool -> first canonical valid counterexample
```

Wallet count never enters the formula. A release-selected verifier must prove
partition admission, novelty, non-overlap, and the terminal refutation. The
illustrative split assigns 20% to novel search coverage and 80% to a decisive
counterexample. This ratio remains unselected.

### Dispute and Sybil bounds

The deterministic dispute-bond interval is:

```text
FrivolousExternalGain < Bond < HonestReward + HonestExternalGain
```

If no integer bond lies inside the interval, the dispute game cannot be made
incentive-compatible by bond tuning alone.

For a legacy equal-split reward pool `V` and cohort size `n`, a two-identity
split is weakly deterred when:

```text
Bond >= ceil(V * (n - 1) / (n * (n + 1)))
```

The preferred construction avoids wallet-count and equal-split rewards. It
pays canonical work or admitted search coverage.

### Public-good assurance and maintenance

For buyer value `v`, pledge `B`, and delay ratio `num/den`, the existing exact
linked-assurance candidate uses:

```text
v * den >= B * den + num * v
```

Pledges fund the job only after the threshold. Failure returns pledge escrow
under the declared refund rule.

Maintenance uses the exact one-shot-deviation predicate:

```text
c * (eps_den * (delta_den - delta_num) + eps_num * delta_num)
<= eps_num * (delta_num * payment
              + slash * (delta_den - delta_num))
```

This prevents a simplified reputation score from substituting for actual
payment, cost, slash, and continuation-value economics.

## Business Simulation

The deterministic stress matrix crosses three demand levels with efficient,
base, and stressed costs. The nine weights total 10,000 basis points. The
fixture uses 100 quote atoms per illustrative dollar. It is a structural
sensitivity analysis rather than a forecast.

| Candidate | Expected monthly cash surplus | After bootstrap bonus | Positive-state weight | Worst monthly loss | Coalition-safe |
| --- | ---: | ---: | ---: | ---: | --- |
| Success fee only, 5% | $16,626.25 | $16,626.25 | 31.25% | $109,900 | yes |
| Listing + success, 3.5% | -$1,973.75 | -$1,973.75 | 31.25% | $119,700 | yes |
| Hybrid SLA, 3% | $58,195 | $49,195 | 62.5% | $88,900 | yes |
| Hybrid SLA + catalog | $111,968.12 | $102,968.12 | 62.5% | $88,050 | yes |
| Full hybrid + assurance | $117,368.12 | $107,468.12 | 62.5% | $87,450 | yes |
| Subscription only | $73,295 | $73,295 | 62.5% | $86,100 | yes |
| Full hybrid + 5% raw-volume emission | $117,368.12 | $18,368.12 | 62.5% | $87,450 | no |

Catalog and public-good demand are scenario inputs. Their apparent advantage
does not establish that demand exists. The phased recommendation captures the
hybrid revenue structure while delaying the two most assumption-sensitive
features.

The take-rate break-even surface shows why subscriptions are useful without
making them proof authority:

| Monthly gap | GMV at 2% | GMV at 3% | GMV at 5% | $5k subscriptions covering gap |
| ---: | ---: | ---: | ---: | ---: |
| $50,000 | $2,500,000 | $1,666,666.67 | $1,000,000 | 10 |
| $100,000 | $5,000,000 | $3,333,333.34 | $2,000,000 | 20 |
| $250,000 | $12,500,000 | $8,333,333.34 | $5,000,000 | 50 |

The final launch fee should be derived from qualified cost and demand evidence.
If a competitive fee cap cannot cover the declared runway under conservative
volume, the product needs prefunding or a smaller service boundary.

### BMSE evaluation

BMSE was exercised in two ways at commit
`bd3601a1c5aea8e24c7775682fa7936540b5d0e4`:

- Its stock marketplace profile selected a self-serve, two-sided subscription
  row under generic SaaS/marketplace/fintech priors.
- Its certificate-backed Pareto primitive replayed the proof-specific exact
  evaluations. With a 60% positive-state threshold, its frontier contained
  `FULL_HYBRID_ASSURANCE`, `HYBRID_SLA_CATALOG`, and `SUBSCRIPTION_ONLY`.

The mapped `expected_npv` field is 24 times expected monthly contribution and
is an undiscounted proxy. BMSE authenticates deterministic frontier decisions;
it does not verify the proof-market premises.

## 30M-ZDEX Proof Reserve

The following launch envelope is recommended for further testing:

| Lane | Cap | ZDEX |
| --- | ---: | ---: |
| ZRPF and protocol-critical proofs | 50% | 15,000,000 |
| External verified-work matching | 20% | 6,000,000 |
| Counterexamples and improvements | 15% | 4,500,000 |
| Verifier and maintenance work | 10% | 3,000,000 |
| Unallocated safety | 5% | 1,500,000 |

The global candidate release is 5 basis points per day of the remaining
reserve, with per-lane and per-job caps. These percentages are an unselected
envelope. They can be changed before activation without altering the fixed
30M-ZDEX total.

If every daily cap were earned, the existing exact integer schedule releases at
most approximately 5,005,601 ZDEX after one year, 15,545,369 after four years,
and 25,165,677 after ten years. Unperformed work releases zero, and integer dust
remains in the reserve.

Reserve exhaustion stops bonuses. It does not stop buyer-funded proof work,
ZRPF resource-fee procurement, or direct ZenoDEX execution.

## Deflationary Link

The proof market adds an external fee-revenue lane. It does not receive first
claim on protocol-wide surplus.

```text
TrueSurplus
  = FinalizedUnrestrictedRevenue
  - refunds and property claims
  - proof sellers and verifiers
  - validators, oracles, relayers, and other critical services
  - safety, insurance, hosting, maintenance, and operations prefund
  - admitted bounded growth liabilities
```

Only positive `TrueSurplus` enters buy-and-burn. Routing 100% of this residual
supports hyper-deflation while preserving every participant's prior claim. The
30M reserve distributes already-created ZDEX and does not mint new supply.

## Evidence Lane

Current evidence:

- exact Python model and 16,384-vector settlement enumeration;
- Boundless-derived effective-window, liability-first bond, durable-receipt,
  payment-escrow, ordered-binding, callback-idempotency, and permissionless-floor
  guards;
- a source-status-preserving review of official Boundless documentation,
  releases, and four published audit PDFs;
- 2,601-case half-fee self-dealing search and a positive raw-volume mutant;
- nine-state-weight business-model sweep;
- BMSE generic baseline and certificate-backed custom Pareto receipt;
- ESSO dual-solver agreement over the bounded payment/refund lifecycle,
  durable receipt gate, atomic callback-outbox ancestry, and one-shot delivery;
- a retained ESSO counterexample showing why refund must bind zero witness and
  zero claimed work key;
- six directly compiled Lean files for bounty caps, composition, Sybil bonds,
  linked assurance, maintenance, and dispute intervals;
- the separate ZRPF cost, procurement, waterfall, and reserve submodel.
- the exact 22-participant registry projection, including twelve currently
  unselected service budgets and their fail-safe exhaustion behaviors.

Required before selection:

- calibrated demand, compute, verification, storage, support, and acquisition
  distributions from real quotes or testnet observations;
- repository-wide Lean-root integration and runtime projections for the six
  directly compiled theorem files;
- an independently reviewed beneficial-owner and related-party policy;
- product decisions on default access policy, payment asset, reserve lane caps,
  counterexample milestone share, and enterprise launch scope.
- qualified prefund and recurring-fee budgets for every launch-critical role.

Required before production:

- production Rust transitions and canonical codecs;
- release-selected verifier registries and opaque admission witnesses;
- mounted ZenoLedger escrow, payment, refund, and restitution capability;
- migration, restart, concurrency, crash, replay, and no-bypass evidence.
- independent-process crash, restart, migration, and redelivery evidence for
  durable receipt-before-payment and committed-outbox idempotency.

## Promotion Boundary

This work supports the hypothesis that a hybrid two-sided proof-service market
is the best structure to test. It does not select prices, predict demand,
activate token distribution, establish proof correctness, prove claimant
identity, or authorize settlement. ZenoLedger remains the only durable economic
writer and finality authority.
