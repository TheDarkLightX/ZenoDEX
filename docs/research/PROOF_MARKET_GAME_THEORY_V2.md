# ZenoProof Procurement Game Theory V2

Status: `RESEARCH_ONLY_UNSELECTED_UNMOUNTED`

This packet evaluates proof-procurement incentives. It defines no live price,
fee, reward, bond, assignment, token, proof-admission, settlement, or release
rule. ZenoLedger remains the sole proposed economic commit authority, and a
verifier witness remains necessary before seller payment.

## Decision Summary

The V1 reverse-Dutch envelope is retained as liveness sensitivity evidence. It
is ineligible to become the default procurement mechanism. Its public rising
clock permits profitable waiting, its reported competitive payments sometimes
fall below the stated minimum, and its modeled bond loss conflicts with the V1
ESSO bond disposition.

The current leading internal experiment is a separated hybrid. It has not yet
won a mechanism tournament or been selected for launch:

1. Routine ZRPF jobs use a lagged benchmark-indexed posted price, sealed
   acceptances, and capacity-ticket assignment from a committed consensus seed.
2. A no-acceptance round may admit sealed late-capacity bids only at or below
   the original posted price. The buyer chooses the cheaper eligible bid or
   funded direct-execution outside option. This lane remains research-only.
3. If neither option is funded, the job is rejected before admission. Funded
   direct execution preserves correctness and settlement availability.
4. Critical jobs may fund a primary and an independently paid standby from a
   different measured failure domain. Domain labels do not prove statistical
   independence.
5. The fixed 30,000,000-ZDEX proof reserve may reward verified useful work,
   qualification, and contestability under one `EconomicWorkKey` and
   owner/epoch caps.
   Recurring proof work must remain fully payable from fees when the reserve is
   zero.

The public reverse-Dutch clock remains available only as an experiment. A
reverse-second-price mechanism remains a useful theorem/control lane under a
fixed bidder set. Its coalition counterexample excludes it from the launch
recommendation. A separate example shows that address count does not establish
beneficial-owner diversity; it is not a profitable false-name bidding witness.

## 1. Game Surface

### Players and authority

- ZRPF, funded from DEX resource fees, is the recurring internal buyer.
- External buyers prefund their own proof, counterexample, or computation jobs.
- Provers choose entry, acceptance, bid, reveal, effort, submission, default,
  and exit.
- Standby provers sell reserved availability and activated computation.
- The deterministic verifier decides whether a result satisfies the named
  profile and `OccurrenceKey`.
- ZenoLedger commits escrow, payment, refund, bond disposition, proof record,
  and the one-shot `OccurrenceKey` payment claim.
- The proof reserve controller can propose a bounded ZDEX bonus. It cannot
  replace the stable base payment or authorize proof admission.

Reserve deduplication and job settlement use different keys:

```text
EconomicWorkKey = H(
  product_kind,
  claim,
  assumptions,
  public_inputs,
  requested_output,
  verifier_profile,
  release
)

OccurrenceKey = H(
  EconomicWorkKey,
  buyer,
  prefund_commitment,
  deadline,
  access_policy,
  nonce
)
```

The reference key encoding is domain-separated by the byte tag
`ZenoDEX/EconomicWorkKey/v2`. It emits the seven field names and values in the
declared order, framing every UTF-8 NFC-normalized byte string with a four-byte
big-endian length, then returns `ewk:v2:` plus the lowercase SHA-256 digest. A
field with leading or trailing whitespace, control or format characters, non-NFC text, or
more than 1 MiB of encoded bytes is rejected. This defines exact encoding for
the reference subject; a runtime parser and cross-language byte-parity receipt
remain open.

The reference claim request carries this descriptor and derives its nullifier
inside the transition. A caller-supplied digest is rejected, so the bounded
model does not treat key syntax alone as proof that a key matches the claimed
work.

Base payment nullifies on `OccurrenceKey`. The finite reserve bonus nullifies on
`EconomicWorkKey`. The current key deduplicates only identical canonical task
encodings. A semantically equivalent task can receive a different key unless a
closed protocol task registry or an independently verified equivalence
certificate binds the encodings. `SEMANTICALLY_EQUIVALENT_WORK_REKEY` therefore
remains an open reserve-extraction attack.

### Exact payoffs

For a selected prover `i`:

```text
ExpectedProverUtility_i
  = p_success_i * (payment_i + verified_bonus_i - success_cost_i)
  + p_detected_collectible_prover_fault_i
      * (-prover_fault_cost_i - collected_slash_i)
  + p_prover_fault_without_collectible_slash_i
      * (-prover_fault_cost_i)
  + p_verifier_fault_i * (-verifier_fault_cost_i)
  - capital_lock_cost_i
  + expected_outside_revenue_i

p_success_i
  + p_detected_collectible_prover_fault_i
  + p_prover_fault_without_collectible_slash_i
  + p_verifier_fault_i
  = 1
```

The two prover-fault events partition faults by whether an enforceable slash is
actually collectible. Detected or attributed faults with no collectible slash
belong to the second event.

For the buyer:

```text
BuyerUtility
  = delivered_value
  - payment
  - verifier_and_publication_cost
  - delay_loss
  - reprocurement_premium
```

The design cannot deter an unbounded external sabotage gain with a finite bond.
Every job therefore needs a bounded blast radius, a funded direct or standby
fallback, and a standardized loss schedule.

### Funding lanes

```text
InternalZRPFPrefund
  = allocated_resource_fees
  + declared_runway_budget

ExternalJobPrefund
  = seller_maximum
  + verifier_budget
  + publication_budget
  + exact_external_success_fee_maximum

ProofReserveBonus
  <= min(
       remaining_30M_ZDEX_reserve,
       job_bonus_cap,
       owner_epoch_remaining_cap
     )
```

The bonus pays only after independently base-funded, verified, useful,
unclaimed work. Base funding may come from allocated DEX resource fees, buyer
prefunding, or a declared runway budget. A reserve-admission verifier must bind
beneficial-owner evidence and reject self-dealing or related-party circular
jobs. The current enum models that classification as a premise; no mounted
beneficial-owner verifier exists. Bid count, request count, and wallet count
earn no bonus.

## 2. Attack Query

Every strategic claim is posed as an existential deviation:

```text
exists state, type profile, strategy, deviation:
  deviating_utility > baseline_utility
```

### V1 payment-floor defect

The saved V1 model assigns the winner's reservation price directly even when
the auction starts above that price:

| Scenario | Reported payment | Minimum price | Correct floor |
| --- | ---: | ---: | ---: |
| Large, efficient | 3,520,442 | 3,767,112 | 3,767,112 |
| Very large, efficient | 27,960,929 | 34,071,112 | 34,071,112 |

Correcting only this floor raises the weighted payment from 6,624,003 to
6,718,880 micro-USD atoms, or from 1.5526 to 1.5749 times the modeled reference
cost.

### Public-clock unilateral waiting

For the V1 micro-efficient scenario:

```text
cost-derived stop:              526,147
next prover's stop:             848,346
profitable delayed stop:        848,345
additional success payment:     322,198
success-adjusted expected gain: 315,754
```

The delayed stop still leaves the required proof and publication window. The
saved calculation assumes unchanged failure probability and zero incremental
waiting or opportunity cost. Its general profitability condition is:

```text
success_adjusted_payment_gain
  > incremental_wait_cost + incremental_failure_loss
```

Under the saved assumptions, applying this one-bidder wait across the twelve V1
scenarios raises weighted payment
to 8,092,995 atoms, or 1.8969 times reference cost. The public clock therefore
fails unilateral truthfulness before considering a cartel.

The micro-stressed scenario has one eligible prover. It can delay from
1,427,481 to the 2,222,224 cap while preserving the deadline. This is unilateral
monopoly extraction.

### First-price scarcity deviation

With true costs `(1, 3, 4)` and a cap of `4`, the lowest-cost prover receives
utility zero from a truthful bid of `1`. Reporting `2` still wins and earns
utility `1`. Sealed pay-as-bid removes clock timing and last-look undercutting;
it retains bid shading. Its role is limited to a short capped scarcity fallback.

### Critical-price coalition

With costs and reports `(1, 2, 4)`, reverse-second-price pays `2` and gives the
two low-cost bidders joint utility `1`. If the runner-up reports `4`, the same
winner receives `4` and coalition utility rises to `3`. This mechanism is
unilaterally truthful under its exact assumptions and coalition-manipulable.

### Address-count diversity failure

One owner can submit three address-level reports `(1, 5, 5)`. A three-address
competition gate passes and reverse-second-price pays `5`. A distinct-owner
gate fails. The single-address baseline bid `(1)` at reserve `5` also pays `5`;
at cost `1`, both cases give utility `4` and the bounded false-name utility gain
is zero. This example refutes address count as owner-diversity evidence. Any
identity-dependent payment or cap needs authenticated economic-operator
evidence.

Over a complete uniform ticket cycle, an owner's aggregate weight is the sum of
its authenticated capacity units, so a capacity-preserving split leaves its
aggregate win count unchanged. Fixed-seed assignment is not split-invariant:
alias ordering can change the selected owner. This property requires uniform,
unpredictable, unbiased randomness and does not authenticate capacity or stop
aliases from evading owner-level diversity caps.

### Stationary equal-share cartel

For `n` risk-neutral symmetric provers with perfect monitoring, an enforceable
stationary equal expected share every period, immediate grim-trigger
punishment, monopoly margin `M`, discount `delta`, and permanent zero punishment
profit:

```text
PV_cooperate = (M/n) / (1-delta)
PV_deviate   = M

one-shot deviation is unprofitable iff delta >= 1 - 1/n
```

For three such provers, `delta = 2/3` is the cooperation boundary. This formula
does not apply to a member at an arbitrary position in a deterministic rotation
without transfers. Sealed bids remove reactive observation; prearranged bids
and allocation remain possible in a repeated market.

### V1 bond mismatch

V1 calibration prices default as loss of 100% of the offered bond. Its ESSO
lifecycle routes one of two bond units to restitution and returns the other.
For the micro workload, named loss is 3,777,780 atoms while a 50% disposition
would supply 1,888,890. These artifacts cannot compose.

V2 separates restitution and deterrence:

```text
RestitutionLoss
  = replacement_premium
  + standardized_delay_loss
  + verifier_waste
  + standby_activation

DeterrenceBond
  = ceil(
      max(0, avoidable_cost + bounded_sabotage_gain - future_value_lost)
      * 10000 / detection_probability_bps
    )

RequiredBond = max(RestitutionLoss, DeterrenceBond)
```

This formula assumes `future_value_lost` is already an expected present value;
`detection_probability_bps` includes enforceable collection; the sabotage term
is a conservative bound on net incremental gain; and restitution components are
disjoint. One forfeited bond can both restore named loss and deter deviation,
which is why the maximum is used instead of their sum.

A verifier-created, occurrence-bound witness for an appealable prover-fault
cause permits full slashing. Named losses are funded first and any residual
enters the declared insurance/penalty account. Verifier infrastructure fault
returns the full prover bond. Witness authenticity remains a runtime premise.

## 3. Bounded Model

### Normal lane

```text
PostedPayment
  = min(
      benchmark + ceil(benchmark * risk_margin_bps / 10000),
      buyer_prefund_cap,
      buyer_value_cap,
      direct_execution_cap
    )
```

The benchmark is lagged, source-pinned, robustly aggregated, and bounded in its
epoch-to-epoch movement. Current-round acceptances are absent from the formula.
A no-acceptance round leaves the posted price unchanged.

The assignment transcript is ordered:

```text
beacon commitment
-> sealed acceptance commits and reveals
-> frozen acceptor, owner, domain, and capacity root
-> unpredictable beacon reveal
-> domain-separated 256-bit words
-> rejection-sampled unbiased ticket in [0, total_capacity)
-> canonical provider-order assignment
```

Providers cannot commit the same capacity to overlapping jobs, and aggregate
capacity must fit the declared integer range. Rejected words require a fresh
domain-separated beacon/XOF word. A publicly known seed before the acceptor set
freezes permits selective reveal and alias-order manipulation. The current model
proves only aggregate owner weight over a full uniform ticket cycle. It does not
implement the prior 20% permissionless floor,
20% owner canary cap, or failure-domain bucket. Those controls remain candidates
for a dedicated assignment-mechanism tournament before selection.

### Scarcity lane

```text
require JobCap <= OriginalPostedPayment

eligible_bid = lowest positive sealed bid <= JobCap, if any
eligible_direct = DirectExecutionOpportunityCost <= JobCap

if eligible_bid and eligible_direct:
    choose min(eligible_bid, DirectExecutionOpportunityCost)
    choose direct execution on an exact tie
else if eligible_bid:
    assign bidder; pay own bid
else if eligible_direct:
    execute directly
else:
    reject unfunded before accepting the job
```

The same occurrence cannot raise its cap after a no-acceptance round. An exact
single-provider search over posted prices, costs, caps, direct costs, and late
bids from zero through five finds no strictly profitable stage-withholding
deviation when normal assignment is certain and the normal and late lanes have
identical compute, capital-lock, opportunity, bonus, and information costs.
Different assignment probabilities or lane costs, multi-provider behavior,
coalitions, repeated play, and future benchmark manipulation remain open.

For an internal ZRPF job, admission requires funded direct capacity. Market
failure reduces scaling throughput and cannot authorize an invalid transition.

### Critical lane

A critical job may procure a primary plus standby:

```text
ExpectedCost
  = Pr(primary_success) * primary_payment
  + standby_reservation_payment
  + Pr(primary_fault) * primary_to_standby_delay_loss
  + Pr(primary_fault and standby_success) * standby_activation_payment
  + Pr(primary_fault and standby_fault) * (
      direct_execution_opportunity_cost
      + residual_delay_loss
    )
  + expected_verifier_and_publication_attempt_costs
  - expected_enforceable_restitution
```

The standby must retain enough residual time to finish after activation. A
different measured domain limits a named common-mode class. Empirical
correlation bounds remain required. The contract must separately name any
payment due for an unsuccessful standby attempt; the displayed expression
assumes activation payment follows standby success.

### Entry and distribution lane

The 30M-ZDEX reserve supports early distribution and contestability through:

- verified useful protocol-selected work;
- qualification and reproducible benchmark jobs;
- bounded random audits and duplicate proofs;
- newly measured capacity or failure domains;
- public-good proofs with exact sponsor and `EconomicWorkKey` terms.

Every payout uses one `EconomicWorkKey` nullifier, a job cap, an owner/epoch cap,
beneficial-owner evidence, an unrelated-party classification, and a declining
reserve balance. That key closes exact canonical duplicates in the reference
subject; semantic-equivalence admission remains open. The reserve pays no raw bid,
wallet, request, or unverified compute metric. The Python reference and bounded
ESSO lifecycle now include an immutable one-job claim transition: an eligible
exact key consumes the bonus from both declining caps and is recorded once; a
repeated key is rejected by the terminal guard. The Python reference tests the
canonical encoding, while the ESSO model uses one bounded claim-bit and carries
no key bytes. Runtime parity, semantic-equivalence admission,
marginal-contribution, and contestability allocation remain open
mechanism-design work.

## 4. Evidence Lane

### Exact enumerator

The V2 Python core exhaustively checks three fixed bidders, costs and reports
from `0` through `reserve+1`, and a reserve of `5`:

```text
unilateral deviation queries: 7,203
truthful IR queries:           1,029
profitable truthful deviation: none
truthful IR violation:         none
```

This is finite evidence for reverse critical-price procurement under fixed
identities and a bidder-independent threshold. It is a control theorem, rather
than the selected launch mechanism.

Named counterexamples remain executable for first-price shading,
critical-price collusion, address-count diversity, fixed-seed alias ordering,
public-clock waiting, and the V1 floor defect.

### Lean

`Proofs/ZenoProofProcurementGameV2.lean` compiles restricted theorems for:

- truthful weak dominance under an own-report-independent critical threshold;
- truthful winner individual rationality;
- first-price and critical-price-coalition counterexamples;
- aggregate capacity-ticket weight preservation under an attributed split;
- same-occurrence scarcity-payment non-uplift under a nonincreasing cap;
- the three-prover stationary equal-share cartel boundary;
- full default-bond disposition conservation through an actual disposition
  structure.

The theorem assumptions are stated in the source and evidence receipt. There
are no placeholders in the file.

### ESSO

The repaired V2 ESSO lifecycle passes 14 of 14 inductive queries with Z3 4.15.4
and CVC5 1.1.2 agreement. It covers buyer and seller-bond conservation, no
automatic price ratchet, seller-payment non-uplift, witness-before-payment,
direct-lane binding, one `OccurrenceKey` payment claim, witnessed prover-fault
slash, mutually exclusive prover/verifier adjudication, and full verifier-fault
return. The exact report and bundle result are retained and source-pinned; a
stale receipt or missing result does not pass the packet checker.

The Python reference and ESSO model now check the same bounded reserve-aware
terminal transition. A successful verified seller-payment commit atomically
debits reserve and owner/epoch caps, records the bounded work-key claim, and
commits base payment and bond return. A second terminal commit is unreachable;
the 14-query receipt covers this one-job claim-bit model. Runtime mounting,
canonical key encoding, multi-job claim-set behavior, and crash-safe external
commit remain open.

The first model failed. Both solvers found that direct payment could be applied
from a `DirectPending` state whose lane was not `DIRECT`. Requiring the exact
lane repaired the counterexample. Only the legacy hashes survive for this
mutant, so its negative evidence is explicitly marked hash-only.

A second named mutant removed the prover-fault-witness guard. Both solvers found
a transition that fully slashed a prover while the witness remained absent.
Restoring the verifier-created, occurrence-bound witness guard repairs it. This
older mutant is also retained as hash-only evidence.

A third mutant permits `verify_submitted_work` after the verifier has created a
prover-fault witness. Both solvers produce the same `sat` adjudication-race
counterexample. An exclusive `ProverFaultWitnessed` typestate, reciprocal
witness guards, and claim/settlement guards repair it. The mutant source, failed
report, failed bundle, repaired report, and repaired bundle are retained with
exact hashes.

### TheoremSearch and primary-source review

TheoremSearch was used only to retrieve theorem shapes and breaker literature.
The useful lead was coalition-proof reverse VCG under specialized
supermodularity conditions. ZenoProof has not established those premises.

Reviewer summaries, exact URLs, access dates, source-status metadata, and claim
limits are recorded in `PROOF_MARKET_PRIMARY_SOURCE_MANIFEST_V2.json`. The
versionless pages were not content-snapshotted, so they remain advisory mutable
evidence.

Primary lessons:

- [Boundless auction documentation](https://docs.boundless.network/developers/tutorials/auction)
  uses a public rising requester price, first lock, and a default disposition
  split between burn and secondary-prover bounty. V2 removes the public clock
  from the normal lane and defines bond restitution in the shared lifecycle.
- [Boundless Proving Node v2.0](https://github.com/boundless-xyz/boundless/releases/tag/v2.0.0)
  reports that a database rewrite removed an approximately 30% cluster penalty;
  its predecessor achieved approximately 99.6% lock fulfillment and lost 25 ZKC
  after two failed locks. Software reliability is an explicit supply variable
  in the ZenoProof simulation plan. A collateral-driven exit response is an
  inference to test.
- [Proo-phi v5](https://arxiv.org/html/2404.06495v5) proves user-value DSIC,
  prover unit-cost DSIC, and budget balance for its homogeneous single-round
  core under declared assumptions. Capacity reports, repeated play, Sybils, and
  all-prover monopoly remain outside that theorem.
- Succinct's official [architecture](https://docs.succinct.xyz/docs/protocol/spn/architecture),
  [auction](https://docs.succinct.xyz/docs/protocol/spn/auction), and
  [lifecycle](https://docs.succinct.xyz/docs/protocol/spn/lifecycle) pages
  respectively describe an off-chain auctioneer with ephemeral proof-request
  data, reverse-auction selection with retries, and multi-factor prover scoring.
  Documented scoring discretion and stake-capacity coupling are attack surfaces
  and supply no ZenoProof proof premise.
- [Gevulot Firestarter](https://docs.gevulot.com/gevulot-docs/firestarter/overview)
  is described by its official documentation as permissioned. Its
  [permissionless ZkCloud allocation](https://docs.gevulot.com/gevulot-docs/zkcloud-design/execution-guarantees)
  page is official design documentation using qualified VRF assignment; it
  supplies no deployment evidence. Capacity-weighted tickets are a ZenoProof
  experiment with no deployed-Gevulot claim.
- Brevis ProverNet's official [auction documentation](https://provernet-docs.brevis.network/provernet-architecture/the-proof-marketplace/request-auction.html)
  supplies a commit/reveal procurement comparator. Its
  [staking page](https://provernet-docs.brevis.network/user-tutorial/staking-in-provernet.html)
  and [mainnet announcement](https://blog.brevis.network/2026/01/06/brevis-provernet-mainnet-and-brev-are-live/)
  conflict on current slashing status, so neither supplies a slashing premise.

The unpreserved raw TheoremSearch outputs had SHA-256 identities:

```text
truthfulness query: e6be65954d84ca557db7f434d159682a1d5f5931d344277f9f7a3e2d3de1fac2
breaker query:      5ab47ca82fe52cec0ebc320696ed5466d6b8457bbd8f0f3729ea6a53127232a9
```

They are orphaned, unverifiable hash notes because the underlying outputs were
not preserved. They carry no replay or proof status. Their useful adjacent lead
was [Karaca et al., arXiv:1711.06774v5](https://arxiv.org/abs/1711.06774v5),
originally submitted on 2017-11-17; its coalition result uses specialized
supermodularity premises that have not been transferred to discrete ZenoProof
jobs.

## 5. Promotion Boundary

The following claims are supported for the exact bounded subject:

- V1's saved payment is below its own auction minimum in two scenarios.
- V1 public-clock winners have profitable unilateral waiting deviations.
- V1 full-loss pricing and V1 half-restitution ESSO semantics disagree.
- A fixed critical-price threshold is unilaterally truthful and individually
  rational in the declared single-parameter model.
- The same critical-price family has an exact coalition failure, while a
  separate witness refutes address count as owner-diversity evidence.
- Posted price is independent of current-round acceptance in the declared
  formula.
- Capacity-ticket owner weight is equal over a complete uniform seed cycle under
  a capacity-preserving attributed split; fixed-seed split invariance is false.
- A same-occurrence late-capacity lane with a nonincreasing cap has no strict
  single-provider withholding gain in the declared bounded search when normal
  assignment is certain and lane costs are equal.
- The bounded V2 lifecycle conserves escrow and bond value and keeps direct
  fallback on its typed lane.
- The bounded Python/ESSO reserve transition consumes one exact work key once
  and rejects duplicate terminal claims without changing reserve state.

Open production evidence includes:

- authenticated workload cycles and resource vectors;
- cost, latency, failure, correlation, capital, and demand distributions;
- benchmark construction and manipulation resistance;
- capacity attestation and non-overcommitment;
- beneficial-owner, related-party, and failure-domain evidence;
- unpredictable unbiased beacon construction and frozen acceptor-root timing;
- permissionless-floor, owner-cap, and domain-bucket assignment policy;
- semantic-equivalence admission or a closed task registry for reserve bonus
  deduplication;
- entry elasticity, concentration, boycott, and bid-rotation telemetry;
- stable-fee revenue sufficiency and direct-execution runway;
- mounted reserve-aware terminal settlement with atomic reserve/payment/claim
  composition;
- canonical Rust transition, codec, ZenoLedger mount, crash recovery, and
  direct/ZRPF parity;
- testnet and shadow-market histories under adversarial entry and exit.

This packet establishes no mechanism that is simultaneously truthful,
efficient, budget-balanced, permissionless, false-name-proof, and
coalition-proof under arbitrary repeated play. The launch objective is narrower:
bound extraction, pay useful verified work, preserve contestability, and keep
correctness safe when the market fails. The packet is a current leading
experiment and remains unselected.

Promotion flags remain:

```text
selected = false
implemented = false
mounted = false
production_ready = false
```
