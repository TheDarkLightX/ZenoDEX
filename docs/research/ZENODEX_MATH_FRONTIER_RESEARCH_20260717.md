---
title: ZenoDEX Mathematics Frontier Research, July 17 2026
type: research-report
status: evidence-first candidate
base_commit: 44d7f0d2a36b2141b553af1df734926c9d559bca
---

# ZenoDEX Mathematics Frontier Research

**Date:** 2026-07-17  
**Repository baseline:** `44d7f0d2a36b2141b553af1df734926c9d559bca`  
**Research branch:** `agent/zenodex-math-frontier-20260717`  
**Scope:** spot CPMM arithmetic, exact-out many-pool routing, uniform batch clearing, mechanism-design claims, MEV bounds, fee mathematics, and LP-value objectives.

## Executive finding

ZenoDEX already has unusually broad arithmetic coverage: exact integer swap semantics, fee and rounding identities, per-pool exact-out minimality, finite-domain optimizer certificates, bounded UPBA economic-loss policies, and several nontrivial concavity and anti-fragmentation results. The central weakness is no longer the absence of local lemmas. It is the distance between local lemmas and the global claims users actually care about:

1. **The exact-out many-pool router proves canonical optimality only over a reconstructed bounded candidate domain.** It does not yet certify global optimality over every feasible integer allocation.
2. **UPBA optimality is finite-grid and fixed-admission optimality.** The current policies bound discretization loss, but do not turn the selected finite surface into unbounded economic or mechanism-design optimality.
3. **Some mechanism terminology is stronger than the theorem.** Binding commit-reveal proves post-commit non-adaptivity. It does not prove that the value chosen before commitment was truthful.
4. **K-monotonicity is not LP welfare.** A pool can preserve or increase its product invariant while LPs still lose to informed flow relative to a rebalancing benchmark.
5. **Gas and activation costs are constraints in the present router, not part of its economic objective.** The frontier formulation is mixed-integer and has explicit activation/no-trade conditions.
6. **The strongest missing proof style is proof-carrying optimization.** ZenoDEX should let an untrusted solver propose a route or clearing outcome, then accept it only when a small dual certificate proves a global lower bound and an explicit primal-dual gap.

The strongest new mathematical result in this research packet is a **sub-one-atom primal-dual certificate** for exact-out routing. Because every executable route cost is an integer number of input atoms, a rational dual lower bound less than one atom below the candidate cost already proves exact global optimality. This is stronger and easier to satisfy than requiring zero continuous duality gap.

## Evidence discipline

This report separates four evidence levels:

- **Repository fact:** directly read from the baseline source, theorem, audit, or runtime implementation.
- **Machine-checkable theorem candidate:** Lean source added in this branch. It is authoritative only when exact-head CI typechecks it with the pinned Lean/mathlib toolchain.
- **Derived design:** follows mathematically from proved ingredients but is not yet wired to settlement authority.
- **Research hypothesis:** promising frontier direction requiring a new theorem, model validation, or empirical calibration before promotion.

No result in this report promotes network, admission, oracle, or solver trust beyond the precise theorem surface stated.

## 1. Current mathematical assurance map

| Surface | What is strong today | Remaining boundary |
|---|---|---|
| CPMM exact-in arithmetic | Exact fee, floor-rounding, reserve, and K identities are extensively formalized. | Local safety does not imply route optimality, fair ordering, or LP welfare. |
| CPMM exact-out arithmetic | The v8 nested-ceiling quote has per-pool sufficiency and minimality proofs. | Many-pool global allocation optimality remains candidate-domain scoped. |
| Exact-out many-pool routing | Runtime reconstructs and audits a deterministic candidate stream, checks caps, route identities, quote totals, and canonical keys. | Pool selection and allocation enumeration are bounded; fallback paths are heuristic; global generator completeness is not proved. |
| Exact-in split routing | ZenoDEX has exact and approximate zero-fee split certificates, including floor-of-concave envelopes. | Fee-aware runtime exact-in routing and arbitrary multi-hop composition need their own certificate surface. |
| UPBA v1/v2/v3 | Finite grid/fill surfaces are explicit; winner dominance is checkable; economic epsilon policies bound configured discretization loss. | No unbounded rational completeness, admission fairness, oracle truth, or general exact-out/multi-hop theorem. |
| Uniform batch clearing | Narrow single-pool uniform-price settlement, deterministic tie-breaking, and bounded candidate scoring exist. | Full game-theoretic incentive compatibility requires a complete utility/type model plus sequencing/admission assumptions. |
| Commit-reveal | Binding and deterministic reveal semantics remove post-deadline adaptation. A narrow fixed-output `min_out` theorem is valid. | Binding does not imply truthful pre-commit reporting or coalition resistance. |
| Fee anti-fragmentation | ZenoDEX already proves ceiling-fee subadditivity, net-input superadditivity, two-part fee-aware anti-fragmentation, and batch K-gap telescoping. | Convert the binary theorem into the exact runtime list/state model and expose it as a settlement/reviewer certificate rather than relying on bounded order enumeration. |
| MEV | Several local no-profit and ordering results exist, with explicit nonclaims. | Multi-step optimal adversary bounds and inclusion/exclusion attacks require an adversary-language maximum theorem. |
| LP economics | K never decreases under the proven fee-aware swap model. | K is not LVR, hedged P&L, toxic-flow loss, or capital efficiency. |

### Primary repository boundaries

The most important baseline documents and theorem packets are:

- `docs/zenodex/DEX_ALGORITHM_AUDIT_V1.md`
- `docs/UPBA_OPTIMALITY_CERTIFICATE.md`
- `docs/UPBA_ECONOMIC_SUFFICIENCY_V1.md`
- `docs/UPBA_V2_ECONOMIC_SUFFICIENCY_V1.md`
- `docs/UPBA_V3_EXACT_OUT_CERTIFICATE.md`
- `src/core/split_routing_dispatch.py`
- `src/core/uniform_batch_clearing.py`
- `src/core/cpmm.py`
- `src/kernels/python/cpmm_swap_v8.py`
- `lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean`
- `lean-mathlib/Proofs/ZenoDEXExactOutManyPoolCandidateDomainContract.lean`
- `lean-mathlib/Proofs/ZenoDEXExactOutManyPoolCpmmQuoteTotality.lean`
- `lean-mathlib/Proofs/CPMMConcavity.lean`
- `lean-mathlib/Proofs/CPMMSandwichCertificate.lean`
- `lean-mathlib/Proofs/MobiusCPMMRoutingBounds.lean`
- `lean-mathlib/Proofs/FeeAwareAntiFragmentation.lean`
- `lean-mathlib/Proofs/FeeAwareBatchKGap.lean`
- `lean-mathlib/Proofs/CommitRevealStrategyproof.lean`
- `lean-mathlib/Proofs/CommitRevealBothParamsSP.lean`

## 2. Breakthrough 1: global exact-out optimality without enumerating every allocation

### Status

**Lean theorem candidate plus implementable design.** The abstract weak-duality theorem, additive-gap theorem, sub-one-atom integrality lift, continuous CPMM tangent identity, rational common-slope normalization, runtime nested-ceiling lower bridge, and a counterexample to false discrete convexity are added in:

`lean-mathlib/Proofs/ZenoDEXExactOutDualCertificate.lean`

### Problem

For pools `i = 1,...,n`, let `q_i` be output atoms allocated to pool `i`, with:

```text
sum_i q_i = Q
0 <= q_i <= cap_i
```

Let the exact executable gross-input quote be:

```text
G_i(q) = ceil(
             ceil(x_i * q / (y_i - q)) * 10000
             / (10000 - fee_bps_i)
           )
```

The global integer problem is:

```text
minimize   sum_i G_i(q_i)
subject to sum_i q_i = Q
           0 <= q_i <= cap_i
           q_i integer
```

The current runtime finds candidates through selected-pool and bounded-allocation machinery. Its certificate can prove the winner is canonical inside that emitted domain, but not that no feasible allocation omitted by the generator is cheaper.

### Dual certificate

Suppose a certificate gives a common rational slope `lambda` and, for every pool, a rational intercept `b_i` satisfying:

```text
b_i + lambda * q <= G_i(q)
```

for every feasible `q` in that pool. Then every feasible route satisfies:

```text
sum_i G_i(q_i)
  >= sum_i (b_i + lambda * q_i)
   = sum_i b_i + lambda * Q
   = L
```

`L` is a global lower bound, independent of how the target is allocated. Let the proposed executable route cost be `U`. Then:

```text
0 <= OPT - L <= U - L
```

so `U - L` is a machine-checkable additive suboptimality certificate.

### Integrality lift: less than one atom proves exactness

Every executable route cost is an integer. Therefore:

```text
U < L + 1 atom
and
L <= every alternative integer cost
```

imply:

```text
U <= every alternative cost.
```

This is the key result. The verifier does **not** need a zero-gap continuous certificate. A lower bound within strictly less than one input atom of the candidate proves exact global integer optimality.

This changes the engineering tradeoff. The solver may use floating point, Newton steps, convex optimization, or heuristics to find a candidate and a nearly tight dual. Settlement trusts only exact rational arithmetic and the `< 1 atom` check.

## 3. Breakthrough 2: an exact square identity supplies continuous CPMM lower bounds

For one CPMM with input reserve `x`, output reserve `y`, fee denominator `d = 10000 - fee_bps`, and requested output `q`, define the continuous relaxation:

```text
c(q) = x * 10000 * q / (d * (y - q)).
```

Its derivative at anchor `a` is:

```text
s(a) = x * 10000 * y / (d * (y - a)^2).
```

The exact tangent gap is:

```text
c(q) - [c(a) + s(a)(q-a)]
  = x * 10000 * y * (q-a)^2
    / [d * (y-a)^2 * (y-q)].
```

On the valid domain `x >= 0`, `y > 0`, `d > 0`, `a < y`, and `q < y`, the right side is nonnegative. Thus every tangent is a global affine lower bound.

This identity is better for high assurance than invoking a generic differentiable-convexity library:

- it reduces soundness to a rational identity and sign checks;
- it avoids numerical Hessian tests;
- it can be checked after cross multiplication;
- it remains small enough for a ZK guest or Tau-side verifier;
- it exposes exactly which denominator and reserve conditions are required.

## 4. Breakthrough 3: rational common-slope normalization avoids irrational KKT anchors

At a continuous optimum, active pools equalize marginal cost, but solving

```text
s_i(a_i) = lambda
```

can introduce square roots. Settlement should not have to trust irrational approximations.

The new Lean packet proves a bounded-domain normalization lemma. Start from any rational tangent:

```text
t_i(q) = alpha_i + s_i q <= c_i(q)
```

on `0 <= q <= cap_i`. For any rational common slope `lambda`, define:

```text
b_i = alpha_i                              when lambda <= s_i
b_i = alpha_i + (s_i - lambda) * cap_i    when s_i < lambda.
```

Then throughout the bounded domain:

```text
b_i + lambda q <= alpha_i + s_i q <= c_i(q).
```

Consequences:

1. Every field in the certificate can be rational and canonically serialized.
2. The solver may choose rational anchors near the continuous optimum.
3. The verifier needs only interval bounds, rational multiplication, and ordering.
4. Tightness can be improved incrementally without changing soundness.

This is a practical bridge from KKT intuition to proof-carrying integer routing.

## 5. Breakthrough 4: the exact v8 nested-ceiling quote dominates the continuous cost

The runtime v8 exact-out quote first ceilings the net input and then ceilings the gross input after fees. The new theorem proves, in exact natural arithmetic:

```text
reserveIn * amountOut * 10000
  <= grossInRequiredV8
     * (10000 - feeBps)
     * (reserveOut - amountOut).
```

Under positive denominators, this is exactly:

```text
continuous cost <= executable nested-ceiling gross cost.
```

Therefore a continuous affine lower bound is also a lower bound on the actual integer runtime quote. This closes the crucial soundness bridge between convex relaxation and executable semantics.

The direction matters. A continuous route is not executable evidence, but a continuous **lower bound** can safely support an integer optimality certificate when the candidate itself is re-quoted by the exact kernel.

## 6. Breakthrough 5: exact-out integer costs are not discretely convex

A tempting design would prove monotone forward marginal costs and certify a route with local one-atom exchange checks. That theorem is false for the runtime nested-ceiling quote.

The Lean packet includes the concrete witness:

```text
reserveIn = 1
reserveOut = 4
feeBps = 0

G(0) = 0
G(1) = 1
G(2) = 1
```

The forward differences are:

```text
G(1)-G(0) = 1
G(2)-G(1) = 0.
```

They decrease, violating discrete convexity. This is not a cosmetic edge case. It invalidates a whole class of local-marginal exactness arguments unless an instance-specific discrete-convexity certificate is supplied.

The correct architecture is therefore:

- use continuous convex structure for global lower bounds;
- use exact integer quotes for the primal route;
- use the rational primal-dual gap for assurance;
- optionally use local integer exchange checks only as extra diagnostics.

## 7. Breakthrough 6: commit-reveal must be classified as non-adaptivity, not truthfulness

### Status

**Lean theorem candidate and claim correction.** Added in:

`lean-mathlib/Proofs/CommitRevealIncentiveCompatibilityBoundary.lean`

### Finding

`CommitRevealBothParamsSP.lean` is commendably explicit in its prose that a commitment does not force truthful reporting. However, theorem names and summaries still use “strategyproofness” for a result whose crucial hypothesis is:

```text
min_out_reported = min_out_true.
```

That hypothesis assumes away the deviation that truthful strategyproofness must compare. The main reflexive theorem is mathematically valid, but its proper interpretation is:

```text
binding commitment
  -> accepted reveal equals committed report
  -> no post-commit adaptive change.
```

It does not establish:

```text
truthful pre-commit report
  >= utility from every strategic pre-commit report.
```

The new Lean file proves:

1. two accepted reveals for one binding commitment induce the same deterministic outcome;
2. assuming `reported = truthful` makes a no-profitable-deviation comparison reflexive;
3. a constructive utility model can satisfy binding while a pre-commit misreport is strictly more profitable;
4. therefore binding does not imply truthful strategyproofness.

### What remains valid

The separate `CommitRevealStrategyproof.lean` theorem for `min_out` is meaningful under its stated one-dimensional model, because output is assumed independent of the reported threshold and utility is explicitly defined. It should remain scoped to that model. It does not automatically lift to strategic `amount_in`, endogenous output, admission effects, coalitions, or cross-batch behavior.

### Promotion rule

Use these terms precisely:

- **binding:** reveal equals prior commitment;
- **hiding:** report is unavailable before reveal;
- **post-commit non-adaptivity:** accepted report cannot change after commitment;
- **individual incentive compatibility:** truthful reporting maximizes one user's utility over all reports, under a complete environment model;
- **group strategyproofness / coalition resistance:** no coalition plus side payments can improve jointly;
- **MEV resistance:** no permitted ordering, inclusion, or exclusion strategy exceeds the declared adversary value bound.

None of the last three follows from binding alone.

## 8. Breakthrough 7: fee-aware anti-fragmentation can replace bounded permutation reasoning

The 2026 formal-methods literature proves, in Lean over a fee-adjusted real CPMM model, a generalized additivity law: with a positive trading fee, a single large same-direction swap yields strictly greater gain than splitting it into sequential smaller swaps. ZenoDEX independently contains a stronger runtime-oriented integer foundation:

- ceiling division is subadditive;
- split ceiling fees are no smaller than the combined fee;
- combined net input is superadditive;
- zero-fee output is anti-fragmenting;
- two-part fee-aware output is anti-fragmenting;
- fee-aware batch K-gaps telescope by list induction.

The missing production move is not to rediscover the theorem. It is to connect the existing binary anti-fragmentation theorem to the exact runtime batch state machine by induction, then expose a compact certificate:

```text
combined same-direction output
  >= sequential fragmented output
```

for arbitrary list length under the exact fee and rounding kernel.

This would let reviewers distinguish two concerns currently entangled in batch reasoning:

- **economic fragmentation:** whether splitting a same-direction amount improves aggregate output;
- **canonical order:** which deterministic ordering is chosen when user-level limits and surplus tie-breaks matter.

Anti-fragmentation can be unbounded in list length even when full `A/B/lex` order enumeration remains deliberately bounded.

## 9. Breakthrough 8: gas-aware routing needs activation variables and no-trade certificates

The frontier routing literature models fixed per-pool execution costs with binary activation variables. The economic objective is not merely:

```text
min sum_i G_i(q_i)
```

but:

```text
min sum_i [G_i(q_i) + z_i * gasCost_i]
subject to q_i <= z_i * cap_i
           z_i in {0,1}.
```

ZenoDEX currently uses limits such as `max_legs` and selected-pool caps. Those control complexity, but they do not prove that activating another pool is economically worthwhile.

The next certificate format should include:

- a route activation bit for every admitted pool or path;
- a governed conversion from gas/resource units into the objective token;
- a fixed activation charge or conservative interval;
- per-pool no-trade inequalities for inactive pools;
- a mixed-integer primal cost;
- a relaxed dual lower bound and explicit integrality/activation gap.

A safe staged design is:

1. certify global token-input optimality with gas excluded;
2. separately certify an upper bound on settlement resources;
3. introduce a governed gas-to-token interval;
4. certify the route remains optimal for every conversion rate in that interval;
5. fail closed when the interval is too wide to distinguish routes.

This avoids embedding a manipulable spot gas oracle directly into consensus-critical arithmetic.

## 10. Breakthrough 9: UPBA should search economic events, not an arbitrary rectangular grid

Current UPBA policies are honest and useful: they prove finite-domain winner optimality and bound configured price/fill quantization loss. Their computational surface still scales as a product of price rows and fill vectors.

A stronger candidate-generation theorem would derive an **event-complete set** from the piecewise structure of the scorer. Candidate events include:

- every admitted limit-price boundary;
- every price at which an intent changes fill eligibility;
- pool marginal-price or clearing-balance roots;
- fill-quantum transition points;
- domain endpoints;
- exact tie-breaking neighbors induced by integer rounding.

Between adjacent events, the active intent set and rounding regime are fixed. If the objective can be proved monotone, convex, concave, or otherwise extremized at a boundary within each cell, only event points and certified interior stationary points need evaluation.

This can change the assurance claim from:

```text
best on a governance-selected grid
```

into:

```text
best over every economically distinct regime admitted by the fixed intent set.
```

This is a research hypothesis, not yet a theorem. The first proof target should be the narrow v1 full-fill, single-pool exact-in scorer. It should not be generalized to v2 partial fills until the event partition for fill quantization is formalized.

## 11. Breakthrough 10: MEV assurance should maximize over an adversary language

The frontier Lean work on MEV frames safety as an upper-bound problem: define the permitted adversarial strategy space and prove no strategy exceeds a stated value. This is a better fit for ZenoDEX than isolated “sandwich resistant” labels.

Recommended object:

```text
AdversaryProgram :=
  bounded sequence of include / exclude / order / insert / route actions
```

with explicit resources:

```text
max inserted trades
max capital
max flash liquidity
max paths
max blocks or batches
oracle and finality assumptions
```

Then define:

```text
MEV(program) = attacker final marked value - initial marked value - costs
```

and prove or certify:

```text
sup over admitted programs MEV(program) <= declaredBudget.
```

The immediate formal target is a three-leg CPMM sandwich under the exact fee and floor kernel, followed by a theorem that uniform batch settlement removes the attacker's intra-batch ordering degree of freedom under fixed admission. Inclusion/exclusion and cross-batch timing must remain separate.

This turns “MEV resistance” from a design adjective into an auditable optimization problem.

## 12. Breakthrough 11: K safety and LP welfare need separate certificates

ZenoDEX's K-gap theorems are valuable accounting invariants. They prove reserve-product behavior under exact fee and rounding semantics. They do not prove that LPs outperform holding or continuously rebalancing the same inventory.

The LVR literature shows that LP loss depends on price variance and marginal liquidity, and recent work treats the fee as a control variable balancing uninformed-volume revenue against adverse-selection extraction and a no-arbitrage band.

A high-assurance dynamic fee controller should therefore be split into:

### Pure proposal function

Inputs:

```text
volatility interval
oracle-confidence interval
pool marginal-liquidity interval
recent uninformed-volume interval
gas/dead-band policy
fee bounds and rate-of-change bounds
```

Output:

```text
proposed fee interval or discrete fee tier
```

### Deterministic admission checker

Checks:

- all inputs are fresh, quorum-backed, and bounded;
- fee remains inside governance limits;
- rate of change is bounded;
- worst-case trader slippage and LP-loss budgets are respected across the input intervals;
- the controller fails closed to a safe static fee if uncertainty is too large.

### Proof target

Do not initially prove that the fee is globally economically optimal. Prove the smaller high-assurance statement:

```text
for every state inside the certified uncertainty box,
selected fee satisfies the declared loss, slippage, and stability guardrails.
```

The stochastic-control optimum can remain a proposer heuristic until its market assumptions are validated for each pool class.

## 13. Proposed exact-out certificate schema

A production packet should be self-contained and kernel-replayable.

```text
ExactOutDualCertificateV1 {
  schema_id
  kernel_id
  pool_set_hash
  target_output_atoms

  pools[] {
    pool_id
    reserve_in
    reserve_out
    fee_bps
    cap_out
    state_fingerprint
  }

  candidate[] {
    pool_id
    amount_out
    exact_gross_in
  }

  common_slope_num
  common_slope_den

  lower_bounds[] {
    pool_id
    anchor_out_num
    anchor_out_den
    tangent_slope_num
    tangent_slope_den
    normalized_intercept_num
    normalized_intercept_den
  }

  dual_lower_num
  dual_lower_den
  candidate_cost_atoms
  gap_num
  gap_den

  claim_kind: EXACT_IF_GAP_LT_ONE | ADDITIVE_GAP
}
```

Verifier steps:

1. Bind the packet to the exact pool state and kernel identity.
2. Recompute candidate feasibility and `sum amount_out = target`.
3. Recompute every exact nested-ceiling quote.
4. Verify each rational anchor is within the pool domain.
5. Verify the tangent square identity or its cross-multiplied lower-bound form.
6. Verify common-slope normalization over `[0, cap]`.
7. Sum the intercepts and `lambda * target` to recover the dual lower bound.
8. Recompute the rational gap.
9. Authorize `EXACT` only when `0 <= gap < 1` input atom.
10. Otherwise expose the additive gap and let policy decide whether it is acceptable.

The solver is untrusted. Floating-point output is never accepted directly. Every accepted field is rechecked with bounded exact integer or rational arithmetic.

## 14. Implementation sequence

### P0: claim correctness and proof kernel

- Merge the commit-reveal incentive-compatibility boundary theorem.
- Deprecate “strategyproof” wording for the both-parameters reflexive theorem while retaining legacy theorem names if compatibility requires them.
- Merge the exact-out dual certificate theorem packet after exact-head Lean CI is green.
- Add both files to the formal-proof hygiene allowlist/ratchet.

### P1: certificate generator and verifier

- Implement a pure Rust or Python reference generator that reads immutable pool snapshots and candidate routes.
- Generate rational anchors, a rational common slope, normalized intercepts, and the gap.
- Implement an independent small verifier using only exact arithmetic.
- Differentially test it against exhaustive enumeration on small domains.
- Add adversarial mutations for every certificate field.

### P2: runtime integration

- Keep existing bounded enumeration as one candidate generator.
- Add continuous/convex seeding as a second untrusted generator.
- Require the dual certificate for any global-optimality claim.
- Fall back to candidate-domain wording when `< 1 atom` cannot be proved.
- Bind the certificate hash into settlement and recursive proof receipts.

### P3: gas and activation

- Add activation bits and fixed costs.
- Prove no-trade conditions for inactive pools.
- Certify robust optimality over a governed gas-conversion interval.

### P4: UPBA event completeness

- Formalize the v1 scorer's event partition.
- Replace arbitrary dense price grids with event-complete candidates plus exact stationary-point certificates.
- Extend only after the fixed-admission v1 theorem is complete.

### P5: adversary and LP economics

- Define the bounded MEV adversary language and exact value function.
- Port the three-leg sandwich optimum proof to the runtime kernel.
- Add LVR/fee guardrail certificates with interval-valued market inputs.

## 15. Tests and falsifiers

A research result should be rejected or narrowed when any of these tests fail.

### Exact-out dual certificate

- Exhaustively enumerate all allocations for thousands of small random pool sets.
- Verify `dual <= true optimum <= candidate` for every case.
- Require `< 1` certificates to agree with exact enumeration.
- Mutate slope, intercept, cap, target, reserve, fee, and quote fields independently; every unsound mutation must fail.
- Include pools at cap, zero allocation, one-atom reserve margins, fee near 100%, and equal-cost ties.

### Discrete-convexity falsifier

- Preserve the `(1,4,0)` witness permanently.
- Search bounded domains for additional decreasing-forward-difference cases after every kernel change.
- Reject any optimizer proof that silently assumes monotone integer marginals.

### Mechanism claims

- For every “incentive compatible” claim, identify type space, report space, utility, admissible deviations, information timing, and sequencing assumptions.
- Generate a countermodel whenever a theorem assumes `report = trueType` rather than proving truthful dominance.
- Test coalitions with side payments separately from individual deviations.

### UPBA event completeness

- Differentially compare event candidates against dense rational grids and exact small-domain enumeration.
- Add a proof obligation that every objective-regime change appears in the event set.
- Keep a counterexample corpus for missed rounding and fill-quantum boundaries.

### Dynamic fees

- Backtest on held-out market regimes and stress synthetic jumps, oracle delay, and volatility estimator failure.
- Report both LVR and fee compensation; do not claim reduced LVR merely because LP net P&L improves.
- Require safe static fallback under stale or wide uncertainty intervals.

## 16. Literature synthesis

### Optimal routing and duality

1. Guillermo Angeris, Alex Evans, and Tarun Chitra, **Optimal Routing for Constant Function Market Makers**, arXiv:2204.05238. Establishes the convex-optimization formulation for CFMM routing without fixed activation costs and motivates KKT/dual verification.
2. Theo Diamandis, Ciamac C. Moallemi, Guillermo Angeris, and Alex Evans, **An Efficient Algorithm for Optimal Routing Through Constant Function Market Makers**, arXiv:2302.04938. Develops decomposition methods suitable for solver/verifier separation.
3. Carlos Escudero, Felipe Lara, and Miguel Sama, **Optimal Routing across Constant Function Market Makers with Gas Fees**, arXiv:2603.02844. Adds mixed-integer activation costs, KKT conditions, generalized-convex sufficiency, no-trade conditions, and relaxation bounds.
4. G. Goyal et al., **Finding the Right Curve: Optimal Design of Constant Function Market Makers**, arXiv:2212.03340. Treats curve design as an optimization problem rather than assuming CPMM is universally optimal.
5. Curry et al., **Optimal Automated Market Makers: Differentiable Economics and Strong Duality**, arXiv:2402.09129. Connects AMM mechanism design to differentiable optimization and duality.

### Batch mechanisms, MEV, and fair ordering

6. Conor McMenamin, Vanesa Daza, Matthias Fitzi, and Padraic O'Donoghue, **FairTraDEX: A Decentralised Exchange Preventing Value Extraction**, arXiv:2202.06384. Shows that frequent batch-auction guarantees depend on more than commitment alone, including escrow, zero-knowledge membership, and a defined game.
7. Andrea Canidio and Robin Fritsch, **Arbitrageurs' Profits, LVR, and Sandwich Attacks: Batch Trading as an AMM Design Response**, arXiv:2307.02074; AFT 2023 version **Batching Trades on Automated Market Makers**. Introduces function-maximizing batch AMMs and analyzes LVR/sandwich elimination under equilibrium competition assumptions.
8. T-H. Hubert Chan, Ke Wu, and Elaine Shi, **Mechanism Design for Automated Market Makers**, arXiv:2402.09357, revised 2025. Separates arbitrage resilience and fair treatment under legacy sequencing from stronger incentive compatibility under decentralized fair sequencing.
9. Marko Putnik and Jérémie Decouchant, **Herring: Parallel Batch-Order-Fairness on DAG-based Blockchain Consensus**, arXiv:2605.23648. Demonstrates that order fairness is a consensus-layer property with liveness and performance tradeoffs, not merely an AMM scoring rule.
10. Massimo Bartoletti, Riccardo Marchesin, and Roberto Zunino, **Certifying Optimal MEV Strategies with Lean**, arXiv:2510.14480. Formalizes MEV upper-bound reasoning and machine-checks sandwich optimality.

### Fees, anti-fragmentation, and LP economics

11. Marco Dessalvi, Massimo Bartoletti, and Alberto Lluch-Lafuente, **A Formal Approach to AMM Fee Mechanisms with Lean 4**, FMBC 2026, DOI 10.4230/OASIcs.FMBC.2026.4. Proves fee-adjusted monotonicity, generalized additivity, anti-fragmentation, and a unique arbitrage optimum in Lean.
12. Jason Milionis, Ciamac C. Moallemi, Tim Roughgarden, and Anthony Lee Zhang, **Automated Market Making and Loss-Versus-Rebalancing**, arXiv:2208.06046. Defines LVR and relates instantaneous loss to volatility and marginal liquidity.
13. Farbod Ghasemlu, **Optimal Dynamic Fees for Automated Market Makers: A Stochastic Control Approach to Loss-Versus-Rebalancing**, arXiv:2606.21769. Derives volatility-feedback fees and an impulse-control dead-band for gas costs.
14. Daniele Maria Di Nosse and Fabrizio Lillo, **Mitigating Adverse Selection in Concentrated Liquidity AMMs with Dynamic Fees: An Agent-Based Model Approach**, arXiv:2606.23070. Finds dynamic fees may compensate LVR more reliably than eliminate it, a crucial claim-discipline distinction.
15. Austin Adams, Ciamac C. Moallemi, Sara Reynolds, and Dan Robinson, **am-AMM: An Auction-Managed Automated Market Maker**, arXiv:2403.03367. Auctions temporary management rights to internalize informed-flow rents and adapt fees.

### Formal verification

16. Daniele Pusceddu and Massimo Bartoletti, **Formalizing Automated Market Makers in the Lean 4 Theorem Prover**, arXiv:2402.06064 / FMBC 2024. Mechanizes CPMM economic properties, including arbitrage.
17. Eske Hoy Nielsen, Danil Annenkov, and Bas Spitters, **Formalising Decentralised Exchanges in Coq**, CPP 2023. Demonstrates end-to-end formal DEX modeling and verified reasoning in Coq.
18. Mohit Garg and Suneel Sarswat, **The Design and Regulation of Exchanges: A Formal Approach**, FSTTCS 2022. Shows how natural exchange properties can characterize a mechanism and yield an extracted verified checker.
19. Natalia Klaus, Palina Tolmach, and Juan Conejero, **A Rust-to-Lean Verification Pipeline with AI Provers: An Experience Report**, arXiv:2605.30106. Supports a production architecture where Rust is extracted to Lean and all AI-generated proof terms remain kernel checked.

### Search tooling

TheoremSearch was inspected as a theorem-level semantic search and formal/informal graph resource. Its public documentation was useful for search framing, but the semantic query endpoint was not available through the execution environment, so no claim in this report depends on an unrecorded TheoremSearch result. Direct Research Kernel, Morph, and ESSO MCP namespaces were also unavailable in this session. The research therefore used repository-grounded proof inventory, primary papers, exact algebra, counterexample search, and Lean source submitted to the repository's own pinned CI lane.

## 17. Claim ledger

### Proved in existing ZenoDEX baseline

- Per-pool v8 exact-out quote sufficiency and minimality.
- Candidate-domain canonicality and substantial route-presentation contracts.
- Finite-grid/fill UPBA winner claims and configured epsilon budgets.
- Zero-fee exact-in floor-concavity approximation certificates.
- Fee ceiling subadditivity and binary fee-aware anti-fragmentation.
- Fee-aware batch K-gap telescoping.

### Added as Lean theorem candidates in this branch

- Generic affine weak duality for fixed-total separable routing.
- Additive primal-dual suboptimality bound.
- Zero-gap global optimality.
- Sub-one-atom exactness for integer objectives.
- Rational common-slope normalization over bounded pool domains.
- Continuous CPMM exact-out tangent square identity and lower bound.
- Exact v8 nested-ceiling quote lower-bounded by the continuous relaxation.
- Concrete failure of exact discrete convexity.
- Binding implies post-commit non-adaptivity.
- Binding does not imply truthful strategyproofness.

These become machine-checked repository evidence only after exact-head CI typechecks the files with no placeholders.

### Implementable but not yet wired

- `ExactOutDualCertificateV1` generator and verifier.
- `< 1 atom` global-optimality promotion rule.
- Arbitrary-list runtime anti-fragmentation certificate.
- Gas-aware activation/no-trade extension.

### Open research hypotheses

- Event-complete UPBA candidate generation for the full v1 scorer.
- Efficient event completeness for v2 partial-fill quantization.
- Full bounded-adversary MEV maximum for runtime settlement.
- Robust interval-certified dynamic fees that improve LP objectives without unacceptable trader harm.

## Conclusion

The best next mathematical architecture for ZenoDEX is **untrusted optimization with proof-carrying global bounds**: retain exact integer kernels for execution, let powerful solvers search freely, and authorize global-optimality claims only when a small rational dual certificate places the executable candidate within strictly less than one atom of a verified lower bound.
