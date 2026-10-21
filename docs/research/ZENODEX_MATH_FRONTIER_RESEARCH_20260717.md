# ZenoDEX mathematics frontier research report

**Date:** 2026-07-17  
**Repository baseline:** `main` at `44d7f0d2a36b2141b553af1df734926c9d559bca`  
**Research branch:** `agent/zenodex-math-frontier-evidence-20260717`  
**Evidence rule:** proved > contract > implemented > replayed test > hypothesis

## Executive verdict

ZenoDEX already has unusually strong local arithmetic and structural proof coverage. The highest-value mathematical gap is no longer another CPMM identity, another candidate curve, or another heuristic optimizer. It is the missing bridge from:

1. exact integer pool semantics,
2. a proposed route or batch,
3. canonical selection among submitted candidates,

into a proof that the accepted economic result is globally optimal over every feasible route or fill plan.

This run produced two formal artifacts and one bounded falsification artifact that change the routing strategy:

1. **Fee-aware gross-input CPMM output has no reserve-independent finite nearly-concavity grade.** The ceiling fee can create a first output jump of arbitrary size. Therefore, the zero-fee local-concavity theory cannot justify a production fee-aware unit-marginal greedy router.
2. **A solver-independent affine-envelope certificate can prove exact global output optimality.** Per-pool rational affine upper bounds sum to a global weak-duality bound. A strict one-output-unit gap certifies the winner without trusting the optimizer or requiring concavity.
3. **A concrete bounded counterexample shows why this matters.** For two identical pools with `(reserve_in, reserve_out, fee_bps) = (1, 7, 1)`, a tempting unit-at-a-time marginal-cost greedy allocation spends 6 gross units for output quota 6, while the globally exact `3 + 3` quota split spends 4.

The recommended architecture is therefore:

> Use continuous KKT, decomposition, mixed-integer active-set search, dynamic programming, or learned ranking only to propose candidates; use exact integer feasibility, affine or piecewise dual envelopes, and canonical tie-break proofs to authorize them.

This is a stronger design than either exhaustive search alone or a fast optimizer alone. Search produces speed. A small proof object produces authority.

## 1. Scope and evidence discipline

### 1.1 Scope

The run concentrated on spot execution mathematics because that is where the repository contains enough exact semantics and Lean infrastructure to support new theorems immediately. The active zUSD repair line in draft PR #443 is a separate stacked branch and is not treated as part of `main` authority in this report.

The inspected spot surfaces were:

- production CPMM fee and rounding semantics;
- two-pool and many-pool split routing;
- staircase and dynamic-programming optimizers;
- uniform batch clearing and UPBA v2 optimality certificates;
- fee anti-fragmentation and batch `k`-gap accounting;
- static curve trade-off theorems;
- proof enumeration, canonical winner, and residual-capacity modules.

### 1.2 Evidence labels

| Label | Meaning |
|---|---|
| `COMPILED_MAIN` | Existing theorem or gate compiled on the baseline branch. |
| `FORMAL_CANDIDATE` | New Lean statement and proof term committed, pending exact-head CI. |
| `REPLAYED_BOUNDED` | Deterministic executable evidence over a finite domain. |
| `IMPLEMENTED` | Runtime relation exists, but the strongest mathematical claim is not proved. |
| `HYPOTHESIS` | Research direction with an explicit falsifier and promotion gate. |

No report sentence upgrades a lower label into a higher one.

### 1.3 Tool boundary

The external Research Kernel, Morph, and ESSO MCP endpoints named in the research prompt were not exposed in this session. The run instead used:

- the repository's retained Research Kernel-style memory under `experiments/math_research_memory/`;
- deterministic bounded falsification committed as a replayable tool and retained JSON;
- the public TheoremSearch corpus and API documentation for theorem-level retrieval orientation;
- repository-native Lean proof artifacts and exact-head CI as the compilation authority;
- primary academic sources, prioritizing current arXiv papers and peer-reviewed proceedings.

The direct TheoremSearch POST endpoint was not reachable from the isolated build container, so no claim is made that its MCP executed inside the repository environment.

## 2. What is already mathematically strong

The research target must start from what the repository already proves well.

### 2.1 Exact integer CPMM semantics

[`CPMMInvariants.lean`](../../lean-mathlib/Proofs/CPMMInvariants.lean) and the v8 runtime kernel use the same essential integer structure:

```text
fee(g) = ceil(g * fee_bps / 10_000)
net(g) = g - fee(g)
out(g) = floor(y * net(g) / (x + net(g)))
```

[`FeeCeilDecomposition.lean`](../../lean-mathlib/Proofs/FeeCeilDecomposition.lean) already proves exact ceiling-fee decomposition properties. This is important because the new negative theorem is not about an approximate fee model. It is caused by the exact production ceiling.

### 2.2 Zero-fee local concavity

[`CPMMConcavity.lean`](../../lean-mathlib/Proofs/CPMMConcavity.lean) proves a reserve-independent near-discrete-concavity result for the zero-fee floored CPMM output. [`GaloisSplitCertificate.lean`](../../lean-mathlib/Proofs/GaloisSplitCertificate.lean) turns a finite defect grade into a local-to-global approximation certificate.

Those theorems remain correct in scope. The new result shows that their grade cannot be chosen independently of reserves after the v8 gross-input ceiling fee is introduced.

### 2.3 Fee anti-fragmentation and batch accounting

[`FeeAwareAntiFragmentation.lean`](../../lean-mathlib/Proofs/FeeAwareAntiFragmentation.lean) and [`FeeAwareBatchKGap.lean`](../../lean-mathlib/Proofs/FeeAwareBatchKGap.lean) already establish useful fee and aggregate-product relations. Re-proving those identities would not be a frontier improvement.

### 2.4 Structural route completeness and canonical winners

The many-pool exact-out proof chain covers structural candidate domains, residual allocations, capacity envelopes, and canonical selection. Examples include:

- [`ZenoDEXExactOutBruteforceCompleteness.lean`](../../lean-mathlib/Proofs/ZenoDEXExactOutBruteforceCompleteness.lean)
- [`ZenoDEXExactOutManyPoolRemainingCapacityEnvelope.lean`](../../lean-mathlib/Proofs/ZenoDEXExactOutManyPoolRemainingCapacityEnvelope.lean)
- [`ZenoDEXRoutingArgmin.lean`](../../lean-mathlib/Proofs/ZenoDEXRoutingArgmin.lean)

This proves valuable statements of the form "the selected key is minimal among a complete abstract candidate domain." The remaining hole is to prove that the concrete economic key assigned to every feasible pool allocation is globally bounded by an independently checkable certificate.

### 2.5 Static curve trade-off

[`ImpossibilityTheoremV2.lean`](../../lean-mathlib/Proofs/ImpossibilityTheoremV2.lean) proves, for the power family

```text
K_alpha(x, y) = x y (x + y)^alpha,
```

that the implemented local slippage and impermanent-loss curvature coefficients move in opposite directions. Under its coefficient convention, their trade-off product is constant at `1/4`. This means that searching for another member of this static one-parameter family cannot improve both local objectives at once.

The implication is strategic: batch design, routing, fee policy, and proof-carrying optimization are more promising force multipliers than adding more ungoverned curve variants.

## 3. Literature frontier

### 3.1 Global CFMM routing

Angeris, Chitra, Evans, and Boyd formulate multi-asset routing across CFMM networks as a convex optimization problem when fixed activation costs are ignored, and as a mixed-integer convex problem when they are included. Their framework also yields arbitrage or no-arbitrage certificates.

Primary source: <https://arxiv.org/abs/2204.05238>

Diamandis, Resnick, Chitra, and Angeris improve computational scalability through decomposition, including support for more complex and aggregate CFMMs.

Primary source: <https://arxiv.org/abs/2302.04938>

Escudero, Lara, and Sama extend the theory in 2026 to fixed gas costs and invariant functions beyond ordinary global convexity. Their relaxed model derives KKT conditions linking utility, prices, fees, and pool activation. Under pseudoconcavity and quasilinearity assumptions, those conditions become sufficient for global optimality, and the paper derives relaxation-error bounds.

Primary source: <https://arxiv.org/abs/2603.02844>

**ZenoDEX implication:** use these methods as candidate generators and dual-certificate generators, not as unchecked authority. ZenoDEX executes integers with ceiling fees and floor outputs, while the continuous theory supplies a relaxation. The integer verifier must close the relaxation gap.

### 3.2 Batch mechanism design

Canidio and Fritsch study a function-maximizing AMM in which all batch trades execute at a price equal to the post-batch marginal price. Under their market and competition assumptions, the mechanism eliminates LVR and sandwich profits.

Primary source: <https://doi.org/10.4230/LIPIcs.AFT.2023.24>

**ZenoDEX implication:** deterministic order and one uniform crossing price are not sufficient to inherit FM-AMM results. The accepted batch must also establish the post-batch marginal-price or equivalent function-maximization condition.

### 3.3 MEV and LVR

Kulkarni, Diamandis, and Chitra distinguish routing MEV from reordering MEV and show that routing quality can behave nontrivially under strategic extraction.

Primary source: <https://arxiv.org/abs/2207.11835>

Milionis, Moallemi, Roughgarden, and Zhang define loss-versus-rebalancing as the adverse-selection loss incurred when stale AMM prices are picked off by better-informed traders.

Primary source: <https://arxiv.org/abs/2208.06046>

**ZenoDEX implication:** canonical ordering removes one discretionary degree of freedom for a fixed admitted batch. It does not prove inclusion fairness, globally optimal routing, fair external pricing, or zero LVR.

### 3.4 Dynamic fees

Ghasemlu's June 2026 preprint derives a growth-optimal fee as pointwise volatility feedback in a stochastic-control LVR model. The optimal fee is increasing in instantaneous variance under the paper's assumptions, and gas costs are treated through an impulse-control dead band.

Primary source: <https://arxiv.org/abs/2606.21769>

**ZenoDEX implication:** dynamic fees are a promising research lane, but not a baseline authority rule. Any implementation needs authenticated lagged volatility, bounded fee movement, stale-oracle fallback, exact replay, and a proof that fee changes cannot invalidate user limits or global optimization certificates.

### 3.5 Formal AMM mathematics

Pusceddu and Bartoletti formalize constant-product AMMs in Lean 4 and mechanize economic properties including arbitrage.

Primary source: <https://arxiv.org/abs/2402.06064>

TheoremSearch reports a corpus of 9.2 million theorem statements and exposes theorem-level semantic search through a REST API and MCP endpoint.

Primary source: <https://arxiv.org/abs/2602.05216>

**ZenoDEX implication:** theorem retrieval is useful, but retrieved theorem names are discovery evidence. Only a proof term compiling against the repository's pinned Lean/mathlib environment enters the assurance surface.

## 4. Breakthrough 1: fee-aware concavity defect is unbounded

### 4.1 Statement

Define the production-style output specialized to input reserve `1` and fee `1` bp:

```text
F_y(g) = floor(y * (g - ceil(g/10_000)) /
               (1 + g - ceil(g/10_000))).
```

For every proposed natural defect grade `k`, choose

```text
y = 2(k + 1).
```

Then:

```text
F_y(0) = 0,
F_y(1) = 0,
F_y(2) = k + 1.
```

The positive second difference at gross inputs `0,1,2` is therefore:

```text
F_y(2) - 2 F_y(1) + F_y(0) = k + 1 > k.
```

Thus no reserve-independent natural `k` can satisfy a bounded near-concavity condition even on the three-point domain `{0,1,2}`.

### 4.2 Formal artifact

[`FeeAwareRoutingNonconcavity.lean`](../../lean-mathlib/Proofs/FeeAwareRoutingNonconcavity.lean) contains:

- `fee_aware_gross_second_difference_unbounded`;
- `no_reserve_independent_concavity_grade`;
- a concrete decreasing-threshold witness for `(x,y,fee) = (1,3,1 bp)`.

Status at report creation: `FORMAL_CANDIDATE`, pending exact-head Lean CI.

### 4.3 Concrete decreasing marginal threshold

For `(x,y,fee) = (1,3,1 bp)`:

```text
minimum gross for output >= 1: 2
minimum gross for output >= 2: 3
```

The threshold increments are `2` and then `1`. They decrease.

This directly invalidates any proof plan that assumes gross-space exact-out jump costs are always nondecreasing under the production fee formula.

### 4.4 Concrete greedy failure

The retained bounded witness uses two identical pools:

```text
reserve_in  = 1
reserve_out = 7
fee_bps     = 1
```

Their minimum gross-cost table for output quota `0..6` is:

```text
[0, 2, 2, 2, 3, 4, 7].
```

A unit-at-a-time marginal-cost greedy algorithm with lowest-index tie-breaking chooses quota allocation `[5,1]` at total gross cost `6`. Exhaustive quota split finds `[3,3]` at total gross cost `4`.

This is a 2-unit absolute gap and 50% excess relative to the optimum. It is not a claim that the repository's staircase dynamic program makes this mistake. It is a falsifier for replacing that DP with a simpler unit-marginal greedy proof.

Artifacts:

- [`check_fee_aware_routing_nonconcavity.py`](../../tools/check_fee_aware_routing_nonconcavity.py)
- [`fee_aware_routing_nonconcavity_evidence_20260717.json`](../../experiments/math_research_memory/fee_aware_routing_nonconcavity_evidence_20260717.json)
- [`test_fee_aware_routing_nonconcavity.py`](../../tests/test_fee_aware_routing_nonconcavity.py)

Status: `REPLAYED_BOUNDED` for grades `0..10,000`; the universal claim belongs to Lean, not the finite replay.

### 4.5 Consequence

The following production shortcuts are mathematically unsound without additional hypotheses:

- lifting the zero-fee grade-1 theorem directly to gross fee-aware output;
- proving exact globality from a local one-unit exchange condition;
- replacing jump-aware DP with per-output-unit marginal greedy allocation;
- treating rounding and fees as a small reserve-independent perturbation.

The correct alternatives are:

1. exact staircase/jump enumeration;
2. bounded exhaustive optimization;
3. a global upper-bound certificate independent of local concavity;
4. a proven reserve-dependent defect bound with an explicit error budget.

## 5. Breakthrough 2: affine-envelope global optimality certificates

### 5.1 Certificate

Let pools be indexed by `i`. Let `F_i(a)` be the exact integer output of pool `i` for gross allocation `a`, and let total gross budget be `B`.

Choose nonnegative integers `p`, `q > 0`, and one intercept `beta_i` per pool such that:

```text
q F_i(a) <= p a + beta_i
```

for every integer `a` in `0..B`.

For every feasible allocation with `sum_i a_i <= B`, summing the inequalities gives:

```text
q sum_i F_i(a_i) <= p B + sum_i beta_i.
```

Let the proposed winner output be `W`. If:

```text
p B + sum_i beta_i < q (W + 1),
```

then integer output implies every feasible competitor has output at most `W`. The winner is globally optimal under the primary output objective.

### 5.2 Formal artifact

[`RoutingAffineEnvelopeCertificate.lean`](../../lean-mathlib/Proofs/RoutingAffineEnvelopeCertificate.lean) contains:

- `component_le_budget`;
- `affine_envelope_global_upper_bound`;
- `strict_unit_gap_certifies_global_optimality`;
- `tight_envelope_certifies_global_optimality`.

Status at report creation: `FORMAL_CANDIDATE`, pending exact-head Lean CI.

### 5.3 Why this closes the important proof gap

The certificate does not trust how the candidate was found. A proposer may use:

- Angeris-style convex routing;
- decomposition;
- KKT active-set search;
- a mixed-integer solver;
- exact dynamic programming;
- branch and bound;
- a learned ranker;
- a heuristic.

The verifier checks only finite exact inequalities and the strict integer gap. This separates proposal efficiency from settlement authority.

It also separates two proof obligations that are currently easy to conflate:

1. **economic globality:** no feasible allocation has larger output;
2. **canonical uniqueness:** among equal-output winners, select the deterministic canonical key.

ZenoDEX already has substantial machinery for the second. The affine certificate supplies a path for the first.

### 5.4 How to generate intercepts

For a common slope `p/q`, the smallest valid intercept is:

```text
beta_i = max_{0 <= a <= B} (q F_i(a) - p a).
```

A development verifier may compute this exhaustively for bounded `B`. A production verifier should exploit the exact output-jump staircase:

- check only jump representatives and interval endpoints;
- retain a canonical segment cover;
- bind every segment to the exact pool state, fee profile, and amount domain;
- reject any uncovered amount;
- use checked wide multiplication.

If the one-line envelope is too loose to establish the strict unit gap, refine it with multiple slopes or piecewise affine segments. The same summation argument applies after introducing canonical segment selectors.

### 5.5 Exact-out dual

The mirror construction for exact-out routing should lower-bound gross cost functions `C_i(z)`:

```text
q C_i(z) >= p z - beta_i.
```

Summed lower bounds can certify that no competitor reaches the target output with less total gross input. This is a high-priority follow-up theorem because the current many-pool staircase work is exact-out oriented.

## 6. Breakthrough 3: current uniform batch clearing is not yet an FM-AMM proof

### 6.1 Current semantics

[`uniform_batch_clearing.py`](../../src/core/uniform_batch_clearing.py) verifies a proposed set of fills against:

- one canonical rational price;
- exact fee and net-input accounting;
- user limits and fill bounds;
- aggregate balance conservation;
- one aggregate pool transition;
- `k_after >= k_before`.

[`UniformBatchOptimality.lean`](../../lean-mathlib/Proofs/UniformBatchOptimality.lean) and the UPBA v2 certificate establish bounded, conditional optimality over an audited finite candidate set when completeness assumptions hold.

These are useful statements. They are not the FM-AMM statement from Canidio and Fritsch.

### 6.2 Missing condition

FM-AMM results require the batch price to equal the post-batch marginal price, or an equivalent proof that the post-batch reserves maximize the designated function for the external price.

The current verifier can accept a fill vector and reserve successor that preserve or increase `k` without proving:

```text
clearing price = post-batch marginal price,
```

or:

```text
post-state = argmax of the governed market function under the batch value constraint.
```

Therefore, current claims should remain:

- canonical for the admitted batch;
- uniform-price within the verified relation;
- aggregate-feasible and `k`-safe;
- bounded-audit optimal when the candidate-set completeness premise is established.

They should not be promoted to blanket "eliminates LVR" or "eliminates all sandwich/routing MEV" claims.

### 6.3 Proposed `CrossThenFM` lane

A stronger batch mechanism can preserve the useful internal crossing structure:

1. Canonically aggregate compatible opposing intents.
2. Cross as much opposing flow as possible without touching pool reserves.
3. Route only the net residual through the governed pool network.
4. Produce a continuous KKT/decomposition candidate.
5. Produce an exact integer affine or piecewise-envelope certificate for the residual route.
6. Bind the final uniform price to the certified post-batch marginal or function-maximizing state.
7. Apply the existing exact fee, conservation, nullifier, and canonical tie-break checks.

This can reduce pool movement while giving a principled route to FM-AMM-style claims. It remains a `HYPOTHESIS` until the exact integer objective and certificate are formalized.

## 7. Breakthrough 4: replace pair-local optimizer trust with a global token-price proof

The frontier routing literature is network-wide and multi-asset. ZenoDEX should represent the optimization certificate around one global token-price vector, not only pair-local splits.

A future proof object should bind:

- exact pre-state roots and canonical pool identities;
- global token-price numerators and denominators;
- the active pool set;
- per-pool exact trades;
- per-pool acceptance/invariant checks;
- global asset conservation;
- activation or fixed-cost terms;
- per-pool dual or affine-envelope bounds;
- the aggregate strict gap;
- the canonical tie-break key.

The continuous solver can use the literature's decomposition and KKT machinery. The authority verifier remains integer-only.

For fixed activation costs, the support set becomes part of the witness. Production globality requires either:

- a complete branch-and-bound certificate;
- exact comparison of every admissible support set in a bounded profile;
- or valid support-level upper bounds that prune all omitted supports.

A relaxed KKT solution alone is not enough.

## 8. Breakthrough 5: pivot static-curve research toward mechanisms

The existing power-family impossibility theorem says that, within that family and its local metrics, lower slippage curvature and better LP impermanent-loss curvature cannot both beat CPMM.

This suggests the following research allocation:

1. **Highest priority:** global routing certificates and batch function maximization.
2. **Next:** oracle-explicit dynamic fee policy with bounded controls.
3. **Next:** regime-specific curve selection with proof-bound applicability domains.
4. **Lower priority:** inventing additional static curves without a theorem stating which objective and regime they improve.

A new curve should be admitted only with:

- a governed objective vector;
- exact domain restrictions;
- reserve and arithmetic bounds;
- local and global no-arbitrage conditions;
- routing compatibility;
- integer-rounding analysis;
- LP value-risk analysis;
- a refinement theorem or explicit noninterchangeability with CPMM;
- rebuilt proof and replay evidence.

## 9. Breakthrough 6: dynamic fees need constitutional bounds

The 2026 stochastic-control result is promising because it links the optimal fee to volatility rather than treating fee selection as an arbitrary governance knob.

For ZenoDEX, the safe research profile is not "let an AI or oracle choose any fee." It is:

```text
fee_next = clamp(
    fee_previous + bounded_step,
    minimum_fee,
    maximum_fee
)
```

where the proposed step is a deterministic function of:

- authenticated lagged volatility;
- a minimum observation count;
- a bounded lookback;
- explicit stale-data behavior;
- a governed model version;
- a fixed-point arithmetic specification.

The fee policy must be unable to:

- rewrite user limit prices;
- alter an already admitted batch;
- bypass anti-fragmentation checks;
- create self-referential oracle manipulation;
- promote a heuristic forecast into settlement authority.

This lane remains `HYPOTHESIS` until an oracle manipulation model, exact fixed-point controller, and replay-bound safety theorem exist.

## 10. Prioritized implementation plan

### P0: compile and preserve the new falsifiers

1. Compile both new Lean modules under the pinned toolchain.
2. Run the retained Python evidence replay.
3. Keep all authority fields false.
4. Add mutation tests for fee rounding, denominator, reserves, and gross inputs.
5. Add the universal theorem and bounded witness to the proof/evidence inventory.

**Promotion gate:** zero `sorry`, zero custom axioms, exact-head Lean CI green, retained JSON exactly reproduced.

### P1: exact-in affine-envelope certificate checker

Implement a pure deterministic checker with nominal types for:

- pool identity and state;
- amount domain;
- slope numerator/denominator;
- intercepts or piecewise segments;
- candidate allocation;
- candidate output;
- strict unit gap;
- canonical violation vector.

The shell may authenticate state and execute an accepted effect plan. It must not recompute the economic decision.

**Promotion gate:** Python/Rust parity, Lean refinement, bounded exhaustive differential tests, forged-certificate rejection, checked arithmetic, proof-bound state and policy identities.

### P2: exact-out mirror certificate

Formalize cost lower envelopes and connect them to the existing many-pool exact-out staircase and canonical-winner chain.

**Promotion gate:** every feasible exact-out split is covered by either a direct candidate or a valid lower-bound certificate; no uncovered residual capacity.

### P3: `CrossThenFM` experimental batch lane

Implement it as a separate profile, not a silent change to existing UPBA semantics.

**Promotion gate:** exact objective, post-batch marginal/function-maximization certificate, user-limit preservation, fee and conservation proof, batch permutation invariance, no authority claim beyond the proved market model.

### P4: multi-token global dual routing

Use a global token-price witness, decomposition candidate generation, and support-set certificates for fixed execution costs.

**Promotion gate:** no pair-local conservation gap, no unsupported activation pruning, complete global asset accounting, exact integer verifier.

### P5: bounded dynamic-fee research profile

Keep it authority-free until robust oracle and manipulation tests exist.

## 11. Broader ZenoDEX follow-up research

The spot results suggest analogous proof-carrying optimization work elsewhere:

- **zUSD:** prove mounted multi-vault liquidation selection, Stability Pool and Default Pool accumulator error feedback, and global debt/custody refinement from one atomic state.
- **Perpetuals:** prove portfolio-level collateral provenance, funding conservation, liquidation priority, and bounded socialized-loss or ADL behavior.
- **Oracles:** formalize robust aggregation, correlated-source failure, lag, manipulation budgets, and divergence-triggered safe modes.
- **Curve selection:** make the selector return a proof-bound applicability certificate rather than a model score with implicit authority.

These are follow-up programs, not completed claims from this run.

## 12. Breakthrough ledger

| ID | Result | Evidence | Status | Production implication |
|---|---|---|---|---|
| B1 | Fee-aware gross CPMM second-difference defect is unbounded across reserves. | Lean module | `FORMAL_CANDIDATE` | Blocks reserve-independent greedy-concavity promotion. |
| B2 | `(1,3,1 bp)` has decreasing exact-out threshold increments `2,1`. | Lean + replay | `FORMAL_CANDIDATE` / `REPLAYED_BOUNDED` | Requires jump-aware or global certificates. |
| B3 | Two identical `(1,7,1 bp)` pools falsify unit-marginal greedy: cost `6` versus optimum `4`. | Tool + retained JSON + pytest | `REPLAYED_BOUNDED` | Preserves DP/staircase requirement. |
| B4 | Per-pool affine envelopes plus a strict integer gap certify exact global output optimality. | Lean module | `FORMAL_CANDIDATE` | Enables proof-carrying fast optimizers. |
| B5 | Current uniform batch relation is crossing-and-`k`-safety, not yet FM-AMM function maximization. | Code/proof/literature comparison | `IMPLEMENTED` distinction | Prevents overclaiming LVR/MEV elimination. |
| B6 | `CrossThenFM` combines internal crossing with certified residual function maximization. | Mechanism design | `HYPOTHESIS` | Candidate next batch profile. |
| B7 | Global token-price dual certificates are the scalable network-routing target. | Literature + repo gap | `HYPOTHESIS` | Replaces pair-local optimizer trust. |
| B8 | Static power-family curve search has a local slippage/IL trade-off; mechanism work has higher leverage. | Existing Lean theorem | `COMPILED_MAIN` | Reorders curve R&D priorities. |
| B9 | Volatility-feedback dynamic fees are promising only behind oracle-explicit constitutional bounds. | 2026 literature + design | `HYPOTHESIS` | Experimental, no settlement authority. |

## 13. Nonclaims

This report and branch do not establish:

- production readiness;
- settlement or release authority;
- that the new Lean files compile until exact-head CI reports success;
- complete optimal routing across arbitrary token graphs;
- exact fixed-cost mixed-integer globality;
- FM-AMM equivalence for the current uniform batch implementation;
- elimination of inclusion MEV, routing MEV, LVR, or all sandwich behavior;
- safety or profitability of dynamic fees;
- completion of zUSD, perpetuals, oracle, ZRPF, DA, finality, or atomic admission work.

The result of this run is a sharper mathematical architecture and two proof candidates, not a blanket upgrade of ZenoDEX's public assurance grade.

## 14. Falsifiable operating thesis

**ZenoDEX can scale its optimizer without weakening assurance if every fast continuous, mixed-integer, learned, or heuristic proposal is admitted only when an exact integer dual-envelope certificate and canonical settlement proof close the globality gap over the governed domain.**
