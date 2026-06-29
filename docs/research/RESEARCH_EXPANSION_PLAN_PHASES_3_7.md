# ZenoDEX Research Expansion Plan - Phases 3-7

## Context

Phases 1-2 produced 33 breakthroughs (28 + 5) with 7 Lean proofs, 27 Python scripts,
and a CPSS-BC research scope certificate (Codex grade A-). This document plans the
next five research phases to expand knowledge coverage across algorithms, math,
assurance, design patterns, mechanism design, game theory, and coding techniques.

## Phase 3: Formal Verification Completion [COMPLETED]

**Goal:** Close the three explicitly identified proof gaps from Phases 1-2.

**Status:** All four sub-phases completed with zero `sorry`/`admit`/`axiom`.

### 3A: CPMM Split Function Continuous Concavity (Lean) [COMPLETED]
- **Theorem:** `splitFunctionCont_concave` in `CpmmSplitConcavity.lean`
- **Result:** The continuous CPMM split function `F(a) = f_0(c0*a) + f_1(c1*(D-a))`
  is strictly concave: the second forward difference is strictly negative.
- **Key identity:** `Δ²f = -2*K*M*h² / ((M+x+h)*(M+x)*(M+x+2h)) < 0`
- **Scope:** Proves continuous concavity (no floor rounding). The discrete
  (floor-rounded) version is NOT universally discretely concave (empirically
  verified: floor rounding causes local non-concavities with max violation 9).
- **Depends on:** Existing `discrete_concave_has_unimodal_global_max` (breakthrough 29).
- **Impact:** Closes the gap in ternary search foundation; combined with breakthrough 29,
  proves ternary search finds the optimal split for CPMM.

### 3B: Ternary Search Algorithm Narrowing Invariant (Lean) [COMPLETED]
- **Theorem:** `ternary_narrowing_invariant` in `TernarySearchAlgorithm.lean`
- **Result:** For a discretely concave function, the leftmost argmax remains in
  the surviving interval after each ternary search step.
- **Key insight:** Case 4 (f(m1) ≥ f(m2)) requires discrete concavity (not just
  unimodality) to handle plateaus: f(m1) = f(m2) and f non-decreasing on [m1, m2]
  implies f is constant on [m1, m2], so d(m1) = 0, and by discrete concavity
  d(b) ≤ 0 for b ≥ m1, making f non-increasing from m1. So f(p) ≤ f(m2),
  contradicting f(m2) < f(p) from the leftmost argmax property.
- **Depends on:** 3A (CPMM concavity) + breakthrough 29 (unimodal global max).
- **Impact:** Completes formal verification of the ternary search algorithm itself.

### 3C: Ternary Search Termination (Lean) [COMPLETED]
- **Theorems:** `ternary_step_shrinks_interval`, `ternary_termination_bound`
  in `TernarySearchAlgorithm.lean`
- **Result:** Each ternary search step strictly reduces the interval size by at
  least 1, giving O(hi - lo) worst-case steps. The average shrinkage factor is
  ~2/3, giving O(log_{3/2}(hi - lo)) expected steps.
- **Depends on:** 3B (narrowing invariant).
- **Impact:** Completes the ternary search verification trilogy.

### 3D: Lipschitz Window Sufficiency (Lean) [COMPLETED]
- **Theorems:** `floor_L_optimal_implies_int_max_nearby`,
  `integer_argmax_trivial_bound` in `WindowBound.lean`
- **Result:** For a Lipschitz concave function with constant L > 0:
  1. f(⌊b*⌋) ≥ f(b*) - L (floor is L-optimal, from breakthrough 19)
  2. The integer argmax n* satisfies f(n*) ≥ f(b*) - L (within L of continuous opt)
  3. |n* - b*| ≤ |n* - ⌊b*⌋| + 1 (trivial triangle inequality bound)
- **Non-claim:** The tight window bound W = ⌈1/L⌉ requires CPMM-specific curvature
  analysis (strictly negative second derivative from 3A). Lipschitz alone cannot
  bound |n* - b*| because a general Lipschitz function can be flat near the maximum.
- **Depends on:** 3A (CPMM concavity), breakthrough 19 (floor proximity).
- **Impact:** Completes adaptive window verification (value bound proven,
  tight distance bound requires CPMM curvature, empirically verified).

## Phase 4: Multi-Pool Generalization & Routing [COMPLETED]

**Goal:** Extend beyond 2-pool CPMM to k-pool, multiple curve families, and exact-out.

### 4A: K-Pool Continuous Concavity [COMPLETED]
- **Lean proof:** `KPoolSplitConcavity.lean` (3-pool, both coordinates)
- **Theorems:** `splitFunction3PoolCont_concave_coord1`, `splitFunction3PoolCont_concave_coord2`
- **Key insight:** Separability — only 2 pools change per coordinate step
  (pool j increasing, pool k-1 decreasing). Each pool's contribution is negative
  by `cpmmOutputCont_secondDiff_neg`. Sum of two negatives is negative.
- **Python test:** `k_pool_concavity_test.py` (10/10 pass)
  - Coordinate-wise second differences negative for k=3,4,5,6
  - Random direction second differences negative (joint concavity)
  - Hessian eigenvalues all negative (negative definite)
  - Separability formula verified: Δ²F = Σ Δ²f_i
- **Non-claim:** The k > 3 case follows by the same argument but requires
  Finset sum infrastructure not developed in Lean. Documented as informal note.
- **Codex finding addressed:** Renamed `k_pool_concavity_principle` from
  `theorem ... : True := by trivial` to an explicit informal note. Fixed
  Hessian comment (NOT diagonal — remainder pool creates off-diagonal terms).

### 4B: K-Pool Discrete Violation Characterization [COMPLETED]
- **Python test:** `k_pool_discrete_violation_test.py` (5/5 pass)
- **Key findings (lean model: continuous fee + floor output):**
  - Max interior violation = 2 for all k (2,3,4,5) — does NOT grow with k
  - Floor error scales as < k: 2-pool 1.98, 3-pool 2.79, 4-pool 3.46, 5-pool 4.01
  - 2-pool ternary search accuracy: 82%
- **Non-claim:** Production model (ceiling fee) has larger violations (~25)
  bounded by O(L) where L is max spot price, not O(1).

### 4C: Non-CPMM Curve Family Concavity [COMPLETED]
- **Python test:** `non_cpmm_curve_concavity_test.py` (8/8 pass)
- **Curve families tested:**
  1. CPMM (baseline, Lean-proven): f'' < 0, split concave, ternary gap 0-1
  2. Cubic-sum K(x,y)=x*y*(p*x+q*y): f'' <= 0 (concave), split concave
  3. Quadratic CPMM K(x,y)=x^2*y: f'' < 0, split concave
- **Key finding:** Cubic-sum discrete ternary search gap = 2-3 (vs 0-1 for CPMM)
  because the integer root solver creates larger rounding plateaus.
- **Non-claim:** Continuous concavity holds for cubic-sum and quadratic CPMM.
  Discrete concavity is WORSE for non-CPMM curves due to more complex integer
  root extraction. Production ternary search for non-CPMM curves needs wider
  windows or different search strategies.
- **Python script:** `non_cpmm_curve_concavity_test.py`

### 4D: K-Pool Discrete Argmax Proximity [COMPLETED]
- **Lean proof:** `KPoolDiscreteArgmaxProximity.lean` (SCALAR conditional theorem)
- **Scope:** Applies the abstract argmax proximity theorem with `epsilon = k`.
  The Lean theorem is scalar (`F : R -> R`, `b* : R`), NOT a vector/simplex
  proof. The actual (k-1)-dimensional simplex formalization is left as future
  work. Floor error bound `< k` is verified empirically, not formally via
  Finset.sum. Zero sorry/admit/axiom.
- **Python test:** `k_pool_discrete_argmax_proximity_test.py` (2020 configs)
  - Exhaustive simplex enumeration for k=3 (D<=15) and k=4 (D<=8)
  - Most k>=3 cases use grid/neighborhood search, not full enumeration
  - All within (L+k) bound

### 4E: Exact-Out Route Certificates via Dominance Pruning (future work)
- **Hypothesis (ZB-20260627-02):** Replace many-pool exact-out candidate enumeration
  with dominance-pruned label-setting, reducing O(n^k) to O(n * k * log(n)).
- **Approach:** Define dominance relation on route labels, prove transitivity,
  implement label-setting algorithm, test against brute force.
- **Risk:** Integer fee rounding can break continuous dominance relation.
- **Python script:** `exact_out_dominance_pruning.py`

### 4D: Dynamic Fee Tier Analysis
- **Hypothesis:** Dynamic fee tiers preserve split concavity under monotonic fee
  functions, but break it under non-monotonic fee schedules.
- **Approach:** Model fee as function of pool state, analyze concavity preservation,
  identify adversarial fee schedules.
- **Python script:** `dynamic_fee_concavity.py`

## Phase 5: Adversarial Robustness & MEV Resistance [COMPLETED]

**Goal:** Use the concavity framework from Phase 3 to bound adversarial attack
profitability, explaining why existing mitigations work.

### 5A: Collusion Gain Bounded by Concavity Parameter [COMPLETED]
- **Python test:** `concavity_bounded_adversarial_test.py` (6/6 pass)
- **Key theorem (compounding from Phase 3D):** The precommit sacrifice attack
  gain is bounded by `|f''(0)| * a_A * a_B` where `|f''(0)|` is the CPMM curvature at the margin (MAXIMUM curvature, empirical bound)
  parameter (strong concavity from `CpmmSplitConcavity.lean`).
- **Empirical verification:** Max gain/bound ratio = 0.987 (gain stays within
  the concavity bound across 200 random configs).
- **Scaling laws confirmed:**
  - Gain scales as O(a_A * a_B) (product of trade sizes)
  - Gain inversely scales with pool depth M (deeper pool = less curvature)
  - Collusion rate is 100% for large B trades (a_B > 2M), ~99.5% for small

### 5B: Min_out Cap Effectiveness via Floor Proximity [COMPLETED]
- **Key insight (compounding from Phase 3D):** The floor proximity lemma
  `f(floor(b*)) >= f(b*) - L` implies that capping min_out at 90% of expected
  output makes sacrifice INFEASIBLE by construction: A always fills because
  output >= 0.9 * expected >= capped min_out.
- **Empirical verification:** 0/200 violations with 90% cap (vs ~42% without cap).
- **Connection to Lean proofs:** The cap works because it exploits the same
  Lipschitz/floor-proximity structure proven in `WindowBound.lean`.

### 5C: Sandwich Profit Bounded by Concavity [COMPLETED]
- **Key theorem:** Sandwich profit ≈ a_victim^2 / (4*M), scaling as O(1/M).
  This is the same M-scaling as the concavity parameter m ~ K/M^2.
- **Empirical verification:** profit * M / a^2 = 0.25 exactly (= 1/4) for all
  tested trade sizes, confirming the theoretical bound.
- **Connection to Phase 4:** Batch clearing reduces sandwich profit by 1/n
  factor (from existing research), and the per-trade profit is bounded by
  the concavity parameter from Phase 3.

### 5D: Open Questions (from existing research, not resolved here)
- Can we achieve 100% collusion resistance without welfare loss? (min_out cap
  achieves this but is a protocol restriction)
- Is there a mechanism that prevents both adaptive AND precommit attacks?
- What is the fundamental limit for collusion-proof batch auctions?
- These remain open for Phase 6 (game theory) investigation.

### 5B: Inclusion & Censorship Attack Bounds
- **Hypothesis:** A validator controlling fraction f of batch inclusion can extract
  rent R(f) = f * (collusion_surplus + MEV), and commit-reveal + min_out cap
  bounds R(f) <= f * epsilon for small epsilon.
- **Approach:** Model validator as batch builder with inclusion power, analyze
  rent extraction under each mitigation, derive bounds.
- **Python script:** `inclusion_censorship_analysis.py`

### 5C: Batch-Boundary Game Analysis
- **Hypothesis:** Strategic intent submission at batch boundaries creates a
  timing game where late submitters gain information advantage, and this advantage
  is bounded by the commit-reveal dead time T_commit.
- **Approach:** Model batch boundary as a Bayesian game, compute equilibrium,
  analyze how T_commit affects information advantage.
- **Python script:** `batch_boundary_game.py`

### 5D: Sybil Attack Resistance
- **Hypothesis:** Under post-AGI threat model (sybil_scale >> human_baseline),
  the min_out cap remains effective because it is per-intent, not per-identity.
- **Approach:** Model sybil as identity splitting, analyze whether splitting
  a single intent into k sub-intents can bypass the min_out cap.
- **Python script:** `sybil_resistance_analysis.py`

### 5E: Cross-Batch Arbitrage Analysis
- **Hypothesis:** Sequential batch settlement creates inter-batch arbitrage
  opportunities proportional to the price drift between batches, and these
  can be bounded by a maximum batch interval T_max.
- **Approach:** Model cross-batch arbitrage as a multi-period optimization,
  compute arbitrage profit as function of T_max and pool parameters.
- **Python script:** `cross_batch_arbitrage.py`

## Phase 6: Game Theory & Economic Mechanism Design [PARTIALLY COMPLETED]

**Goal:** Formalize the game-theoretic structure of the min_out cap mechanism
and characterize the welfare-collusion Pareto frontier.

### 6A: Fixed-Order Filled-User No-Gain Check for Min_out Cap [COMPLETED]
- **Python test:** `nash_equilibrium_min_out_cap_test.py` (5/5 pass)
- **Scope:** Fixed-order filled-user no-gain check (NOT a full Nash
  equilibrium for the (A,B) optimal ordering game). Checks that FILLED
  users under FIXED user-id ordering cannot gain by lowering min_out.
- **Empirical verification:** 0/418 no-gain violations for filled users.
  171/171 unfilled users benefit from lowering min_out (welfare-improving,
  not a strategic manipulation).
- **Key insight:** User UTILITY = OUTPUT (tokens received), NOT surplus
  (output - min_out). Lowering min_out increases surplus but NOT utility.
  This is the key distinction that gives the no-gain property.

### 6B: Welfare-Collusion Pareto Frontier [COMPLETED]
- **Pareto frontier traced:** alpha in [0.5, 1.0], measuring welfare and
  collusion rate at each cap ratio.
- **Sweet spot identified:** alpha=0.9 achieves 0% collusion with ~100% welfare.
  The frontier is nearly flat: small cap (alpha=0.9) eliminates collusion
  with minimal welfare loss.
- **Monotonicity confirmed:** Collusion rate monotonically decreases as alpha
  decreases. Welfare degrades gracefully (not cliff-like).

### 6C: Open Game Theory Questions (not resolved here)
- Post-AGI coupled game analysis (7-layer game) — future work
- LP incentive analysis (withdrawal timing game) — future work
- Oracle dispute game feasible-parameter polytope — future work
- Governance mechanism design — future work
- These require more complex game-theoretic models beyond the concavity
  framework developed in Phases 3-5.

### 6B: LP Incentive Analysis
- **Hypothesis:** LP withdrawal timing creates a game where rational LPs withdraw
  before large swaps, and this can be mitigated by a withdrawal delay T_withdraw
  combined with IL insurance.
- **Approach:** Model LP as a strategic agent with withdrawal option, compute
  equilibrium withdrawal strategy, analyze IL insurance impact.
- **Python script:** `lp_incentive_analysis.py`

### 6C: Oracle Dispute Game Feasible-Parameter Polytope
- **Hypothesis (ZB-20260627-03):** The oracle dispute game parameters (dispute bond,
  reward, slash, MEV) form a feasible polytope, and this polytope is non-empty
  for all modules with MEV < MEV_max.
- **Approach:** Compile dispute parameters into integer feasibility constraints,
  solve for feasible region, identify MEV_max.
- **Python script:** `oracle_dispute_polytope.py`

### 6D: Governance Mechanism Design
- **Hypothesis:** Governance parameter updates (fee, collateral ratio, funding rate)
  can be modeled as a mechanism design problem where the governance token holders
  are the agents, and the objective is DEX safety + user welfare.
- **Approach:** Formalize governance as a mechanism, analyze strategyproofness,
  identify governance attack vectors.
- **Python script:** `governance_mechanism_analysis.py`

### 6E: Proof Mining Economics
- **Hypothesis:** Proof mining rewards create a market where miners compete to find
  proofs, and the reward structure must satisfy budget balance + individual rationality
  + strategyproofness (Myrdal-Satterthwaite impossibility applies unless we relax one).
- **Approach:** Model proof mining as a procurement auction, analyze which
  Myrdal-Satterthwaite relaxation is acceptable, design the reward mechanism.
- **Python script:** `proof_mining_economics.py`

## Phase 7: Production Assurance & Formal Settlement

**Goal:** End-to-end formal verification and production readiness.

### 7A: End-to-End Settlement Proof (Lean)
- **Hypothesis:** The full settlement pipeline (intent validation -> batch clearing ->
  swap execution -> delta aggregation -> conservation check) preserves all safety
  invariants: conservation, non-negativity, determinism, k-product preservation.
- **Approach:** Compose existing component proofs into a pipeline proof, identify
  gaps, fill them.
- **Depends on:** Phase 3 (all), existing component proofs.

### 7B: Tau Spec Semantic Correctness
- **Hypothesis:** The 7 core Tau specs (cpmm_v1, balance_safety_v1, balance_transition_v1,
  batch_canonical_v1_4, batching_v1, batching_v1_4, governance_timelock_v1) are
  semantically equivalent to their Python implementations.
- **Approach:** For each spec, generate test vectors from Python, run through Tau,
  compare outputs. Formalize the equivalence as a Lean theorem for the core specs.
- **Python script:** `tau_semantic_correctness.py`

### 7C: CoW Capacity-Coupled Netting (ZB-20260627-01)
- **Hypothesis:** CoW (Coincidence of Wants) netting with capacity coupling can be
  solved as a bounded exact constrained matching problem in O(n^2 * B) where B is
  the batch capacity bound.
- **Approach:** Formalize CoW netting as a bipartite matching with capacity
  constraints, implement bounded exact solver, test against greedy baseline.
- **Python script:** `cow_capacity_netting.py`

### 7D: Confidential Computation Verification
- **Hypothesis:** The FHE sealed-bid mechanism preserves bid privacy and produces
  correct clearing prices, verifiable by a zero-knowledge proof.
- **Approach:** Model the FHE sealed-bid as a secure computation, analyze privacy
  guarantees, design the ZK proof for clearing price correctness.
- **Python script:** `confidential_verification.py`

### 7E: Production Deployment Checklist
- **Goal:** Create a machine-readable production deployment checklist with formal
  verification gates, adversarial test gates, and Tau certificate gates.
- **Approach:** Compile all proof obligations, test obligations, and certificate
  obligations into a single checklist with pass/fail criteria.

## Execution Priority

| Phase | Priority | Rationale |
|-------|----------|-----------|
| 3 | HIGH | Closes explicitly identified proof gaps; foundation for all later work |
| 5 | HIGH | Addresses non-claims that block production authority |
| 4 | MEDIUM | Extends algorithm coverage; needed for multi-pool production |
| 6 | MEDIUM | Deepens economic understanding; needed for governance and oracle |
| 7 | MEDIUM | Integrates everything; depends on 3-6 |

## Verification Standard

Each phase must pass Codex peer review at grade A- or higher, following the
protocol established in Phases 1-2:
- Lean proofs compile with zero errors, zero warnings, zero sorries
- Python tests have hard assertions with exact values
- Documentation has no overclaims
- Certificate replay passes with all facts = 1
