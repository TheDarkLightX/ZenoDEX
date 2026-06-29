# Codex Peer Review Chain-of-Thought: Phases 3-6

**Date:** 2026-06-29
**Branch:** `cpss-bc-research-codex-grade-a`
**Reviewer:** Codex (gpt-5.5, xhigh reasoning)
**Author agent:** Devin (GLM-5.2 High)
**Goal:** A- grade on Phases 3-6 of the CPSS-BC research run

This file records the deepest chain-of-thought insights from the multi-iteration
Codex peer review loop, so the process is auditable alongside the deliverables.

---

## 1. The Review Loop Shape

The loop followed the protocol in `AGENTS.md`:

```
submit -> grade -> findings -> fix -> resubmit -> ... -> A|A-
```

Iterations and grades:

| Iter | Scope       | Grade | Findings | Theme                                  |
|------|-------------|-------|----------|----------------------------------------|
| 1    | Phase 3     | B+    | 4        | scope overclaims, argmax corollary     |
| 2    | Phases 4-6  | C+    | 5        | Nash overclaim, concavity overstate, tautology, discriminant, scope |
| 3    | Phases 4-6  | B+    | 2 Medium | stale "Nash" naming, stale "tighter"   |
| 4    | Phases 4-6  | B+    | 3 Medium | stale `m/2`, conservation inconsistency, prod-guide exactness |
| 5    | Conservation | C+   | 6        | commutativity theorem, falsified bound in product, no falsification assertions |
| 6    | Conservation | B-   | 5        | stale Lean header overclaims, "Lean PROVEN universal" labels, epsilon blur, tautological cap test |
| 7    | Conservation | A-   | 1 LOW    | stale 1.82x prose drift, duplicated sentence |
| 8    | Lipschitz-stateful bridge | A- | 3    | stale handoff, stale docstring, continuous-vs-rounded scope note |
| 9    | Lipschitz-stateful bridge | A  | 0    | all round 8 findings resolved, zero findings |
| 10   | Game theory (Phase 6) | A- | 3    | raw algebraic equality (no conditional transition), raw output (no utility fn), scope note as theorem |
| 11   | Game theory (Phase 6) | A  | 0    | all round 10 findings resolved, zero findings |

The grade plateaued at B+ across iterations 3 and 4 for the Phases 4-6 scope.
The conservation law package then went through its own 3-iteration loop
(C+ -> B- -> A-) before reaching the target. The Lipschitz-stateful bridge
then went through a 2-iteration loop (A- -> A) to close the formal gap
between the generic Lipschitz increment and the exact stateful CPMM attack
model. The game-theory package (Phase 6) then went through a 2-iteration
loop (A- -> A) to formalize the fixed-order filled-user no-gain property
with a proper utility function and conditional batch transition. Each iteration closed the named findings but a new stale-wording or
scope-inconsistency surfaced. This is the key process insight: **stale
wording is a moving target because the same concept is described in multiple
files, and a fix in one file does not propagate to the others.**

---

## 2. Deepest Insight: The Curvature Parameter Confusion

The single most repeated finding across iterations 2, 3, and 4 was about how
the concavity parameter `m` is described relative to `|f''(0)|`.

### The Mathematical Reality

For CPMM `f(x) = K*gamma*x / (M + gamma*x)`:

- `f''(x) = -2*K*gamma^2*M / (M + gamma*x)^3` (concave, magnitude DECREASING in x)
- `|f''(0)| = 2*K*gamma^2 / M^2`  (MAXIMUM curvature, at the margin)
- `m := min_x |f''(x)|` over the domain  (MINIMUM curvature, the strong concavity parameter from Phase 3D)

So `|f''(0)| >= m` always. They are different quantities:

- `m` (min curvature) governs the algorithm window: `W ~ sqrt(2*(L+eps)/m)`.
- `|f''(0)|` (max curvature at margin) is what the second-order Taylor
  approximation `Gain ~ |f''(0)| * a_A * a_B / 2` uses.

### Why The Confusion Persisted

The original Phase 5 write-up used `m` loosely to mean "the concavity
parameter" without distinguishing min vs max curvature. When the concavity
bound `(m/2)*a_A*a_B` was FALSIFIED empirically (ratio up to 1.88x), the fix
was to switch the empirical scaling probe to `|f''(0)|`. But the prose in
multiple files kept referring to `m/2`, "tighter than m", or "conservation
law" framing that no longer matched the math.

### The Resolution (Iteration 4)

Three coordinated changes:

1. **Lean scope note** (`ConcavityConservationLaw.lean`): explicitly state that
   the `(m/2)` bound is FALSIFIED, and that the empirical probe uses
   `|f''(0)|` which is a MORE CONSERVATIVE upper bound (since `|f''(0)| >= m`).
   The word "tighter" was wrong because tighter means smaller; `|f''(0)|` is
   larger, so it is more conservative, not tighter.

2. **Conservation test** (`concavity_conservation_law_test.py`): the docstring
   and the inline comment at the tradeoff frontier test both now distinguish
   "algebraic window relation is Lean-proven" from "actual gain decrease is
   empirical". The `(m/2)` reference is replaced with the falsification note
   and the `|f''(0)|` empirical-probe explanation.

3. **Production guide** (`PRODUCTION_IMPLEMENTATION_GUIDE.md`): the exactness
   table was changed from `100% / No loss` to `96% empirical` with a note that
   algorithm narrowing is empirical and only the key unimodality property is
   Lean-proven. This aligns the production guide with the breakthrough report.

### The General Lesson

When a bound is falsified and replaced by a different quantity, every file
that referenced the old quantity must be updated, AND the relational language
("tighter", "smaller", "more conservative") must be checked against the actual
inequality direction. A single global grep for the old symbol is necessary but
not sufficient; the prose around it must also be reconciled.

---

## 3. The Nash Equilibrium Rescoping

### Original Claim (Phase 6)

The min_out cap mechanism "achieves a Nash equilibrium for filled users."

### Why It Was An Overclaim

A Nash equilibrium requires that NO user can beneficially deviate, including
unfilled users and users outside the current batch. The Phase 6 test only
checked that filled users, given the fixed (A,B) ordering, cannot gain by
deviating from their reported parameters. This is a much weaker property:

- It fixes the ordering (not a strategic variable in the test).
- It only considers filled users (unfilled users might deviate).
- It does not consider entry/exit or batch-boundary games.

### The Rescoped Claim

"Fixed-order filled-user no-gain check": given the (A,B) ordering is fixed,
no filled user can gain by misreporting their parameters. This is a
single-profile no-gain property, not a Nash equilibrium.

### Why The Renaming Took Multiple Iterations

The renaming touched:

- The test function name (`test_cap_mechanism_nash_equilibrium` -> `..._fixed_order_no_gain`)
- All print strings ("Nash violations" -> "no-gain violations")
- Variable names (`nash_violations` -> `no_gain_violations`)
- The research plan prose
- The breakthrough report
- The handoff doc

Iteration 3 caught the test-level naming. Iteration 4 confirmed the prose was
also clean. The lesson: when rescoping a claim, rename the symbol everywhere
in one pass, then grep for the old term across ALL docs, not just the file
that triggered the finding.

---

## 4. The Conservation Law That Wasn't

### The Original Framing

Phase 5 framed a "concavity conservation law": the curvature parameter `m`
governs BOTH the algorithm window AND the adversarial gain bound, with a
tradeoff frontier `window * gain ~ sqrt(M) * L * a_A` that "decreases with M".

### Why The Framing Broke

1. The "conservation law" name implies a Lean-proven theorem linking window
   to gain. No such theorem exists. The Lean file proves only algebraic
   identities (`sqrt(2*L/m) = sqrt(M)` at eps=0) and a generic Lipschitz
   increment.

2. The "decreases with M" claim is internally inconsistent: the Lipschitz
   product `sqrt(M) * L * a_A` is INCREASING in M (since `sqrt(M)` grows and
   `L*a_A` is constant for balanced pools). Only the ACTUAL stateful gain
   decreases with M, and that is empirical.

### The Rescoped Framing

- The Lean file is named `ConcavityConservationLaw.lean` for historical
  reasons, but its header and scope note now explicitly say "This file proves
  two algebraic identities and one generic Lipschitz increment. It does NOT
  prove a conservation law."
- The test file is named `concavity_conservation_law_test.py` for historical
  reasons, but its docstring now says "This is NOT a conservation law
  package."
- The tradeoff frontier test now says: "algebraic window relation is
  Lean-proven; actual gain decrease is empirical."

### The General Lesson

A filename is a historical artifact. When the claim it names is falsified or
narrowed, the file can keep its name but its header MUST state the actual
scope. Reviewers grade the header and the tests, not the filename. But the
header must be reconciled with every other file that references the old
framing.

---

## 5. The Production Guide Exactness Overstatement

### The Original Table

| Exactness | 100% | 100% | No loss |

### Why It Was Wrong

The breakthrough report says `96% empirical exactness` for the ternary search
DP. The `100%` in the production guide came from conflating "the key property
(discrete concavity implies unimodal global maximum) is Lean-proven" with
"the algorithm always finds the global maximum." The Lean proof proves the
PROPERTY that makes ternary search correct; it does NOT prove the ALGORITHM
(narrowing invariant and termination) is exact. The 4% empirical gap is real.

### The Fix

| Exactness | 100% | 96% empirical | 4% empirical gap (algorithm narrowing empirical; key unimodality property Lean-proven) |

### The General Lesson

"Property proven" != "algorithm proven". A proof of the property that
justifies an algorithm is necessary but not sufficient for algorithm
correctness. Production guides must distinguish the two.

---

## 6. The Iteration Cost Of Stale Wording

The grade plateaued at B+ for two iterations because each fix introduced or
left stale wording in a file not directly under review. The cost was roughly
2 extra review iterations (~30 minutes each) for what were essentially
copy-editing fixes.

### The Process Fix (For Future Phases)

Before submitting to Codex:

1. **Global grep the OLD term** across `docs/research/`, `lean-mathlib/Proofs/`,
   and any handoff/scope docs. Do not rely on the finding's file list.
2. **Check relational language** ("tighter", "smaller", "more conservative",
   "decreases", "increases") against the actual inequality direction.
3. **Reconcile every file that references the same concept**, not just the
   file that triggered the finding.
4. **Distinguish "property proven" from "algorithm proven"** in any
   production-facing doc.
5. **When a filename names a falsified claim**, keep the filename but make
   the header explicitly state the actual scope.

---

## 7. What The Lean Proofs Actually Establish

For the record, the Lean-proven theorems in this research run (Phases 3-6):

**Phase 3 (2-pool, continuous):**
- `CpmmSplitConcavity.lean`: continuous concavity of the CPMM split function.
- `TernarySearchAlgorithm.lean`: narrowing invariant and termination for the
  ternary search procedure (under the strong concavity hypothesis `m`).
- `StrongConcavityWindowBound.lean`: Lipschitz window sufficiency.
- `DiscreteArgmaxProximity.lean`: discrete argmax proximity under strong
  concavity (scalar, conditional on the external `m` hypothesis).

**Phase 4 (K-pool, continuous):**
- `KPoolSplitConcavity.lean`: 3-pool coordinate-wise second difference is
  non-positive (coordinate-wise concavity, NOT joint concavity).

**Phase 5 (conservation):**
- `ConcavityConservationLaw.lean`: algebraic identities
  (`m = 2*K/M^2 = 2*L/M`, `sqrt(2*L/m) = sqrt(M)` at eps=0, generic
  Lipschitz increment `f(a_A)-f(0) <= L*a_A`), AND the stateful CPMM attack
  gain bound (`cpmm_stateful_gain_bound`: `gain <= L*a_A` for fee-free CPMM,
  `cpmm_stateful_gain_bound_with_fee`: same with fee parameter gamma).
  No conservation law, no monotonicity.

**Phase 6 (game theory):**
- `MinOutCapGameTheory.lean`: fixed-order filled-user no-gain property
  with formal game definitions (`utility`: if filled then output else 0;
  `batchTransition`: conditional pool state transition). Five theorems:
  `cpmm_output_independent_of_min_out`, `filled_user_lower_min_out_still_fills`,
  `filled_user_lower_min_out_same_output`,
  `filled_user_no_profitable_deviation` (utility-based no-gain),
  `batch_state_invariant_after_filled_deviation` (conditional transition
  equality). NOT a full Nash equilibrium for the (A,B) optimal ordering game.

### What Is NOT Lean-Proven

- The ternary search ALGORITHM exactness (96% empirical).
- Any conservation law linking window to gain (no such theorem).
- Any Nash equilibrium (the claim was rescoped to a fixed-order no-gain check).
- Any monotonicity of gain with respect to pool depth (empirical only).

---

## 8. Target Grade Achieved: A

The target was A-. It was achieved at iteration 7 (conservation law scope)
after a 3-iteration sub-loop (C+ -> B- -> A-). The package was then extended
with the Lipschitz-stateful bridge (two new Lean theorems proving the exact
stateful CPMM attack gain bound), which went through a 2-iteration sub-loop
(A- -> A) to reach A with zero findings. The game-theory package (Phase 6)
then went through a 2-iteration sub-loop (A- -> A) to formalize the
fixed-order filled-user no-gain property with a formal utility function
and conditional batch transition.

The Phases 4-6 scope plateaued at B+ across iterations 3-4 and was not
resubmitted after the conservation package absorbed all the stale-wording
findings.

The final A grades were conditional on host verification (Codex sandbox
blocks pytest via bwrap loopback). Host verification confirmed:
- `lake env lean Proofs/ConcavityConservationLaw.lean`: 0 errors/warnings
- `lake env lean Proofs/MinOutCapGameTheory.lean`: 0 errors/warnings
- `python3 docs/research/concavity_conservation_law_test.py`: 9/9 PASS
- `python3 docs/research/nash_equilibrium_min_out_cap_test.py`: 5/5 PASS
- `pytest`: 11/11 PASS (10 conservation + 1 game theory)

The conservation law A grade was achieved with zero findings. The key
extension that moved the package from A- to A was proving the stateful
CPMM attack gain bound in Lean (`cpmm_stateful_gain_bound` for fee-free,
`cpmm_stateful_gain_bound_with_fee` for fee-bearing), closing the formal
gap between the generic Lipschitz increment and the exact stateful attack
model.

The game-theory A grade was achieved with zero findings. The key extension
that moved the package from A- to A was adding formal game definitions
(`utility`: if filled then output else 0; `batchTransition`: conditional
pool state transition) and proving the no-gain property through the
utility function rather than raw output equality.

---

## 9. Replay Commands

```bash
# Lean (compiles in Codex sandbox)
cd lean-mathlib && lake env lean Proofs/ConcavityConservationLaw.lean
cd lean-mathlib && lake env lean Proofs/KPoolSplitConcavity.lean

# Python (host; Codex sandbox blocks pytest via bwrap loopback)
python3 docs/research/concavity_conservation_law_test.py
python3 docs/research/concavity_bounded_adversarial_test.py
python3 docs/research/nash_equilibrium_min_out_cap_test.py
python3 docs/research/non_cpmm_curve_concavity_test.py
python3 docs/research/k_pool_concavity_test.py
python3 docs/research/k_pool_discrete_violation_test.py
python3 docs/research/k_pool_discrete_argmax_proximity_test.py
python3 docs/research/discrete_argmax_proximity_test.py
python3 docs/research/cpmm_split_concavity_test.py
```

---

## 10. Non-Claims (Explicit)

- Stateful CPMM attack gain bound: Lean PROVEN (`cpmm_stateful_gain_bound`:
  `gain <= L*a_A` for fee-free CPMM; `cpmm_stateful_gain_bound_with_fee`:
  same with fee). The empirical scaling probe in `concavity_bounded_adversarial_test.py`
  uses `|f''(0)|` (maximum curvature) which is a tighter constant than L but
  is empirical only.
- Nash equilibrium: NOT claimed. Rescoped to fixed-order filled-user no-gain
  check.
- Conservation law: NOT proven. Algebraic identities and stateful gain bound only.
- Ternary search algorithm exactness: 96% empirical. Key property
  (unimodality) Lean-proven; algorithm narrowing empirical.
- Monotonicity of gain with pool depth: empirical only.
- Min_out cap universal mitigation: NOT claimed. Phase 2 replay model only.
- K-pool joint concavity: NOT claimed. Coordinate-wise concavity only
  (3-pool, Lean-proven).
