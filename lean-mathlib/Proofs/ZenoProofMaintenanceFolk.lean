import Mathlib

/-!
# ZenoProof Maintenance Folk Theorem (Exact Nat Predicate)

## Motivation

The ZenoProof spec lists maintenance subscription as a reward mode. Round 1
acknowledged this but did not formalize it. This file formalizes the exact
cross-multiplied Nat one-shot-deviation condition for ZenoProof maintenance
subscriptions, with monotonicity theorems on the three design levers
(slash, payment, cost), plus a retained counterexample showing that the
earlier simplified score is not sound.

## Main Results

- `honestSustainableExact`: promoted cross-multiplied Nat predicate:
  `c · (εDen · (δDen - δNum) + εNum · δNum) ≤ εNum · (δNum · p + s · (δDen - δNum))`.
- `honestSustainableSimple`: retained as a heuristic score only.
- `simple_score_not_sufficient_counterexample`: Lean-checked false accept
  for the old simplified score.
- `exact_sustainability_monotone_in_slash`: increasing slash preserves
  exact sustainability.
- `exact_sustainability_monotone_in_payment`: increasing payment preserves
  exact sustainability.
- `exact_sustainability_antimonotone_in_cost`: decreasing cost preserves
  exact sustainability.
- `simple_score_monotone_in_slash`, `simple_score_monotone_in_payment`,
  `simple_score_antimonotone_in_cost`: the demoted heuristic remains
  monotone, but monotonicity is not enough for safety.
- Exact witnesses include sustainable, unsustainable, and higher-slash-
  rescued configurations.

## Model

A maintainer receives payment `p` per period, incurs cost `c` per period,
faces slash `s` if caught defecting, and discounts future at
`δ = δNum / δDen`. The continuation value of honest cooperation is
`ε = εNum / εDen` (the per-period surplus from maintaining the subscription).

The exact one-shot-deviation condition (honest is sustainable iff defecting
once and losing the subscription is not profitable) is:

```text
c · (εDen · (δDen - δNum) + εNum · δNum)
  ≤ εNum · (δNum · p + s · (δDen - δNum))
```

## Scope

Exact one-shot-deviation verifier for the stated rational model. A full
repeated-game formalization with histories, strategies, and equilibrium
semantics remains open.
-/

namespace Internal
namespace ZenoProofMaintenanceFolk

/-! ## Core Definitions -/

/-- Exact sustainability predicate (cross-multiplied Nat form).

The maintainer is honest-sustainable iff the one-shot-deviation gain
(cost saved by defecting once) is dominated by the continuation loss
(slash + foregone future payments, discounted).

Cross-multiplied to avoid division and `Real`. Parameters:
- `c`: per-period cost of maintenance
- `p`: per-period payment for maintenance
- `s`: slash penalty if caught defecting
- `δNum / δDen`: discount factor `δ` (0 < δNum < δDen)
- `εNum / εDen`: per-period surplus `ε` from maintaining subscription -/
def honestSustainableExact (c p s δNum δDen εNum εDen : Nat) : Prop :=
  c * (εDen * (δDen - δNum) + εNum * δNum) ≤
    εNum * (δNum * p + s * (δDen - δNum))

/-- Simplified (heuristic) sustainability score.

This is the Klein-Leffler-style simplified score. It is NOT sufficient
for safety: `simple_score_not_sufficient_counterexample` shows a false
accept. Retained only as a heuristic object. -/
def honestSustainableSimple (c p s δNum δDen : Nat) : Prop :=
  c * (δDen - δNum) ≤ δNum * p + s * (δDen - δNum)

/-! ## Counterexample: Simple Score Is Not Sufficient -/

/-- **Simple Score Not Sufficient**: the simplified score can pass while
the exact one-shot-deviation condition fails.

Witness: `p=0, c=1, s=2, δ=2/3 (δNum=2, δDen=3), ε=1 (εNum=1, εDen=1)`.
- Simple: `1 * (3 - 2) = 1 ≤ 2 * 0 + 2 * (3 - 2) = 2`. Passes.
- Exact: `1 * (1 * 1 + 1 * 2) = 3 ≤ 1 * (2 * 0 + 2 * 1) = 2`. Fails.

The simplified score ignores the `ε` surplus, which is the key term
distinguishing the exact condition. -/
theorem simple_score_not_sufficient_counterexample :
    honestSustainableSimple 1 0 2 2 3 = true ∧
    ¬ (honestSustainableExact 1 0 2 2 3 1 1) := by
  unfold honestSustainableSimple honestSustainableExact
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## Monotonicity Theorems (Exact Predicate) -/

/-- **Exact Sustainability Monotone in Slash**: increasing the slash `s`
preserves exact sustainability. A larger slash makes defecting more
costly, so honest cooperation becomes more attractive. -/
theorem exact_sustainability_monotone_in_slash
    (c p s1 s2 δNum δDen εNum εDen : Nat)
    (_hDelta : δNum < δDen) (hS : s1 ≤ s2)
    (h1 : honestSustainableExact c p s1 δNum δDen εNum εDen) :
    honestSustainableExact c p s2 δNum δDen εNum εDen := by
  unfold honestSustainableExact at *
  -- RHS grows in s: εNum * (δNum * p + s * (δDen - δNum))
  have hRHS : εNum * (δNum * p + s1 * (δDen - δNum)) ≤
              εNum * (δNum * p + s2 * (δDen - δNum)) := by
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    exact hS
  omega

/-- **Exact Sustainability Monotone in Payment**: increasing the payment
`p` preserves exact sustainability. A larger payment makes honest
cooperation more attractive. -/
theorem exact_sustainability_monotone_in_payment
    (c p1 p2 s δNum δDen εNum εDen : Nat)
    (_hDelta : δNum < δDen) (hP : p1 ≤ p2)
    (h1 : honestSustainableExact c p1 s δNum δDen εNum εDen) :
    honestSustainableExact c p2 s δNum δDen εNum εDen := by
  unfold honestSustainableExact at *
  have hRHS : εNum * (δNum * p1 + s * (δDen - δNum)) ≤
              εNum * (δNum * p2 + s * (δDen - δNum)) := by
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact hP
  omega

/-- **Exact Sustainability Anti-Monotone in Cost**: decreasing the cost
`c` preserves exact sustainability. A lower cost makes honest cooperation
cheaper, so it's easier to sustain. -/
theorem exact_sustainability_antimonotone_in_cost
    (c1 c2 p s δNum δDen εNum εDen : Nat)
    (_hDelta : δNum < δDen) (hC : c2 ≤ c1)
    (h1 : honestSustainableExact c1 p s δNum δDen εNum εDen) :
    honestSustainableExact c2 p s δNum δDen εNum εDen := by
  unfold honestSustainableExact at *
  -- LHS shrinks in c: c * (εDen * (δDen - δNum) + εNum * δNum)
  have hLHS : c2 * (εDen * (δDen - δNum) + εNum * δNum) ≤
              c1 * (εDen * (δDen - δNum) + εNum * δNum) := by
    apply Nat.mul_le_mul_right
    exact hC
  omega

/-! ## Monotonicity Theorems (Simple Score, Demoted) -/

/-- **Simple Score Monotone in Slash**: the demoted heuristic remains
monotone in slash, but monotonicity is not enough for safety. -/
theorem simple_score_monotone_in_slash
    (c p s1 s2 δNum δDen : Nat)
    (_hDelta : δNum < δDen) (hS : s1 ≤ s2)
    (h1 : honestSustainableSimple c p s1 δNum δDen) :
    honestSustainableSimple c p s2 δNum δDen := by
  unfold honestSustainableSimple at *
  have hRHS : δNum * p + s1 * (δDen - δNum) ≤
              δNum * p + s2 * (δDen - δNum) := by
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    exact hS
  omega

/-- **Simple Score Monotone in Payment**: the demoted heuristic remains
monotone in payment. -/
theorem simple_score_monotone_in_payment
    (c p1 p2 s δNum δDen : Nat)
    (_hDelta : δNum < δDen) (hP : p1 ≤ p2)
    (h1 : honestSustainableSimple c p1 s δNum δDen) :
    honestSustainableSimple c p2 s δNum δDen := by
  unfold honestSustainableSimple at *
  have hRHS : δNum * p1 + s * (δDen - δNum) ≤
              δNum * p2 + s * (δDen - δNum) := by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact hP
  omega

/-- **Simple Score Anti-Monotone in Cost**: the demoted heuristic remains
anti-monotone in cost. -/
theorem simple_score_antimonotone_in_cost
    (c1 c2 p s δNum δDen : Nat)
    (_hDelta : δNum < δDen) (hC : c2 ≤ c1)
    (h1 : honestSustainableSimple c1 p s δNum δDen) :
    honestSustainableSimple c2 p s δNum δDen := by
  unfold honestSustainableSimple at *
  have hLHS : c2 * (δDen - δNum) ≤ c1 * (δDen - δNum) := by
    apply Nat.mul_le_mul_right
    exact hC
  omega

/-! ## Non-Vacuity Witnesses -/

/-- Witness: sustainable configuration.
`c=1, p=5, s=3, δ=1/2 (δNum=1, δDen=2), ε=1 (εNum=1, εDen=1)`.
Exact: `1 * (1 * 1 + 1 * 1) = 2 ≤ 1 * (1 * 5 + 3 * 1) = 8`. Sustainable. -/
theorem witness_sustainable :
    honestSustainableExact 1 5 3 1 2 1 1 := by
  unfold honestSustainableExact
  decide

/-- Witness: unsustainable configuration.
`c=10, p=1, s=1, δ=1/2 (δNum=1, δDen=2), ε=1 (εNum=1, εDen=1)`.
Exact: `10 * (1 * 1 + 1 * 1) = 20 ≤ 1 * (1 * 1 + 1 * 1) = 2`? No.
Unsustainable. -/
theorem witness_unsustainable :
    ¬ honestSustainableExact 10 1 1 1 2 1 1 := by
  unfold honestSustainableExact
  decide

/-- Witness: higher slash rescues sustainability.
With `c=5, p=1, s=1`: unsustainable (`5*2=10 > 1*2=2`).
With `c=5, p=1, s=10`: sustainable (`5*2=10 ≤ 1*11=11`).
Increasing slash from 1 to 10 rescues the configuration. -/
theorem witness_higher_slash_rescues :
    ¬ honestSustainableExact 5 1 1 1 2 1 1 ∧
    honestSustainableExact 5 1 10 1 2 1 1 := by
  unfold honestSustainableExact
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## Boundary Cases -/

/-- Boundary: zero cost is always sustainable.
When `c=0`, LHS = 0 ≤ any RHS. -/
theorem boundary_zero_cost_always_sustainable
    (p s δNum δDen εNum εDen : Nat) (_hDelta : δNum < δDen) :
    honestSustainableExact 0 p s δNum δDen εNum εDen := by
  unfold honestSustainableExact
  omega

/-- Boundary: zero slash requires enough payment.
When `s=0`, the condition reduces to
`c * (εDen * (δDen - δNum) + εNum * δNum) ≤ εNum * δNum * p`.
Payment `p` must be large enough to cover the cost. -/
theorem boundary_zero_slash_needs_payment
    (c p δNum δDen εNum εDen : Nat) (_hDelta : δNum < δDen) :
    honestSustainableExact c p 0 δNum δDen εNum εDen ↔
    c * (εDen * (δDen - δNum) + εNum * δNum) ≤ εNum * δNum * p := by
  unfold honestSustainableExact
  rw [show εNum * (δNum * p + 0 * (δDen - δNum)) = εNum * δNum * p from by ring]

end ZenoProofMaintenanceFolk
end Internal
