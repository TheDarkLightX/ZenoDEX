import Mathlib

/-!
# ZenoOracle Dispute Game Incentive Compatibility Bound (Internal Exploration)

INTERNAL ONLY. This file lives under `internal/proofs/` and is NOT part of the
main `lean-mathlib/Proofs/` library.

## Motivation

The oracle dispute game has two strategic constraints that must hold
simultaneously for the mechanism to be incentive-compatible:

1. **Honest challenge profitability**: A challenger who disputes a genuinely
   wrong report must expect positive profit.  Otherwise bad values persist
   unchallenged.

2. **Frivolous dispute deterrence**: A challenger who disputes a correct report
   must expect negative profit.  Otherwise the dispute mechanism is weaponized
   to grief honest reporters.

## Model

Parameters (all in the same integer denomination):
  `D`           = dispute bond (challenger's upfront cost)
  `R`           = dispute reward (paid to challenger if dispute is upheld)
  `M_up`        = MEV extractable from an upheld dispute
  `M_rej`       = MEV extractable from a rejected dispute
  `p_w`         = probability dispute is upheld when report is wrong (0 or 1)
  `p_f`         = probability dispute is upheld when report is correct (0 or 1)

We work in the **deterministic boundary case** `p_w = 1, p_f = 0`, which gives
the cleanest and most binding constraints:

  honest_profit    = R + M_up - D
  frivolous_profit = M_rej - D

## Main Result

**Theorem `dispute_game_feasible_iff`**: The dispute game is incentive-compatible
(honest challenges profitable AND frivolous disputes deterred) if and only if:

```text
M_rej < D ∧ D < R + M_up
```

Plain reading: the dispute bond must sit strictly between the frivolous-dispute
MEV gain and the honest-challenge total gain.

**Corollary `dispute_game_feasibility_requires_honest_gain_above_frivolous_gain`**:
A necessary condition for feasibility is `M_rej < R + M_up`.

Plain reading: the honest-challenge total gain must exceed the frivolous-dispute
MEV gain.  If this fails, no dispute bond can satisfy both constraints.

## Scope

Deterministic boundary case only (`p_w = 1, p_f = 0`).  The probabilistic
generalization with `p_w, p_f ∈ [0, 1]` is sketched at the bottom.
-/

namespace Internal
namespace ZenoOracleDisputeGameBound

/-- Honest challenger profit: reward + MEV from upheld dispute, minus bond.
We avoid Int arithmetic by stating the profit condition as a Nat inequality:
honest profit > 0 iff R + M_up > D. -/
def honestProfitPositive (D R M_up : Nat) : Prop :=
  D < R + M_up

/-- Frivolous challenger profit: MEV from rejected dispute, minus bond.
Frivolous profit < 0 iff M_rej < D. -/
def frivolousProfitNegative (D M_rej : Nat) : Prop :=
  M_rej < D

/-- Dispute game is incentive-compatible: honest challenges profitable
AND frivolous disputes deterred. -/
def disputeGameFeasible (D R M_up M_rej : Nat) : Prop :=
  honestProfitPositive D R M_up ∧ frivolousProfitNegative D M_rej

/-- **Dispute Game Feasibility Theorem** (deterministic boundary).

The dispute game is incentive-compatible iff the bond sits strictly between
the frivolous-dispute MEV gain and the honest-challenge total gain. -/
theorem dispute_game_feasible_iff
    (D R M_up M_rej : Nat) :
    disputeGameFeasible D R M_up M_rej ↔ M_rej < D ∧ D < R + M_up := by
  unfold disputeGameFeasible honestProfitPositive frivolousProfitNegative
  constructor
  · intro ⟨h_honest, h_frivolous⟩
    constructor
    · omega
    · omega
  · intro ⟨h_rej, h_honest⟩
    constructor
    · omega
    · omega

/-- **Feasibility Necessity Corollary**.

If the dispute game is feasible, then the honest-challenge total gain
must exceed the frivolous-dispute MEV gain. -/
theorem dispute_game_feasibility_requires_honest_gain_above_frivolous_gain
    (D R M_up M_rej : Nat)
    (h : disputeGameFeasible D R M_up M_rej) :
    M_rej < R + M_up := by
  rw [dispute_game_feasible_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact Nat.lt_trans h1 h2

/-! ## Non-Vacuity Witnesses -/

/-- Witness: with `D = 10`, `R = 15`, `M_up = 0`, `M_rej = 0`,
the game is feasible.  Honest profit = 5, frivolous profit = -10. -/
theorem witness_feasible_standard :
    disputeGameFeasible 10 15 0 0 := by
  rw [dispute_game_feasible_iff]
  constructor
  · decide
  · decide

/-- Witness: with MEV from rejected dispute exceeding the honest gain,
no bond can make the game feasible.  `M_rej = 20 > R + M_up = 15`.

Strengthened from a fixed `D` to all `D`. -/
theorem witness_infeasible_mev_reject_exceeds_honest_gain
    (D : Nat) :
    ¬ disputeGameFeasible D 15 0 20 := by
  rw [dispute_game_feasible_iff]
  intro ⟨h1, h2⟩
  have : 20 < 15 := Nat.lt_trans h1 h2
  omega

/-- When `M_rej + 1 = R + M_up`, no integer bond `D` can satisfy both
strict inequalities `M_rej < D` and `D < R + M_up`. -/
theorem witness_infeasible_adjacent_gap
    (D : Nat) :
    ¬ disputeGameFeasible D 15 0 14 := by
  rw [dispute_game_feasible_iff]
  intro ⟨h1, h2⟩
  have : 14 < 15 := Nat.lt_trans h1 h2
  have : D = 14 := by omega
  omega

/-- Witness: bond equal to honest gain makes honest profit zero
(boundary violation).  `D = R + M_up = 15`. -/
theorem witness_boundary_bond_equals_honest_gain :
    ¬ disputeGameFeasible 15 15 0 0 := by
  rw [dispute_game_feasible_iff]
  intro ⟨_, h2⟩
  omega

/-- Witness: bond equal to frivolous MEV makes frivolous profit zero
(boundary violation).  `D = M_rej = 5`. -/
theorem witness_boundary_bond_equals_frivolous_gain :
    ¬ disputeGameFeasible 5 15 0 5 := by
  rw [dispute_game_feasible_iff]
  intro ⟨h1, _⟩
  omega

/-- Witness: zero bond makes frivolous profit positive (not deterred).
`D = 0` violates `M_rej < D` for any `M_rej > 0`. -/
theorem witness_zero_bond_infeasible
    (M_rej : Nat) (h : 0 < M_rej) :
    ¬ disputeGameFeasible 0 15 0 M_rej := by
  rw [dispute_game_feasible_iff]
  intro ⟨h1, _⟩
  omega

/-- Witness: `M_rej = R + M_up` makes the game infeasible for all bonds.
The strict inequality `D < R + M_up` and `M_rej < D` imply `M_rej < R + M_up`,
a contradiction. -/
theorem witness_mev_reject_equals_honest_gain
    (D : Nat) :
    ¬ disputeGameFeasible D 15 0 15 := by
  rw [dispute_game_feasible_iff]
  intro ⟨h1, h2⟩
  omega

/-! ## Probabilistic Generalization

When `p_w` and `p_f` are not deterministic, the constraints become:

```text
honest_profit    = p_w * (R + M_up) - D
frivolous_profit = p_f * (R + M_up) + (1 - p_f) * M_rej - D
```

Feasibility requires:

```text
p_w * (R + M_up) > D > p_f * (R + M_up) + (1 - p_f) * M_rej
```

We model probabilities as BPS-scaled integers (`p_w, p_f ∈ [0, BPS]` where
`BPS = 10000`) and use cross-multiplied comparisons to avoid division:

```text
p_w * gain > D * BPS  ∧  p_f * gain + (BPS - p_f) * M_rej < D * BPS
```

This matches the Python verifier's exact scaled integer arithmetic. -/

/-- BPS scale constant (10000 basis points = 100%). -/
def BPS : Nat := 10_000

/-- Probabilistic dispute game feasibility using BPS-scaled integers.

`p_w` and `p_f` are in basis points `[0, BPS]`.  Comparisons are
cross-multiplied by `BPS` to avoid fractional arithmetic.
The bounds `p_w ≤ BPS` and `p_f ≤ BPS` are preconditions. -/
def probDisputeGameFeasible (D R M_up M_rej p_w p_f : Nat) : Prop :=
  p_w ≤ BPS ∧ p_f ≤ BPS ∧
  p_w * (R + M_up) > D * BPS ∧
  p_f * (R + M_up) + (BPS - p_f) * M_rej < D * BPS

/-- **Probabilistic Feasibility Necessity**.

If the probabilistic dispute game is feasible, then the discrimination gap
times the honest gain must exceed the residual frivolous MEV (scaled by BPS):

```text
(p_w - p_f) * (R + M_up) > (BPS - p_f) * M_rej
```

Plain reading: the signal quality `(p_w - p_f)` times the honest gain
must dominate the residual frivolous MEV.  When `p_w = BPS` and `p_f = 0`,
this reduces to `BPS * (R + M_up) > BPS * M_rej`, i.e. `R + M_up > M_rej`,
matching the deterministic corollary. -/
theorem prob_feasibility_requires_discrimination_gap
    (D R M_up M_rej p_w p_f : Nat)
    (h : probDisputeGameFeasible D R M_up M_rej p_w p_f) :
    (p_w - p_f) * (R + M_up) > (BPS - p_f) * M_rej := by
  unfold probDisputeGameFeasible BPS at h
  obtain ⟨_, _, h_honest, h_frivolous⟩ := h
  have h_trans : p_w * (R + M_up) > p_f * (R + M_up) + (10000 - p_f) * M_rej := by omega
  have h_gain_pos : 0 < R + M_up := by
    by_contra h_not
    push_neg at h_not
    have h_zero : R + M_up = 0 := by omega
    have : p_w * (R + M_up) = 0 := by rw [h_zero, Nat.mul_zero]
    omega
  have h_pf_lt_pw : p_f < p_w := by
    by_contra h_not
    push_neg at h_not
    have h_eq : p_f = p_w + (p_f - p_w) := by omega
    have h_friv' : p_f * (R + M_up) < D * 10000 := by omega
    have h_mono : p_f * (R + M_up) ≥ p_w * (R + M_up) := by
      rw [h_eq, Nat.add_mul]
      apply Nat.le_add_right
    omega
  have h_sum : p_w - p_f + p_f = p_w := by omega
  have h_add_mul : (p_w - p_f + p_f) * (R + M_up) = (p_w - p_f) * (R + M_up) + p_f * (R + M_up) := Nat.add_mul _ _ _
  have h_combined : (p_w - p_f) * (R + M_up) + p_f * (R + M_up) = p_w * (R + M_up) := by
    rw [← h_add_mul, h_sum]
  unfold BPS
  omega

/-- The deterministic case `p_w = BPS, p_f = 0` recovers the corollary
`M_rej < R + M_up` from the probabilistic necessity. -/
theorem deterministic_recovers_corollary
    (D R M_up M_rej : Nat)
    (h : probDisputeGameFeasible D R M_up M_rej BPS 0) :
    M_rej < R + M_up := by
  have h_gap := prob_feasibility_requires_discrimination_gap D R M_up M_rej BPS 0 h
  unfold BPS at h_gap
  simp at h_gap
  omega

/-- Witness: probabilistic feasibility with `p_w = 8000, p_f = 1000`.
Discrimination gap = 7000 bps, honest gain = 15, frivolous MEV = 0.
`8000 * 15 = 120000 > 110000 = 11 * 10000` and `1000 * 15 = 15000 < 110000`. -/
theorem witness_prob_feasible_standard :
    probDisputeGameFeasible 11 15 0 0 8000 1000 := by
  unfold probDisputeGameFeasible BPS
  decide

/-- Witness: probabilistic infeasibility when discrimination gap is too small.
`p_w = 5001, p_f = 5000`, gap = 1 bps, honest gain = 10, frivolous MEV = 100.
`1 * 10 = 10 < 5000 * 100 = 500000`. -/
theorem witness_prob_infeasible_small_gap
    (D : Nat) :
    ¬ probDisputeGameFeasible D 10 0 100 5001 5000 := by
  unfold probDisputeGameFeasible BPS
  intro ⟨_, _, h1, h2⟩
  omega

/-- Witness: `p_w = p_f` makes the game infeasible for all bonds.
No discrimination gap means honest and frivolous profits are identical. -/
theorem witness_prob_infeasible_equal_probs
    (D : Nat) :
    ¬ probDisputeGameFeasible D 15 0 0 5000 5000 := by
  unfold probDisputeGameFeasible BPS
  intro ⟨_, _, h1, h2⟩
  omega

/-- Witness: `p_f = BPS` makes frivolous profit equal to honest gain,
so no bond can deter frivolous disputes. -/
theorem witness_prob_infeasible_p_f_at_max
    (D : Nat) :
    ¬ probDisputeGameFeasible D 15 0 0 9999 10000 := by
  unfold probDisputeGameFeasible BPS
  intro ⟨_, _, h1, h2⟩
  omega

/-- Witness: probabilistic feasibility with nonzero `M_rej`.
`p_w = 9000, p_f = 1000, R = 20, M_up = 0, M_rej = 5, D = 18`.
`9000 * 20 = 180000 > 180000` -- need strict, so `D = 17`: `180000 > 170000`.
`1000 * 20 + 9000 * 5 = 20000 + 45000 = 65000 < 170000`. -/
theorem witness_prob_feasible_nonzero_mrej :
    probDisputeGameFeasible 17 20 0 5 9000 1000 := by
  unfold probDisputeGameFeasible BPS
  decide

end ZenoOracleDisputeGameBound
end Internal
