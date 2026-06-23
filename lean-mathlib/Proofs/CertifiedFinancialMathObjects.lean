import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Certified Financial Math Objects

This file formalizes the core math for a proof-carrying derivatives layer.

The first layer is a compositional payoff algebra:

- `Safe f L U` means `f` is bounded in `[L, U]`
- `CertifiedPayoff Ω` packages a payoff over worlds `Ω` with certified bounds
- compositional constructors preserve sound bounds
- collateral requirements are computed from the certified interval

The second layer is a stateful certified object:

- `CertifiedFinancialObject Σ W` packages state, witnesses, transition safety,
  and a payoff bounded on the invariant
- `run` replays a witness trace
- invariant preservation over replay gives no-default after settlement
-/

namespace Proofs

namespace CertifiedFinancialMathObjects

open scoped BigOperators

variable {World State Witness ι : Type _}

/-- A payoff `f` is safe on world type `Ω` when every world value lies in
the closed interval `[L, U]`. -/
def Safe (f : World → ℝ) (L U : ℝ) : Prop :=
  ∀ ω, L ≤ f ω ∧ f ω ≤ U

/-- Generic writer collateral from an upper payoff bound. -/
def writerCollateral (U : ℝ) : ℝ := max 0 U

/-- Generic holder collateral from a lower payoff bound. -/
def holderCollateral (L : ℝ) : ℝ := max 0 (-L)

/-- A bounded payoff object over a world space `Ω`. -/
structure CertifiedPayoff (World : Type _) where
  payoff : World → ℝ
  lower : ℝ
  upper : ℝ
  sound : Safe payoff lower upper

namespace CertifiedPayoff

@[simp] theorem lower_le (P : CertifiedPayoff World) (ω : World) :
    P.lower ≤ P.payoff ω :=
  (P.sound ω).1

@[simp] theorem le_upper (P : CertifiedPayoff World) (ω : World) :
    P.payoff ω ≤ P.upper :=
  (P.sound ω).2

/-- Constant payoff object. -/
def const (c : ℝ) : CertifiedPayoff World where
  payoff := fun _ => c
  lower := c
  upper := c
  sound := by
    intro ω
    constructor <;> simp

/-- Sum of two certified payoffs. -/
def add (P Q : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => P.payoff ω + Q.payoff ω
  lower := P.lower + Q.lower
  upper := P.upper + Q.upper
  sound := by
    intro ω
    constructor <;> linarith [P.lower_le ω, P.le_upper ω, Q.lower_le ω, Q.le_upper ω]

/-- Difference of two certified payoffs. -/
def sub (P Q : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => P.payoff ω - Q.payoff ω
  lower := P.lower - Q.upper
  upper := P.upper - Q.lower
  sound := by
    intro ω
    constructor <;> linarith [P.lower_le ω, P.le_upper ω, Q.lower_le ω, Q.le_upper ω]

/-- Scale by a nonnegative scalar. -/
def scaleNonneg (a : ℝ) (ha : 0 ≤ a) (P : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => a * P.payoff ω
  lower := a * P.lower
  upper := a * P.upper
  sound := by
    intro ω
    constructor
    · exact mul_le_mul_of_nonneg_left (P.lower_le ω) ha
    · exact mul_le_mul_of_nonneg_left (P.le_upper ω) ha

/-- Scale by a nonpositive scalar. -/
def scaleNonpos (a : ℝ) (ha : a ≤ 0) (P : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => a * P.payoff ω
  lower := a * P.upper
  upper := a * P.lower
  sound := by
    intro ω
    constructor
    · exact mul_le_mul_of_nonpos_left (P.le_upper ω) ha
    · exact mul_le_mul_of_nonpos_left (P.lower_le ω) ha

/-- Positive part `max(f, 0)`. -/
def positivePart (P : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => max (P.payoff ω) 0
  lower := max P.lower 0
  upper := max P.upper 0
  sound := by
    intro ω
    constructor
    · exact max_le_max (P.lower_le ω) le_rfl
    · exact max_le_max (P.le_upper ω) le_rfl

/-- Cap a payoff above by `C` using `min(f, C)`. -/
def cap (P : CertifiedPayoff World) (C : ℝ) : CertifiedPayoff World where
  payoff := fun ω => min (P.payoff ω) C
  lower := min P.lower C
  upper := min P.upper C
  sound := by
    intro ω
    constructor
    · exact min_le_min (P.lower_le ω) le_rfl
    · exact min_le_min (P.le_upper ω) le_rfl

/-- Pointwise minimum of two certified payoffs. -/
def pointwiseMin (P Q : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => min (P.payoff ω) (Q.payoff ω)
  lower := min P.lower Q.lower
  upper := min P.upper Q.upper
  sound := by
    intro ω
    constructor
    · exact min_le_min (P.lower_le ω) (Q.lower_le ω)
    · exact min_le_min (P.le_upper ω) (Q.le_upper ω)

/-- Pointwise maximum of two certified payoffs. -/
def pointwiseMax (P Q : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => max (P.payoff ω) (Q.payoff ω)
  lower := max P.lower Q.lower
  upper := max P.upper Q.upper
  sound := by
    intro ω
    constructor
    · exact max_le_max (P.lower_le ω) (Q.lower_le ω)
    · exact max_le_max (P.le_upper ω) (Q.le_upper ω)

/-- Pointwise product of two nonnegative certified payoffs. -/
def mulNonneg (P Q : CertifiedPayoff World)
    (hP : 0 ≤ P.lower) (hQ : 0 ≤ Q.lower) : CertifiedPayoff World where
  payoff := fun ω => P.payoff ω * Q.payoff ω
  lower := P.lower * Q.lower
  upper := P.upper * Q.upper
  sound := by
    intro ω
    have hPω : 0 ≤ P.payoff ω := le_trans hP (P.lower_le ω)
    have hQω : 0 ≤ Q.payoff ω := le_trans hQ (Q.lower_le ω)
    have hPupper : 0 ≤ P.upper := le_trans hP (le_trans (P.lower_le ω) (P.le_upper ω))
    constructor
    · exact mul_le_mul (P.lower_le ω) (Q.lower_le ω)
        hQ hPω
    · exact mul_le_mul (P.le_upper ω) (Q.le_upper ω)
        hQω hPupper

/-- Pointwise square of a nonnegative certified payoff. -/
def sqNonneg (P : CertifiedPayoff World) (hP : 0 ≤ P.lower) : CertifiedPayoff World :=
  mulNonneg P P hP hP

/-- Primitive clamp value used by the safe-playground grammar. -/
def clampValue (x A B : ℝ) : ℝ := max A (min x B)

theorem left_le_clampValue (x A B : ℝ) :
    A ≤ clampValue x A B := by
  exact le_max_left _ _

theorem clampValue_le_right (x A B : ℝ) (hAB : A ≤ B) :
    clampValue x A B ≤ B := by
  unfold clampValue
  exact max_le hAB (min_le_right _ _)

/-- Clamp a payoff into a certified interval `[A, B]`. -/
def clamp (P : CertifiedPayoff World) (A B : ℝ) (hAB : A ≤ B) : CertifiedPayoff World where
  payoff := fun ω => clampValue (P.payoff ω) A B
  lower := A
  upper := B
  sound := by
    intro ω
    constructor
    · exact left_le_clampValue (P.payoff ω) A B
    · exact clampValue_le_right (P.payoff ω) A B hAB

/-- Finite sum of certified payoffs. -/
def sum (S : Finset ι) (P : ι → CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => S.sum fun i => (P i).payoff ω
  lower := S.sum fun i => (P i).lower
  upper := S.sum fun i => (P i).upper
  sound := by
    intro ω
    constructor
    · exact Finset.sum_le_sum fun i hi => (P i).lower_le ω
    · exact Finset.sum_le_sum fun i hi => (P i).le_upper ω

/-- A capped positive-part payoff, useful for options and capped notes. -/
def cappedPositivePart (P : CertifiedPayoff World) (K Cap : ℝ) :
    CertifiedPayoff World :=
  cap (positivePart (sub P (const K))) Cap

/-- A capped call with nonnegative notional. -/
def cappedCall (P : CertifiedPayoff World) (N K Cap : ℝ)
    (hN : 0 ≤ N) : CertifiedPayoff World :=
  scaleNonneg N hN (cappedPositivePart P K Cap)

theorem cappedPositivePart_upper_le_cap (P : CertifiedPayoff World) (K Cap : ℝ)
    (_hCap : 0 ≤ Cap) :
    (cappedPositivePart P K Cap).upper ≤ Cap := by
  dsimp [cappedPositivePart, cap]
  exact min_le_right _ _

theorem cappedCall_upper_le_notional_cap (P : CertifiedPayoff World) (N K Cap : ℝ)
    (hN : 0 ≤ N) (_hCap : 0 ≤ Cap) :
    (cappedCall P N K Cap hN).upper ≤ N * Cap := by
  have hcap : (cappedPositivePart P K Cap).upper ≤ Cap :=
    min_le_right _ _
  dsimp [cappedCall, scaleNonneg]
  exact mul_le_mul_of_nonneg_left hcap hN

end CertifiedPayoff

/-- If a realized payoff lies in `[L, U]`, then the writer collateral computed
from `U` cannot go negative after settlement. -/
theorem writer_no_default_of_bounds {x L U : ℝ}
    (hx : L ≤ x ∧ x ≤ U) :
    0 ≤ writerCollateral U - x := by
  unfold writerCollateral
  have hxu : x ≤ max 0 U := le_trans hx.2 (le_max_right _ _)
  linarith

/-- If a realized payoff lies in `[L, U]`, then the holder collateral computed
from `L` cannot go negative after settlement. -/
theorem holder_no_default_of_bounds {x L U : ℝ}
    (hx : L ≤ x ∧ x ≤ U) :
    0 ≤ holderCollateral L + x := by
  unfold holderCollateral
  have hL : -L ≤ max 0 (-L) := le_max_right _ _
  linarith

/-- Bilateral collateral sufficiency on a certified interval. -/
theorem bilateral_no_default_of_bounds {x L U : ℝ}
    (hx : L ≤ x ∧ x ≤ U) :
    0 ≤ holderCollateral L + x ∧ 0 ≤ writerCollateral U - x := by
  constructor
  · exact holder_no_default_of_bounds hx
  · exact writer_no_default_of_bounds hx

theorem CertifiedPayoff.writer_no_default (P : CertifiedPayoff World) (ω : World) :
    0 ≤ writerCollateral P.upper - P.payoff ω :=
  writer_no_default_of_bounds ⟨P.lower_le ω, P.le_upper ω⟩

theorem CertifiedPayoff.holder_no_default (P : CertifiedPayoff World) (ω : World) :
    0 ≤ holderCollateral P.lower + P.payoff ω :=
  holder_no_default_of_bounds ⟨P.lower_le ω, P.le_upper ω⟩

theorem CertifiedPayoff.bilateral_no_default (P : CertifiedPayoff World) (ω : World) :
    0 ≤ holderCollateral P.lower + P.payoff ω ∧
      0 ≤ writerCollateral P.upper - P.payoff ω :=
  bilateral_no_default_of_bounds ⟨P.lower_le ω, P.le_upper ω⟩

/-- A stateful certified financial object:
transition law + witness policy + invariant + bounded payoff on admissible
states. This is the Lean core of a proof-carrying derivative object. -/
structure CertifiedFinancialObject (State Witness : Type _) where
  transition : State → Witness → State
  witnessOk : Witness → Prop
  invariant : State → Prop
  payoff : State → ℝ
  lower : ℝ
  upper : ℝ
  payoffBounded : ∀ {σ}, invariant σ → lower ≤ payoff σ ∧ payoff σ ≤ upper
  transitionSafe : ∀ {σ w}, invariant σ → witnessOk w → invariant (transition σ w)

namespace CertifiedFinancialObject

/-- Replay a witness trace through the certified transition law. -/
def run (O : CertifiedFinancialObject State Witness) (σ : State) : List Witness → State
  | [] => σ
  | w :: ws => run O (O.transition σ w) ws

@[simp] theorem run_nil (O : CertifiedFinancialObject State Witness) (σ : State) :
    O.run σ [] = σ := rfl

@[simp] theorem run_cons (O : CertifiedFinancialObject State Witness) (σ : State)
    (w : Witness) (ws : List Witness) :
    O.run σ (w :: ws) = O.run (O.transition σ w) ws := rfl

/-- Certified invariant preservation across a replayable witness trace. -/
theorem invariant_run (O : CertifiedFinancialObject State Witness) :
    ∀ {σ ws}, O.invariant σ → List.Forall O.witnessOk ws → O.invariant (O.run σ ws)
  | σ, [], hInv, _ => by simpa using hInv
  | σ, w :: ws, hInv, hWs => by
      rw [List.forall_cons] at hWs
      rcases hWs with ⟨hw, htail⟩
      have hStep : O.invariant (O.transition σ w) := O.transitionSafe hInv hw
      simpa using O.invariant_run hStep htail

/-- Writer collateral stays solvent after replay as long as the invariant and
witness policy hold. -/
theorem writer_no_default_after_run (O : CertifiedFinancialObject State Witness)
    {σ : State} {ws : List Witness}
    (hInv : O.invariant σ) (hWs : List.Forall O.witnessOk ws) :
    0 ≤ writerCollateral O.upper - O.payoff (O.run σ ws) := by
  have hFinal : O.invariant (O.run σ ws) := O.invariant_run hInv hWs
  exact writer_no_default_of_bounds (O.payoffBounded hFinal)

/-- Holder collateral stays solvent after replay as long as the invariant and
witness policy hold. -/
theorem holder_no_default_after_run (O : CertifiedFinancialObject State Witness)
    {σ : State} {ws : List Witness}
    (hInv : O.invariant σ) (hWs : List.Forall O.witnessOk ws) :
    0 ≤ holderCollateral O.lower + O.payoff (O.run σ ws) := by
  have hFinal : O.invariant (O.run σ ws) := O.invariant_run hInv hWs
  exact holder_no_default_of_bounds (O.payoffBounded hFinal)

/-- Full bilateral no-default theorem after replay. -/
theorem bilateral_no_default_after_run (O : CertifiedFinancialObject State Witness)
    {σ : State} {ws : List Witness}
    (hInv : O.invariant σ) (hWs : List.Forall O.witnessOk ws) :
    0 ≤ holderCollateral O.lower + O.payoff (O.run σ ws) ∧
      0 ≤ writerCollateral O.upper - O.payoff (O.run σ ws) := by
  constructor
  · exact O.holder_no_default_after_run hInv hWs
  · exact O.writer_no_default_after_run hInv hWs

end CertifiedFinancialObject

/-- Concrete non-vacuity witness: a capped call with constant underlying has a
certified upper payout equal to notional times cap. -/
theorem witness_capped_call_upper :
    (CertifiedPayoff.cappedCall (World := Unit) (CertifiedPayoff.const 3) 10 1 (1 / 4)
      (by positivity)).upper ≤ 10 * (1 / 4 : ℝ) := by
  exact CertifiedPayoff.cappedCall_upper_le_notional_cap
    (P := CertifiedPayoff.const 3) (N := 10) (K := 1) (Cap := 1 / 4)
    (by positivity) (by positivity)

end CertifiedFinancialMathObjects

end Proofs
