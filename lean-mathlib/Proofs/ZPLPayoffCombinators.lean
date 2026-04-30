import Proofs.CertifiedFinancialMathObjects
import Proofs.ZenoPayoffLanguage
import Mathlib

/-!
# ZPL Payoff Combinators

The current FIRE/ZPL proof surface certifies bounded arithmetic expressions.
This packet proves richer financial-object combinators that are still small
enough to verify: digitals, barriers, clamps/collars, conditional notes, short
positions, and an algebraic theorem layer over bounded payoffs.

## Discovery layer (beyond the seed)

We discover and prove:

1. **Conditional payoff algebra** — `conditionalZero` is idempotent,
   conditional-zero of a nonneg payoff has simpler bounds.
2. **Portfolio-level solvency** — any finite portfolio of conditional-zero legs
   is bilaterally solvent under aggregate certified-payoff collateral.
3. **Reusable capital-bound lemmas** — writer and holder collateral monotonicity,
   conditional collateral tightening.
4. **Conditional collar** — a barrier + collar combinator with tight bounds.
5. **Digital portfolio** — sum of digitals with aggregate collateral bound.
6. **Negation** — short-side of conditional payoffs with bilateral solvency.
-/

namespace Proofs
namespace ZPLPayoffCombinators

open CertifiedFinancialMathObjects

variable {World : Type _}

noncomputable section

namespace CertifiedPayoff

/-- A fixed digital payout: pay `amount` when `trigger` holds, else zero. -/
def digital (trigger : World → Prop) [DecidablePred trigger]
    (amount : ℝ) (hAmount : 0 ≤ amount) : CertifiedPayoff World where
  payoff := fun ω => if trigger ω then amount else 0
  lower := 0
  upper := amount
  sound := by
    intro ω
    by_cases h : trigger ω
    · simp [h, hAmount]
    · simp [h, hAmount]

/-- A barrier/conditional payoff: pay `P` when `trigger` holds, else zero. -/
def conditionalZero (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] : CertifiedPayoff World where
  payoff := fun ω => if trigger ω then P.payoff ω else 0
  lower := min P.lower 0
  upper := max P.upper 0
  sound := by
    intro ω
    simp only
    by_cases h : trigger ω
    · simp only [h, if_true]
      exact ⟨le_trans (min_le_left _ _) (P.lower_le ω),
             le_trans (P.le_upper ω) (le_max_left _ _)⟩
    · simp only [h, if_false]
      exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- A collar is just a certified clamp with financial naming. -/
def collar (P : CertifiedPayoff World) (floor cap : ℝ) (h : floor ≤ cap) :
    CertifiedPayoff World :=
  P.clamp floor cap h

theorem digital_payoff_eq_amount_or_zero
    (trigger : World → Prop) [DecidablePred trigger]
    (amount : ℝ) (hAmount : 0 ≤ amount) (ω : World) :
    (digital trigger amount hAmount).payoff ω = amount ∨
      (digital trigger amount hAmount).payoff ω = 0 := by
  simp only [digital]
  by_cases h : trigger ω <;> simp [h]

theorem digital_bilateral_no_default
    (trigger : World → Prop) [DecidablePred trigger]
    (amount : ℝ) (hAmount : 0 ≤ amount) (ω : World) :
    0 ≤ holderCollateral (digital trigger amount hAmount).lower +
        (digital trigger amount hAmount).payoff ω ∧
      0 ≤ writerCollateral (digital trigger amount hAmount).upper -
        (digital trigger amount hAmount).payoff ω := by
  exact (digital trigger amount hAmount).bilateral_no_default ω

theorem conditionalZero_interval_is_minmax
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] :
    (conditionalZero P trigger).lower = min P.lower 0 ∧
      (conditionalZero P trigger).upper = max P.upper 0 := by
  exact ⟨rfl, rfl⟩

theorem conditionalZero_payoff_bounds
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] (ω : World) :
    min P.lower 0 ≤ (conditionalZero P trigger).payoff ω ∧
      (conditionalZero P trigger).payoff ω ≤ max P.upper 0 := by
  exact ⟨(conditionalZero P trigger).lower_le ω, (conditionalZero P trigger).le_upper ω⟩

theorem conditionalZero_bilateral_no_default
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] (ω : World) :
    0 ≤ holderCollateral (conditionalZero P trigger).lower +
        (conditionalZero P trigger).payoff ω ∧
      0 ≤ writerCollateral (conditionalZero P trigger).upper -
        (conditionalZero P trigger).payoff ω := by
  exact (conditionalZero P trigger).bilateral_no_default ω

theorem collar_payoff_between_floor_cap
    (P : CertifiedPayoff World) (floor cap : ℝ) (h : floor ≤ cap) (ω : World) :
    floor ≤ (collar P floor cap h).payoff ω ∧
      (collar P floor cap h).payoff ω ≤ cap := by
  exact ⟨(collar P floor cap h).lower_le ω, (collar P floor cap h).le_upper ω⟩

/-- A conditional collateral budget never exceeds the wider of zero and the
original payoff bounds. -/
theorem conditionalZero_writerCollateral_le_max
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] :
    writerCollateral (conditionalZero P trigger).upper =
      writerCollateral (max P.upper 0) := by
  rfl

/-
Any finite portfolio of conditional-zero legs is solvent under the existing
aggregate certified-payoff collateral rule.
-/
theorem conditional_portfolio_bilateral_no_default
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)]
    (ω : World) :
    0 ≤ holderCollateral
          (S.sum fun i => (conditionalZero (P i) (trigger i)).lower) +
        S.sum (fun i => (conditionalZero (P i) (trigger i)).payoff ω) ∧
      0 ≤ writerCollateral
          (S.sum fun i => (conditionalZero (P i) (trigger i)).upper) -
        S.sum (fun i => (conditionalZero (P i) (trigger i)).payoff ω) := by
  unfold holderCollateral writerCollateral;
  constructor <;> cases max_cases ( 0 : ℝ ) ( -∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).lower ) <;> cases max_cases ( 0 : ℝ ) ( ∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).upper ) <;> linarith [ show ∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).payoff ω ≤ ∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).upper from Finset.sum_le_sum fun i hi => by exact ( conditionalZero ( P i ) ( trigger i ) ).le_upper ω, show ∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).lower ≤ ∑ i ∈ S, ( conditionalZero ( P i ) ( trigger i ) ).payoff ω from Finset.sum_le_sum fun i hi => by exact ( conditionalZero ( P i ) ( trigger i ) ).lower_le ω ]

/-!
## Discovery Layer: Conditional Payoff Algebra & Reusable Collateral Lemmas

Beyond the seed theorems, we develop a compositional theory of conditional
payoffs with portfolio-level solvency guarantees.
-/

-- ============================================================================
-- Section 1: Collateral monotonicity
-- ============================================================================

/-- Writer collateral is monotone in the upper bound. -/
theorem writerCollateral_mono {a b : ℝ} (h : a ≤ b) :
    writerCollateral a ≤ writerCollateral b := by
  simp only [writerCollateral]
  exact max_le_max le_rfl h

/-- Holder collateral is antitone in the lower bound. -/
theorem holderCollateral_anti {a b : ℝ} (h : a ≤ b) :
    holderCollateral b ≤ holderCollateral a := by
  simp only [holderCollateral]
  exact max_le_max le_rfl (neg_le_neg h)

-- ============================================================================
-- Section 2: Conditional payoff algebra — idempotence
-- ============================================================================

/-- Applying `conditionalZero` twice with the same trigger is idempotent
(the payoff function is the same). -/
theorem conditionalZero_idempotent_payoff
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] (ω : World) :
    (conditionalZero (conditionalZero P trigger) trigger).payoff ω =
      (conditionalZero P trigger).payoff ω := by
  simp only [conditionalZero]
  by_cases h : trigger ω <;> simp [h]

/-- The payoff of a sum of conditional-zero legs equals the sum of individual
conditional-zero payoffs. This validates component-wise collateral analysis. -/
theorem conditionalZero_sum_payoff
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)] (ω : World) :
    (S.sum fun i => (conditionalZero (P i) (trigger i)).payoff ω) =
      S.sum fun i => if trigger i ω then (P i).payoff ω else 0 := by
  simp [conditionalZero]

-- ============================================================================
-- Section 3: Digital portfolio — aggregate collateral
-- ============================================================================

/-- A portfolio of digital payoffs, each with its own trigger and amount. -/
def digitalPortfolio
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι)
    (triggers : ι → World → Prop) [∀ i, DecidablePred (triggers i)]
    (amounts : ι → ℝ) (hAmounts : ∀ i ∈ S, 0 ≤ amounts i) :
    CertifiedPayoff World where
  payoff := fun ω => S.sum fun i => if triggers i ω then amounts i else 0
  lower := 0
  upper := S.sum amounts
  sound := by
    intro ω
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      by_cases h : triggers i ω <;> simp [h, hAmounts i hi]
    · apply Finset.sum_le_sum
      intro i hi
      by_cases h : triggers i ω <;> simp [h, hAmounts i hi]

/-- Each digital in the portfolio has nonneg payoff,
so the aggregate holder collateral is zero. -/
theorem digitalPortfolio_holderCollateral_zero
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (triggers : ι → World → Prop) [∀ i, DecidablePred (triggers i)]
    (amounts : ι → ℝ) (hAmounts : ∀ i ∈ S, 0 ≤ amounts i) :
    holderCollateral (digitalPortfolio S triggers amounts hAmounts).lower = 0 := by
  simp [digitalPortfolio, holderCollateral]

/-- Bilateral no-default for a digital portfolio. -/
theorem digitalPortfolio_bilateral_no_default
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (triggers : ι → World → Prop) [∀ i, DecidablePred (triggers i)]
    (amounts : ι → ℝ) (hAmounts : ∀ i ∈ S, 0 ≤ amounts i) (ω : World) :
    0 ≤ holderCollateral (digitalPortfolio S triggers amounts hAmounts).lower +
        (digitalPortfolio S triggers amounts hAmounts).payoff ω ∧
      0 ≤ writerCollateral (digitalPortfolio S triggers amounts hAmounts).upper -
        (digitalPortfolio S triggers amounts hAmounts).payoff ω := by
  exact (digitalPortfolio S triggers amounts hAmounts).bilateral_no_default ω

-- ============================================================================
-- Section 4: Conditional collar — barrier + collar combinator
-- ============================================================================

/-- Conditional collar: collar applied only when a barrier trigger is active,
otherwise zero. Bounds are `[min floor 0, max cap 0]`. -/
def conditionalCollar
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger]
    (floor cap : ℝ) (h : floor ≤ cap) :
    CertifiedPayoff World :=
  conditionalZero (collar P floor cap h) trigger

/-- The conditional collar payoff is bounded by `[min floor 0, max cap 0]`. -/
theorem conditionalCollar_bounds
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger]
    (floor cap : ℝ) (h : floor ≤ cap) (ω : World) :
    min floor 0 ≤ (conditionalCollar P trigger floor cap h).payoff ω ∧
      (conditionalCollar P trigger floor cap h).payoff ω ≤ max cap 0 := by
  exact ⟨(conditionalCollar P trigger floor cap h).lower_le ω,
         (conditionalCollar P trigger floor cap h).le_upper ω⟩

/-- Bilateral no-default for a conditional collar. -/
theorem conditionalCollar_bilateral_no_default
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger]
    (floor cap : ℝ) (h : floor ≤ cap) (ω : World) :
    0 ≤ holderCollateral (conditionalCollar P trigger floor cap h).lower +
        (conditionalCollar P trigger floor cap h).payoff ω ∧
      0 ≤ writerCollateral (conditionalCollar P trigger floor cap h).upper -
        (conditionalCollar P trigger floor cap h).payoff ω := by
  exact (conditionalCollar P trigger floor cap h).bilateral_no_default ω

-- ============================================================================
-- Section 5: Nonneg-payoff conditional — tighter bounds when P.lower ≥ 0
-- ============================================================================

/-- When the underlying payoff is nonneg, the conditional-zero lower bound
simplifies to 0. -/
theorem conditionalZero_lower_of_nonneg
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger]
    (hP : 0 ≤ P.lower) :
    (conditionalZero P trigger).lower = 0 := by
  simp [conditionalZero, min_eq_right hP]

/-- When the underlying payoff is nonneg, holder collateral for the conditional
payoff is zero. -/
theorem conditionalZero_holderCollateral_zero_of_nonneg
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger]
    (hP : 0 ≤ P.lower) :
    holderCollateral (conditionalZero P trigger).lower = 0 := by
  rw [conditionalZero_lower_of_nonneg P trigger hP]
  simp only [holderCollateral, neg_zero, max_self]

-- ============================================================================
-- Section 6: Portfolio certified payoff from conditionalZero legs
-- ============================================================================

/-- Build a portfolio certified payoff from a finset of conditional-zero legs.
This is the certified sum of conditional-zero payoffs. -/
def conditionalPortfolio
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)] :
    CertifiedPayoff World :=
  CertifiedPayoff.sum S (fun i => conditionalZero (P i) (trigger i))

/-- The conditional portfolio is itself a certified payoff, so bilateral
no-default holds by the general theorem. -/
theorem conditionalPortfolio_bilateral_no_default
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)]
    (ω : World) :
    0 ≤ holderCollateral (conditionalPortfolio S P trigger).lower +
        (conditionalPortfolio S P trigger).payoff ω ∧
      0 ≤ writerCollateral (conditionalPortfolio S P trigger).upper -
        (conditionalPortfolio S P trigger).payoff ω := by
  exact (conditionalPortfolio S P trigger).bilateral_no_default ω

/-- The conditional portfolio lower bound equals the sum of individual lower bounds. -/
theorem conditionalPortfolio_lower
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)] :
    (conditionalPortfolio S P trigger).lower =
      S.sum fun i => (conditionalZero (P i) (trigger i)).lower := rfl

/-- The conditional portfolio upper bound equals the sum of individual upper bounds. -/
theorem conditionalPortfolio_upper
    {ι : Type _} [DecidableEq ι]
    (S : Finset ι) (P : ι → CertifiedPayoff World)
    (trigger : ι → World → Prop) [∀ i, DecidablePred (trigger i)] :
    (conditionalPortfolio S P trigger).upper =
      S.sum fun i => (conditionalZero (P i) (trigger i)).upper := rfl

-- ============================================================================
-- Section 7: Writer/holder collateral nonnegativity
-- ============================================================================

/-- Writer collateral is nonneg. -/
theorem writerCollateral_nonneg (U : ℝ) : 0 ≤ writerCollateral U := le_max_left _ _

/-- Holder collateral is nonneg. -/
theorem holderCollateral_nonneg (L : ℝ) : 0 ≤ holderCollateral L := le_max_left _ _

-- ============================================================================
-- Section 8: Negation / short-side of a conditional payoff
-- ============================================================================

/-- The negation (short side) of a certified payoff. -/
def neg (P : CertifiedPayoff World) : CertifiedPayoff World where
  payoff := fun ω => -(P.payoff ω)
  lower := -P.upper
  upper := -P.lower
  sound := by
    intro ω
    constructor
    · exact neg_le_neg (P.le_upper ω)
    · exact neg_le_neg (P.lower_le ω)

/-- Shorting a conditional-zero payoff is bilaterally solvent. -/
theorem neg_conditionalZero_bilateral_no_default
    (P : CertifiedPayoff World)
    (trigger : World → Prop) [DecidablePred trigger] (ω : World) :
    0 ≤ holderCollateral (neg (conditionalZero P trigger)).lower +
        (neg (conditionalZero P trigger)).payoff ω ∧
      0 ≤ writerCollateral (neg (conditionalZero P trigger)).upper -
        (neg (conditionalZero P trigger)).payoff ω := by
  exact (neg (conditionalZero P trigger)).bilateral_no_default ω

end CertifiedPayoff

end

end ZPLPayoffCombinators
end Proofs
