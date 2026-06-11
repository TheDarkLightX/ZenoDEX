import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Funding Imbalance EV

Manual Lean proofs for a core game-theoretic finding from the funding-rate market:
under positive long/short stake sizes, the canonical imbalance expression

`(L - S)^2 / (2 * L * S)`

is non-negative, and it is zero iff the market is perfectly balanced (`L = S`).

This formalizes the structural shape of the EV term observed in wave analysis.
-/

namespace Proofs
namespace FundingImbalanceEV

/-- Canonical imbalance expression (in rational arithmetic). -/
def dualEV (L S : ℚ) : ℚ := (L - S) ^ 2 / (2 * L * S)

/-- The imbalance EV term is always non-negative for positive long/short stakes. -/
theorem dualEV_nonneg {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    0 ≤ dualEV L S := by
  unfold dualEV
  apply div_nonneg
  · exact sq_nonneg (L - S)
  · nlinarith

/-- The imbalance EV term is zero exactly at perfect balance (`L = S`). -/
theorem dualEV_eq_zero_iff {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    dualEV L S = 0 ↔ L = S := by
  have h2L_ne : (2 * L) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ne_of_gt hL)
  have hden_ne : (2 * L * S) ≠ 0 := by
    exact mul_ne_zero h2L_ne (ne_of_gt hS)
  unfold dualEV
  constructor
  · intro hzero
    have hsq : (L - S) ^ 2 = 0 := by
      field_simp [hden_ne] at hzero
      nlinarith
    have hdiff : L - S = 0 := sq_eq_zero_iff.mp hsq
    linarith
  · intro hEq
    subst hEq
    simp

/-- Strict positivity holds exactly when the imbalance is non-zero (`L ≠ S`). -/
theorem dualEV_pos_iff {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    0 < dualEV L S ↔ L ≠ S := by
  constructor
  · intro hpos hEq
    subst hEq
    simp [dualEV] at hpos
  · intro hneq
    have hnonneg : 0 ≤ dualEV L S := dualEV_nonneg hL hS
    have hne0 : dualEV L S ≠ 0 := by
      intro hzero
      exact hneq ((dualEV_eq_zero_iff hL hS).mp hzero)
    have h0ne : (0 : ℚ) ≠ dualEV L S := by
      intro hz
      exact hne0 hz.symm
    exact lt_of_le_of_ne hnonneg h0ne

/-- Non-vacuity witness: imbalance EV is strictly positive when `L ≠ S`. -/
theorem witness_dualEV_positive :
    0 < dualEV 7 3 := by
  have hL : (0 : ℚ) < 7 := by norm_num
  have hS : (0 : ℚ) < 3 := by norm_num
  have hneq : (7 : ℚ) ≠ 3 := by norm_num
  exact (dualEV_pos_iff hL hS).2 hneq

/-! ## Structural characterization

The lemmas above treat `(L - S)^2 / (2 L S)` as an opaque expression.  The
results below give its complete structure:

* `dualEV_symm` / `dualEV_scale_invariant`: the EV term is symmetric in the
  two sides and depends only on the stake *ratio* — it is a scale-free
  market-shape statistic, not a size statistic.
* `dualEV_eq_imbalance_form`: the exact reparametrization
  `dualEV L S = 2 ρ² / (1 - ρ²)` where `ρ = (L - S) / (L + S)` is the
  normalized imbalance in `(-1, 1)`.  All three earlier lemmas
  (`dualEV_nonneg`, `dualEV_eq_zero_iff`, `dualEV_pos_iff`) become corollaries
  of this single identity, and it exposes the divergence of the EV term as
  the market becomes one-sided (`ρ → ±1`).
* `two_mul_imbalance_sq_le_dualEV`: the scale-free quadratic floor
  `2 ρ² ≤ dualEV` — the minimum balancing pressure grows quadratically in
  normalized imbalance.
* `dualEV_strict_mono_in_imbalance`: strictly more (squared) normalized
  imbalance means a strictly larger EV term, across any two markets of any
  sizes.
-/

/-- Normalized imbalance ratio `ρ = (L - S) / (L + S)`. -/
def imbalanceRatio (L S : ℚ) : ℚ := (L - S) / (L + S)

/-- The imbalance EV term is symmetric in the two sides. -/
theorem dualEV_symm (L S : ℚ) : dualEV L S = dualEV S L := by
  unfold dualEV
  rw [show (L - S) ^ 2 = (S - L) ^ 2 by ring, show 2 * L * S = 2 * S * L by ring]

/-- The imbalance EV term is scale-invariant: it depends only on the ratio of
    the stakes, not on market size. -/
theorem dualEV_scale_invariant (c L S : ℚ) (hc : c ≠ 0) :
    dualEV (c * L) (c * S) = dualEV L S := by
  unfold dualEV
  have hnum : (c * L - c * S) ^ 2 = c ^ 2 * (L - S) ^ 2 := by ring
  have hden : 2 * (c * L) * (c * S) = c ^ 2 * (2 * L * S) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- The squared normalized imbalance is strictly below 1 for positive stakes. -/
theorem imbalanceRatio_sq_lt_one {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    (imbalanceRatio L S) ^ 2 < 1 := by
  have hsum : (0 : ℚ) < L + S := by linarith
  have habs : |imbalanceRatio L S| < 1 := by
    unfold imbalanceRatio
    rw [abs_div, abs_of_pos hsum, div_lt_one hsum, abs_lt]
    constructor <;> linarith
  calc (imbalanceRatio L S) ^ 2 = |imbalanceRatio L S| ^ 2 := (sq_abs _).symm
    _ < 1 := by nlinarith [abs_nonneg (imbalanceRatio L S)]

/-- **Exact reparametrization**: for positive stakes,
    `dualEV L S = 2 ρ² / (1 - ρ²)` with `ρ = (L - S) / (L + S)`.
    The EV term is a function of the scale-free normalized imbalance alone,
    and it diverges as the market becomes one-sided (`ρ → ±1`). -/
theorem dualEV_eq_imbalance_form {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    dualEV L S = 2 * (imbalanceRatio L S) ^ 2 / (1 - (imbalanceRatio L S) ^ 2) := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hsum : (0 : ℚ) < L + S := by linarith
  have hsum_ne : L + S ≠ 0 := ne_of_gt hsum
  have hden_eq : 1 - (imbalanceRatio L S) ^ 2 = 4 * L * S / (L + S) ^ 2 := by
    unfold imbalanceRatio
    field_simp
    ring
  have hden_pos : (0 : ℚ) < 4 * L * S / (L + S) ^ 2 := by positivity
  rw [hden_eq]
  unfold dualEV imbalanceRatio
  rw [eq_div_iff (ne_of_gt hden_pos)]
  field_simp
  ring

/-- Scale-free quadratic floor: `2 ρ² ≤ dualEV L S`.  The minimum balancing
    pressure of the funding mechanism grows at least quadratically in the
    normalized imbalance, in units independent of market size. -/
theorem two_mul_imbalance_sq_le_dualEV {L S : ℚ} (hL : 0 < L) (hS : 0 < S) :
    2 * (imbalanceRatio L S) ^ 2 ≤ dualEV L S := by
  rw [dualEV_eq_imbalance_form hL hS]
  have hlt := imbalanceRatio_sq_lt_one hL hS
  have hpos : 0 < 1 - (imbalanceRatio L S) ^ 2 := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg (imbalanceRatio L S)]

/-- The reparametrized form `x ↦ 2x / (1 - x)` is strictly monotone on
    `(-∞, 1)` (no lower bound on `x` is needed). -/
theorem imbalance_form_strict_mono {x y : ℚ} (hxy : x < y) (hy : y < 1) :
    2 * x / (1 - x) < 2 * y / (1 - y) := by
  have hx1 : (0 : ℚ) < 1 - x := by linarith
  have hy1 : (0 : ℚ) < 1 - y := by linarith
  rw [div_lt_div_iff₀ hx1 hy1]
  nlinarith

/-- Strictly more squared normalized imbalance means a strictly larger EV
    term, across any two markets of any sizes. -/
theorem dualEV_strict_mono_in_imbalance {L S L' S' : ℚ}
    (hL : 0 < L) (hS : 0 < S) (hL' : 0 < L') (hS' : 0 < S')
    (himb : (imbalanceRatio L S) ^ 2 < (imbalanceRatio L' S') ^ 2) :
    dualEV L S < dualEV L' S' := by
  rw [dualEV_eq_imbalance_form hL hS, dualEV_eq_imbalance_form hL' hS']
  exact imbalance_form_strict_mono himb (imbalanceRatio_sq_lt_one hL' hS')

/-- Non-vacuity for the structural results: at `L = 7`, `S = 3`,
    `ρ = 2/5`, `dualEV = 8/21 = 2ρ²/(1-ρ²)`, the quadratic floor
    `2ρ² = 8/25` holds, and doubling both sides leaves the EV unchanged. -/
theorem witness_imbalance_form :
    imbalanceRatio 7 3 = 2 / 5 ∧
    dualEV 7 3 = 8 / 21 ∧
    2 * (imbalanceRatio 7 3) ^ 2 ≤ dualEV 7 3 ∧
    dualEV (2 * 7) (2 * 3) = dualEV 7 3 := by
  norm_num [imbalanceRatio, dualEV]

end FundingImbalanceEV
end Proofs
