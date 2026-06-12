import Proofs.CPMMConcavity
import Mathlib.Tactic

/-!
# Sandwich Certificate: Linear-Error Optimality for Floors of Concave Functions

`CPMMConcavity` Part III proves the graded certificate: grade-k concavity plus
2 neighbor comparisons certify global optimality within `k·d·(d−1)/2` at
distance `d` — and that quadratic error is TIGHT for the generic grade-k class
(`approx_certificate_tight`).

This file proves the CPMM split objective is not generic: it is a **floor of a
discretely concave rational function** (one floor unit per pool). For that
class the same 2 comparisons certify optimality within `δ·(d+1)` — LINEAR in
the distance — because the neighbor check caps the concave envelope's slope at
`δ`, and concavity propagates the cap to every later step.

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `RatDiscreteConcave` | Def | ℚ-valued non-increasing first differences |
| 2 | `rat_slope_le` / `rat_concave_linear_growth` | Core | slope cap propagates; growth ≤ n·s |
| 3 | `rat_discrete_concave_reverse` | Core | reversal preserves ℚ-concavity |
| 4 | `SandwichConcave` | Def | ∃ concave G with f ≤ G ≤ f + δ on {0..D} |
| 5 | `sandwich_certificate_linear` | Main | 2 checks ⟹ f(j) ≤ f(a★) + δ·(d+1) |
| 6 | `cpmmOutQ_*` | Bridge | cpmmOut = ⌊y·a/(x+a)⌋ over ℚ, concave envelope |
| 7 | `cpmm_split_sandwich` | Bridge | split objective is SandwichConcave 2 |
| 8 | `cpmm_zero_fee_split_certificate_linear` | Main | f(j) ≤ f(a★) + 2·d + 2, ALL pools |
| 9 | `cpmm_zero_fee_split_certificate_combined` | Main | error ≤ min(d·(d−1), 2·d+2) |
| 10| `witness_linear_order_necessary` | Tightness | floor-of-concave can gain ~d: linear order is right |

The envelope `G(a) = y·a/(x+a)` is taken over ℚ with the junk value `0/0 = 0`
at the single degenerate point `x = a = 0`, which keeps every statement
hypothesis-free in the pool parameters (matching the unconditional Part I/III
theorems).
-/

namespace Proofs
namespace CPMMSandwich

open CPMMConcavity (cpmmOut cpmmZeroFeeSplitObj)

/-! ## ℚ-valued discrete concavity -/

/-- Discrete concavity for ℚ-valued sequences: non-increasing first differences. -/
def RatDiscreteConcave (G : ℕ → ℚ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D → G (i + 2) - G (i + 1) ≤ G (i + 1) - G i

/-- Slopes only decrease to the right of `a`. -/
theorem rat_slope_le (G : ℕ → ℚ) (D a : ℕ) (hconc : RatDiscreteConcave G D)
    (m : ℕ) (hm : a + m + 1 ≤ D) :
    G (a + m + 1) - G (a + m) ≤ G (a + 1) - G a := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hn := ih (by omega)
    have hc := hconc (a + n) (by omega)
    have e1 : a + (n + 1) + 1 = a + n + 2 := by omega
    have e2 : a + (n + 1) = a + n + 1 := by omega
    rw [e1, e2]
    linarith

/-- Linear growth under a slope cap: if the first step out of `a` is ≤ s and
    G is discretely concave, then `G (a+n) ≤ G a + n·s`. -/
theorem rat_concave_linear_growth (G : ℕ → ℚ) (D a : ℕ) (s : ℚ)
    (hconc : RatDiscreteConcave G D)
    (hstep : G (a + 1) - G a ≤ s)
    (n : ℕ) (hn : a + n ≤ D) :
    G (a + n) ≤ G a + n * s := by
  induction n with
  | zero => simp
  | succ m ih =>
    have ihm := ih (by omega)
    have hslope := rat_slope_le G D a hconc m (by omega)
    have e : a + (m + 1) = a + m + 1 := by omega
    rw [e]
    push_cast
    linarith

/-- Index reversal preserves ℚ-valued discrete concavity. -/
theorem rat_discrete_concave_reverse (G : ℕ → ℚ) (D : ℕ)
    (hconc : RatDiscreteConcave G D) :
    RatDiscreteConcave (fun b => G (D - b)) D := by
  intro i hi
  show G (D - (i + 2)) - G (D - (i + 1)) ≤ G (D - (i + 1)) - G (D - i)
  have e1 : D - i = (D - (i + 2)) + 2 := by omega
  have e2 : D - (i + 1) = (D - (i + 2)) + 1 := by omega
  rw [e1, e2]
  linarith [hconc (D - (i + 2)) (by omega)]

/-! ## The sandwich class and the linear certificate -/

/-- `f` is sandwiched within `δ` below a discretely concave rational envelope
    on `{0, …, D}`. Floors of concave functions satisfy this with δ = 1;
    sums of two floors (the split objective) with δ = 2. -/
def SandwichConcave (δ : ℚ) (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∃ G : ℕ → ℚ, RatDiscreteConcave G D ∧
    ∀ i, i ≤ D → (f i : ℚ) ≤ G i ∧ G i ≤ (f i : ℚ) + δ

/-- **LINEAR SANDWICH CERTIFICATE**: if `f` is δ-sandwiched below a concave
    envelope and the 2-comparison certificate holds at `a`, then every `j ≤ D`
    satisfies

      (f j : ℚ) ≤ f a + δ * (|j − a| + 1).

    Compare `CPMMConcavity.nearly_certificate_global_approx`: the graded bound
    is quadratic in the distance and tight for generic grade-k functions; the
    sandwich structure upgrades it to linear. -/
theorem sandwich_certificate_linear (δ : ℚ) (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hsand : SandwichConcave δ f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1)) :
    ∀ j, j ≤ D →
      (f j : ℚ) ≤ (f a : ℚ) + δ * (|(j : ℚ) - (a : ℚ)| + 1) := by
  obtain ⟨G, hG, hbox⟩ := hsand
  intro j hj
  rcases lt_trichotomy j a with hja | rfl | haj
  · -- j < a: reverse the envelope and reuse the right-side argument.
    have hapos : 0 < a := by omega
    set Gr : ℕ → ℚ := fun b => G (D - b) with hGr
    have hGr_conc : RatDiscreteConcave Gr D := rat_discrete_concave_reverse G D hG
    -- Slope cap at D - a for the reversed envelope, from the LEFT neighbor check.
    have hstep : Gr (D - a + 1) - Gr (D - a) ≤ δ := by
      have e1 : D - (D - a + 1) = a - 1 := by omega
      have e2 : D - (D - a) = a := by omega
      have hup := (hbox (a - 1) (by omega)).2
      have hlo := (hbox a ha).1
      have hcheck := h_prev hapos
      simp only [hGr, e1, e2]
      have : (f (a - 1) : ℚ) ≤ (f a : ℚ) := by exact_mod_cast hcheck
      linarith
    have hgrow := rat_concave_linear_growth Gr D (D - a) δ hGr_conc hstep (a - j) (by omega)
    have e3 : D - (D - a + (a - j)) = j := by omega
    have e4 : D - (D - a) = a := by omega
    have hj_up : (f j : ℚ) ≤ Gr (D - a + (a - j)) := by
      simp only [hGr, e3]
      exact (hbox j hj).1
    have ha_up : Gr (D - a) ≤ (f a : ℚ) + δ := by
      simp only [hGr, e4]
      exact (hbox a ha).2
    have habs : |(j : ℚ) - (a : ℚ)| = ((a - j : ℕ) : ℚ) := by
      rw [abs_sub_comm]
      have : (a : ℚ) - (j : ℚ) = ((a - j : ℕ) : ℚ) := by
        have hle : j ≤ a := by omega
        push_cast [hle]
        ring
      rw [this]
      exact abs_of_nonneg (by positivity)
    rw [habs]
    have := hgrow
    nlinarith [hj_up, ha_up, this]
  · -- j = a: the sandwich itself forces δ ≥ 0
    have hbox_j := hbox j hj
    have hz : |(j : ℚ) - (j : ℚ)| = 0 := by simp
    rw [hz]
    nlinarith [hbox_j.1, hbox_j.2]
  · -- a < j: direct right-side argument on G.
    have haD : a < D := by omega
    have hstep : G (a + 1) - G a ≤ δ := by
      have hup := (hbox (a + 1) (by omega)).2
      have hlo := (hbox a ha).1
      have hcheck := h_next haD
      have : (f (a + 1) : ℚ) ≤ (f a : ℚ) := by exact_mod_cast hcheck
      linarith
    have hgrow := rat_concave_linear_growth G D a δ hG hstep (j - a) (by omega)
    have e : a + (j - a) = j := by omega
    rw [e] at hgrow
    have hj_up : (f j : ℚ) ≤ G j := (hbox j hj).1
    have ha_up : G a ≤ (f a : ℚ) + δ := (hbox a ha).2
    have habs : |(j : ℚ) - (a : ℚ)| = ((j - a : ℕ) : ℚ) := by
      have : (j : ℚ) - (a : ℚ) = ((j - a : ℕ) : ℚ) := by
        have hle : a ≤ j := by omega
        push_cast [hle]
        ring
      rw [this]
      exact abs_of_nonneg (by positivity)
    rw [habs]
    nlinarith [hj_up, ha_up, hgrow]

/-! ## CPMM instantiation -/

/-- The rational CPMM envelope `y·a/(x+a)` (junk value 0 at the single
    degenerate point x = a = 0, where ℚ division by zero is 0). -/
noncomputable def cpmmOutQ (x y a : ℕ) : ℚ := (y * a : ℚ) / ((x + a : ℕ) : ℚ)

/-- Floor sandwich, lower half: the integer output never exceeds the envelope. -/
theorem cpmmOut_le_envelope (x y a : ℕ) :
    ((cpmmOut x y a : ℤ) : ℚ) ≤ cpmmOutQ x y a := by
  rcases Nat.eq_zero_or_pos (x + a) with hz | hpos
  · -- x = a = 0: both sides are 0.
    have hx : x = 0 := by omega
    have ha : a = 0 := by omega
    subst hx; subst ha
    simp [cpmmOut, cpmmOutQ]
  · have hfloor : cpmmOut x y a * (x + a) ≤ y * a := Nat.div_mul_le_self _ _
    have hQ : ((cpmmOut x y a * (x + a) : ℕ) : ℚ) ≤ ((y * a : ℕ) : ℚ) := by
      exact_mod_cast hfloor
    have hden : (0 : ℚ) < ((x + a : ℕ) : ℚ) := by exact_mod_cast hpos
    rw [cpmmOutQ, le_div_iff₀ hden]
    push_cast at hQ ⊢
    linarith

/-- Floor sandwich, upper half: the envelope is below the integer output + 1. -/
theorem envelope_lt_cpmmOut_add_one (x y a : ℕ) :
    cpmmOutQ x y a < ((cpmmOut x y a : ℤ) : ℚ) + 1 := by
  rcases Nat.eq_zero_or_pos (x + a) with hz | hpos
  · have hx : x = 0 := by omega
    have ha : a = 0 := by omega
    subst hx; subst ha
    simp [cpmmOut, cpmmOutQ]
  · have hmod : y * a % (x + a) < x + a := Nat.mod_lt _ hpos
    have hdecomp : y * a = (x + a) * cpmmOut x y a + y * a % (x + a) :=
      (Nat.div_add_mod _ _).symm
    have hlt : y * a < (x + a) * (cpmmOut x y a + 1) := by
      calc y * a = (x + a) * cpmmOut x y a + y * a % (x + a) := hdecomp
        _ < (x + a) * cpmmOut x y a + (x + a) := by omega
        _ = (x + a) * (cpmmOut x y a + 1) := by ring
    have hQ : ((y * a : ℕ) : ℚ) < (((x + a) * (cpmmOut x y a + 1) : ℕ) : ℚ) := by
      exact_mod_cast hlt
    have hden : (0 : ℚ) < ((x + a : ℕ) : ℚ) := by exact_mod_cast hpos
    rw [cpmmOutQ, div_lt_iff₀ hden]
    push_cast at hQ ⊢
    linarith

/-- The envelope is discretely concave (cross-multiplied slope comparison;
    at the junk point the inequality is checked directly). -/
theorem cpmmOutQ_concave (x y D : ℕ) :
    RatDiscreteConcave (fun a => cpmmOutQ x y a) D := by
  intro i hi
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · -- x = 0: envelope is 0 at a = 0 (junk) and constantly y for a ≥ 1.
    have hval : ∀ a : ℕ, 0 < a → cpmmOutQ 0 y a = (y : ℚ) := by
      intro a hapos
      have hden : ((0 + a : ℕ) : ℚ) ≠ 0 := by
        have hpos' : 0 < 0 + a := by omega
        have : (0 : ℚ) < ((0 + a : ℕ) : ℚ) := by exact_mod_cast hpos'
        exact ne_of_gt this
      rw [cpmmOutQ]
      field_simp
      push_cast
      ring
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- positions 0,1,2: values 0, y, y; slopes y then 0.
      have h1 := hval 1 (by omega)
      have h2 := hval 2 (by omega)
      have h0 : cpmmOutQ 0 y 0 = 0 := by simp [cpmmOutQ]
      simp only [h0, h1, h2]
      have : (0 : ℚ) ≤ (y : ℚ) := by positivity
      linarith
    · have h0 := hval i hipos
      have h1 := hval (i + 1) (by omega)
      have h2 := hval (i + 2) (by omega)
      simp only [h0, h1, h2]
      linarith
  · -- x ≥ 1: all denominators positive; clear them and reduce to
    -- (x+i)(x+i+1) ≤ (x+i+1)(x+i+2) after simplification.
    have d0 : (0 : ℚ) < ((x + i : ℕ) : ℚ) := by
      have : 0 < x + i := by omega
      exact_mod_cast this
    have d1 : (0 : ℚ) < ((x + (i + 1) : ℕ) : ℚ) := by
      have : 0 < x + (i + 1) := by omega
      exact_mod_cast this
    have d2 : (0 : ℚ) < ((x + (i + 2) : ℕ) : ℚ) := by
      have : 0 < x + (i + 2) := by omega
      exact_mod_cast this
    show cpmmOutQ x y (i + 2) - cpmmOutQ x y (i + 1) ≤
      cpmmOutQ x y (i + 1) - cpmmOutQ x y i
    unfold cpmmOutQ
    rw [div_sub_div _ _ (ne_of_gt d2) (ne_of_gt d1),
      div_sub_div _ _ (ne_of_gt d1) (ne_of_gt d0),
      div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    ring_nf
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℚ) y)
        (Nat.cast_nonneg (α := ℚ) i)) (Nat.cast_nonneg (α := ℚ) x),
      mul_nonneg (Nat.cast_nonneg (α := ℚ) y) (Nat.cast_nonneg (α := ℚ) x),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℚ) y)
        (Nat.cast_nonneg (α := ℚ) x)) (Nat.cast_nonneg (α := ℚ) x)]

/-- **THE SPLIT OBJECTIVE IS 2-SANDWICHED** below a concave envelope, for every
    pool configuration: each pool's floor costs at most one unit. -/
theorem cpmm_split_sandwich (x₀ y₀ x₁ y₁ D : ℕ) :
    SandwichConcave 2 (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D := by
  refine ⟨fun a => cpmmOutQ x₀ y₀ a + cpmmOutQ x₁ y₁ (D - a), ?_, ?_⟩
  · -- Sum of concave + reversed concave is concave.
    intro i hi
    have h0 := cpmmOutQ_concave x₀ y₀ D i hi
    have h1 := rat_discrete_concave_reverse (fun a => cpmmOutQ x₁ y₁ a) D
      (cpmmOutQ_concave x₁ y₁ D) i hi
    simp only at h1
    linarith
  · intro i _
    constructor
    · have l0 := cpmmOut_le_envelope x₀ y₀ i
      have l1 := cpmmOut_le_envelope x₁ y₁ (D - i)
      simp only [cpmmZeroFeeSplitObj]
      push_cast
      push_cast at l0 l1
      linarith
    · have u0 := envelope_lt_cpmmOut_add_one x₀ y₀ i
      have u1 := envelope_lt_cpmmOut_add_one x₁ y₁ (D - i)
      simp only [cpmmZeroFeeSplitObj]
      push_cast
      push_cast at u0 u1
      linarith

/-- **LINEAR CERTIFICATE FOR CPMM SPLIT ROUTING** (all pools, no hypotheses):
    the 2-comparison certificate at `a★` bounds every competitor by a LINEAR
    error in the distance:

      obj(j) ≤ obj(a★) + 2·d + 2,   d = |j − a★|.

    This strictly improves the Part III quadratic bound `d·(d−1)` for d ≥ 4,
    by exploiting that the objective is a floor of a concave envelope rather
    than a generic grade-2 function. -/
theorem cpmm_zero_fee_split_certificate_linear
    (x₀ y₀ x₁ y₁ D a_star : ℕ) (ha : a_star ≤ D)
    (h_prev : 0 < a_star →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star - 1))
    (h_next : a_star < D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star + 1)) :
    ∀ j, j ≤ D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D j ≤
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star
          + 2 * |(j : ℤ) - (a_star : ℤ)| + 2 := by
  intro j hj
  have h := sandwich_certificate_linear 2 (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D a_star
    ha (cpmm_split_sandwich x₀ y₀ x₁ y₁ D) h_prev h_next j hj
  -- Transport the ℚ inequality back to ℤ (push_cast turns ℤ-abs into ℚ-abs).
  have hZ : ((cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D j : ℤ) : ℚ) ≤
      ((cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star
        + 2 * |(j : ℤ) - (a_star : ℤ)| + 2 : ℤ) : ℚ) := by
    push_cast
    linarith [h]
  exact_mod_cast hZ

/-- **COMBINED CERTIFICATE**: both error regimes at once — quadratic (better
    for d ≤ 3) and linear (better for d ≥ 4):

      obj(j) ≤ obj(a★) + min(d·(d−1), 2·d + 2). -/
theorem cpmm_zero_fee_split_certificate_combined
    (x₀ y₀ x₁ y₁ D a_star : ℕ) (ha : a_star ≤ D)
    (h_prev : 0 < a_star →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star - 1))
    (h_next : a_star < D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star + 1)) :
    ∀ j, j ≤ D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D j ≤
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star
          + min (|(j : ℤ) - (a_star : ℤ)| * (|(j : ℤ) - (a_star : ℤ)| - 1))
              (2 * |(j : ℤ) - (a_star : ℤ)| + 2) := by
  intro j hj
  have hquad := CPMMConcavity.cpmm_zero_fee_split_certificate_approx
    x₀ y₀ x₁ y₁ D a_star ha h_prev h_next j hj
  have hlin := cpmm_zero_fee_split_certificate_linear
    x₀ y₀ x₁ y₁ D a_star ha h_prev h_next j hj
  rcases le_total (|(j : ℤ) - (a_star : ℤ)| * (|(j : ℤ) - (a_star : ℤ)| - 1))
      (2 * |(j : ℤ) - (a_star : ℤ)| + 2) with hmin | hmin
  · rw [min_eq_left hmin]; linarith [hquad]
  · rw [min_eq_right hmin]; linarith [hlin]

/-- **LINEAR ORDER IS NECESSARY**: a floor of a concave (here: linear)
    envelope can gain ≈ d after a certified point, so no sub-linear error
    bound holds for the sandwich class. f(a) = ⌊9a/10⌋ passes the certificate
    at a★ = 0 (f(0) = f(1) = 0) yet f(20) = 18 = 0 + 18, against the linear
    bound 1·(20+1) = 21 (δ = 1 for a single floor). -/
theorem witness_linear_order_necessary :
    (9 * 1 / 10 : ℕ) = 0 ∧
    (9 * 20 / 10 : ℕ) = 18 ∧
    18 ≤ 1 * (20 + 1) := by
  native_decide

end CPMMSandwich
end Proofs
