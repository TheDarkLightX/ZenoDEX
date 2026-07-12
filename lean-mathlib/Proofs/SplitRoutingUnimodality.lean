/-!
Split Routing Conditional Bounds and DTSSR Arithmetic Lemmas.

This module contains boundedness results, a conditional perturbation lemma,
and arithmetic witnesses used while studying the Discrete Ternary Search
Split Router (DTSSR).

The proved declarations establish:
1. Integer CPMM output and two-pool objectives are reserve-bounded.
2. A function within one unit of a supplied concave midpoint model satisfies
   a two-unit near-unimodality inequality.
3. A coarse logarithmic exponent witness exists.
4. A candidate that dominates both endpoints dominates either single-pool
   allocation.

This file does not prove continuous CPMM concavity, a ternary-search state
invariant, a bound connecting the runtime evaluation counter to the displayed
arithmetic expression, or global DTSSR optimality. Integer fee rounding can
break discrete concavity, so runtime correctness requires a separate exact
rescue certificate or an implementation-connected approximation theorem.
-/

namespace Proofs
namespace SplitRoutingUnimodality

-- Model CPMM output as a Nat -> Nat function (integer domain)
-- f(a) = y * net / (x + net) where net = a - ceil(a * fee / 10000)

/-- For natural numbers, floor division is monotone non-decreasing:
    if a ≤ b then a / d ≤ b / d. -/
theorem nat_div_mono (a b d : Nat) (hab : a ≤ b) (_hd : d > 0) :
    a / d ≤ b / d := Nat.div_le_div_right hab

/-- CPMM output floor is bounded: y * net / (x + net) ≤ y.
    This proves the output never exceeds the reserve. -/
theorem cpmm_output_bounded (y net x : Nat) (hx : x > 0) :
    y * net / (x + net) ≤ y := by
  have hd : x + net > 0 := Nat.lt_of_lt_of_le hx (Nat.le_add_right x net)
  have h1 : y * net ≤ (x + net) * y := by
    rw [Nat.mul_comm (x + net) y]
    apply Nat.mul_le_mul_left
    exact Nat.le_add_left net x
  exact Nat.div_le_of_le_mul h1

/-- The split objective at any point is bounded by the sum of reserves.
    g(a) = f₀(a) + f₁(D-a) ≤ y₀ + y₁. -/
theorem split_objective_bounded
    (y0 y1 net0 net1 x0 x1 : Nat)
    (hx0 : x0 > 0) (hx1 : x1 > 0) :
    y0 * net0 / (x0 + net0) + y1 * net1 / (x1 + net1) ≤ y0 + y1 := by
  have h0 := cpmm_output_bounded y0 net0 x0 hx0
  have h1 := cpmm_output_bounded y1 net1 x1 hx1
  omega

/-- Near-unimodality: If the continuous function g_c is strictly concave,
    and the integer function g differs from g_c by at most δ per term,
    then for any three points a₁ < a₂ < a₃:
      g(a₂) ≥ min(g(a₁), g(a₃)) - 2δ

    We prove the case δ=1 (floor perturbation of each pool output).
    This means g(a₂) ≥ min(g(a₁), g(a₃)) - 2.

    Note: We state this as a conditional theorem requiring that the
    continuous interpolation holds. -/
theorem near_unimodal_from_concave
    (g gc : Nat → Nat)
    (a1 a2 a3 : Nat)
    (_h_order : a1 < a2 ∧ a2 < a3)
    (h_concave_mid : gc a2 ≥ min (gc a1) (gc a3))
    (h_close : ∀ a, g a ≤ gc a + 1 ∧ gc a ≤ g a + 1) :
    g a2 + 2 ≥ min (g a1) (g a3) := by
  have hg2 := (h_close a2).2  -- gc a2 ≤ g a2 + 1
  have hgc1 := (h_close a1).1  -- g a1 ≤ gc a1 + 1
  have hgc3 := (h_close a3).1  -- g a3 ≤ gc a3 + 1
  -- gc a2 ≥ min (gc a1) (gc a3)
  -- gc a2 ≤ g a2 + 1
  -- g a1 ≤ gc a1 + 1, so gc a1 ≥ g a1 - 1 (in Nat, this needs care)
  -- Combining: g a2 + 1 ≥ gc a2 ≥ min (gc a1) (gc a3)
  -- And gc a_i ≤ g a_i + 1, so min (gc a1) (gc a3) ≤ min (g a1 + 1) (g a3 + 1)
  -- Wait, min goes the wrong way with ≤.
  -- We need: min (gc a1) (gc a3) ≥ min (g a1) (g a3) - 1
  -- Because gc a_i ≥ g a_i - 1 (but in Nat we need g a_i ≤ gc a_i + 1)
  omega

/-- Coarse exponent witness used when budgeting a ternary-style search.

    The conclusion only proves that some bounded `k` satisfies `3^k > D`.
    It does not model interval updates, use `W` in the conclusion, or prove
    convergence of the runtime search implementation. -/
theorem ternary_convergence_steps
    (D W : Nat) (_hD : D > 0) (_hW : W > 0) (_hWD : W ≤ D) :
    -- After ceil(log2(D)) steps, interval width ≤ D / 2^ceil(log2(D))
    -- We prove the simpler bound: 3^k > D/W → width < W after k steps
    -- using the fact that each step reduces by factor 2/3
    ∃ k : Nat, k ≤ 2 * (Nat.log2 D + 1) ∧ 3 ^ k > D := by
  -- 3^k grows faster than 2^k, so k = 2*(log2 D + 1) suffices
  -- since 3^(2*(log2 D + 1)) ≥ 2^(2*(log2 D + 1)) ≥ 2^(log2 D + 1) > D
  refine ⟨2 * (Nat.log2 D + 1), Nat.le_refl _, ?_⟩
  have h1 : D < 2 ^ (Nat.log2 D + 1) := Nat.lt_log2_self
  have h2 : (2 : Nat) ≤ 3 := by omega
  have h3 : 2 ^ (2 * (Nat.log2 D + 1)) ≤ 3 ^ (2 * (Nat.log2 D + 1)) :=
    Nat.pow_le_pow_left h2 _
  have h4 : 2 ^ (Nat.log2 D + 1) ≤ 2 ^ (2 * (Nat.log2 D + 1)) := by
    apply Nat.pow_le_pow_right
    · omega
    · omega
  omega

/-- Arithmetic sanity check for the proposed expression
    `4 * (log2 D + 1) + 104`.

    The theorem establishes only that this expression is at least `108`.
    It is not an upper bound on an implementation evaluation counter. -/
theorem dtssr_eval_bound (D : Nat) (_hD : D > 0) :
    4 * (Nat.log2 D + 1) + 104 ≥ 4 + 104 := by
  omega

/-- Numeric evaluation of the proposed expression at `D = 1000000`. -/
theorem dtssr_eval_witness_1M :
    4 * (Nat.log2 1000000 + 1) + 104 ≤ 184 := by native_decide

/-- Numeric evaluation of the proposed expression at `D = 10000`. -/
theorem dtssr_eval_witness_10K :
    4 * (Nat.log2 10000 + 1) + 104 ≤ 160 := by native_decide

/-- Numeric evaluation of the proposed expression at `D = 1000000000`. -/
theorem dtssr_eval_witness_1B :
    4 * (Nat.log2 1000000000 + 1) + 104 ≤ 224 := by native_decide

/-- The DTSSR split is always at least as good as any single-pool allocation.
    If g(a*) is the DTSSR output and f₀(D), f₁(D) are single-pool outputs,
    then g(a*) ≥ max(f₀(D), f₁(D)). This follows from the fact that DTSSR
    evaluates a=0 and a=D as candidates. -/
theorem dtssr_beats_single_pool
    (f0 f1 g : Nat → Nat)
    (D a_star : Nat)
    (h_g : ∀ a, a ≤ D → g a = f0 a + f1 (D - a))
    (h_dtssr : g a_star ≥ g 0 ∧ g a_star ≥ g D) :
    g a_star ≥ f1 D ∧ g a_star ≥ f0 D := by
  constructor
  · -- `g(0) = f0(0) + f1(D) ≥ f1(D)` by nonnegativity in `Nat`.
    have hg0 := h_g 0 (Nat.zero_le D)
    simp at hg0
    omega
  · have hgD := h_g D (Nat.le_refl D)
    simp at hgD
    omega

end SplitRoutingUnimodality
end Proofs
