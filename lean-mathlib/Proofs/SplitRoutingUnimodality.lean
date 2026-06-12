import Proofs.GaloisSplitCertificate

/-!
# Split Routing Trisection (DTSSR): Local Discard Lemmas

The mathematical foundation for the Discrete Ternary Search Split Router
(DTSSR): for a **discretely concave** objective on `{0,...,D}`, the local
discard lemmas show which side of two ordered probes is dominated. The file also
records bounded-output sanity lemmas, a ±1 perturbation lemma, and an arithmetic
step-budget fact. It does not prove an end-to-end trisection implementation.

## Key theorems

| # | Name | Statement |
|---|------|-----------|
| 1 | `discard_left` | f(m₁) < f(m₂) → every j ≤ m₁ is strictly beaten by m₁+1 |
| 2 | `discard_right` | f(m₂) ≤ f(m₁) → every j ≥ m₂−1 is (weakly) dominated by m₂−1 |
| 3 | `trisect_keep_right` | f(m₁) < f(m₂) → the max over [m₁+1, D] is the global max |
| 4 | `trisect_keep_left` | f(m₂) ≤ f(m₁) → the max over [0, m₂−1] is the global max |
| 5 | `cpmm_output_bounded` / `split_objective_bounded` | Output ≤ reserves (sanity bounds) |
| 6 | `near_unimodal_from_concave` | ±1-perturbations of unimodal values stay near-unimodal |
| 7 | `dtssr_beats_single_pool` | DTSSR result ≥ both single-pool allocations |
| 8 | `ternary_step_budget` | arithmetic budget: 2·(log₂ D + 1) gives 3^k > D |

Theorems 1–4 are the **trisection invariant**: at probe points m₁ < m₂,
comparing f(m₁) with f(m₂) always identifies a third of the interval that
cannot strictly contain the optimum. Theorem 8 is the arithmetic half of the
usual geometric-shrink analysis; the interval-update implementation is outside
this Lean file.

The exact invariant applies to discretely concave objectives. The integer CPMM
split objective is only *nearly* concave (grade 2; see
`CPMMConcavity.cpmm_zero_fee_split_nearly_concave`), and fee-aware split routing
can be farther from a concave envelope. Runtime DTSSR-style profiles therefore
remain heuristic unless compared against the exact staircase solver or a
separate certificate. The unconditional 2-comparison zero-fee envelope is
`CPMMConcavity.cpmm_zero_fee_split_approx_certificate`.
-/

namespace Proofs
namespace SplitRoutingUnimodality

open GaloisSplitCertificate

/-! ## Part 1: The trisection invariant

For discretely concave f and probe points m₁ < m₂ ≤ D:

* if f(m₁) < f(m₂), the slope at m₁ is still positive, so f is strictly
  increasing on [0, m₁+1] — the left third [0, m₁] is strictly suboptimal;
* if f(m₂) ≤ f(m₁), the slope into m₂ is already non-positive, so f is
  non-increasing on [m₂−1, D] — the right third [m₂, D] gains nothing
  over m₂−1.

Either way a third of the domain can be discarded WITHOUT losing the
global maximum. -/

/-- **DISCARD LEFT**: under discrete concavity, if the probe comparison
    rises (f(m₁) < f(m₂) with m₁ < m₂), then every point j ≤ m₁ is
    STRICTLY beaten by m₁ + 1. Hence no global maximizer lies in [0, m₁].

    Proof: if the slope at m₁ were ≤ 0, `right_mono` would force
    f(m₂) ≤ f(m₁) — contradiction; so f(m₁) < f(m₁+1). Slopes are
    non-increasing (`nearly_delta_le` at grade 0), so the slope into m₁
    is also positive, and `left_mono` at m₁ dominates all j ≤ m₁. -/
theorem discard_left (f : ℕ → ℤ) (D m₁ m₂ : ℕ)
    (hconc : DiscreteConcave f D)
    (h12 : m₁ < m₂) (h2D : m₂ ≤ D)
    (hlt : f m₁ < f m₂) :
    ∀ j, j ≤ m₁ → f j < f (m₁ + 1) := by
  -- The slope at m₁ is positive.
  have hdelta : f m₁ < f (m₁ + 1) := by
    by_contra hle
    push_neg at hle
    have h := right_mono f D m₁ hconc hle (m₂ - m₁) (by omega)
    rw [show m₁ + (m₂ - m₁) = m₂ by omega] at h
    omega
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
  · exact hdelta
  · -- j < m₁ (so m₁ ≥ 1): the slope into m₁ dominates the positive slope at m₁.
    have hbase : f m₁ ≥ f (m₁ - 1) := by
      have h := nearly_delta_le 0 f D
        ((nearly_zero_iff_concave f D).mpr hconc) (m₁ - 1) 1 (by omega)
      rw [show m₁ - 1 + 1 = m₁ by omega] at h
      -- h : f (m₁ + 1) - f m₁ ≤ (f m₁ - f (m₁ - 1)) + 1 * 0
      simp only [Nat.cast_one, mul_zero] at h
      linarith
    have h := left_mono f D m₁ hconc (by omega) hbase j (by omega)
    linarith

/-- **DISCARD RIGHT**: under discrete concavity, if the probe comparison
    does not rise (f(m₂) ≤ f(m₁) with m₁ < m₂), then every point
    j ∈ [m₂−1, D] is weakly dominated by m₂ − 1. Hence the right third
    can be discarded: a global maximizer survives in [0, m₂−1].

    Proof: if the slope into m₂ were positive, the right-anchored chord
    bound (`nearly_chord_le_rev` at grade 0) would force
    f(m₁) − f(m₂) ≤ (m₂−m₁)·(f(m₂−1) − f(m₂)) ≤ −(m₂−m₁) < 0,
    contradicting f(m₂) ≤ f(m₁). So f(m₂) ≤ f(m₂−1), and `right_mono`
    from m₂ − 1 dominates everything to the right. -/
theorem discard_right (f : ℕ → ℤ) (D m₁ m₂ : ℕ)
    (hconc : DiscreteConcave f D)
    (h12 : m₁ < m₂) (h2D : m₂ ≤ D)
    (hge : f m₂ ≤ f m₁) :
    ∀ j, m₂ - 1 ≤ j → j ≤ D → f j ≤ f (m₂ - 1) := by
  -- The slope into m₂ is non-positive.
  have hdelta : f m₂ ≤ f (m₂ - 1) := by
    by_contra hlt'
    push_neg at hlt'
    have h := nearly_chord_le_rev 0 f D
      ((nearly_zero_iff_concave f D).mpr hconc) m₁ (m₂ - m₁) (by omega)
    rw [show m₁ + (m₂ - m₁) = m₂ by omega] at h
    -- h : 2·(f m₁ − f m₂) ≤ 2·(m₂−m₁)·(f (m₂−1) − f m₂) + 0
    have hn1 : (1 : ℤ) ≤ ((m₂ - m₁ : ℕ) : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have hd1 : f (m₂ - 1) - f m₂ ≤ -1 := by omega
    nlinarith [h, hge, hn1, hd1]
  intro j hjlo hjhi
  have h := right_mono f D (m₂ - 1) hconc
    (by rwa [show m₂ - 1 + 1 = m₂ by omega]) (j - (m₂ - 1)) (by omega)
  rwa [show m₂ - 1 + (j - (m₂ - 1)) = j by omega] at h

/-- **TRISECTION INVARIANT (rising probe)**: when f(m₁) < f(m₂), the
    maximum over the kept interval [m₁+1, D] equals the global maximum:
    every point of {0,...,D} is dominated by some point of [m₁+1, D]. -/
theorem trisect_keep_right (f : ℕ → ℤ) (D m₁ m₂ : ℕ)
    (hconc : DiscreteConcave f D)
    (h12 : m₁ < m₂) (h2D : m₂ ≤ D)
    (hlt : f m₁ < f m₂) :
    ∀ j, j ≤ D → ∃ i, m₁ + 1 ≤ i ∧ i ≤ D ∧ f j ≤ f i := by
  intro j hj
  by_cases hjm : j ≤ m₁
  · exact ⟨m₁ + 1, le_refl _, by omega,
      le_of_lt (discard_left f D m₁ m₂ hconc h12 h2D hlt j hjm)⟩
  · exact ⟨j, by omega, hj, le_refl _⟩

/-- **TRISECTION INVARIANT (non-rising probe)**: when f(m₂) ≤ f(m₁), the
    maximum over the kept interval [0, m₂−1] equals the global maximum:
    every point of {0,...,D} is dominated by some point of [0, m₂−1]. -/
theorem trisect_keep_left (f : ℕ → ℤ) (D m₁ m₂ : ℕ)
    (hconc : DiscreteConcave f D)
    (h12 : m₁ < m₂) (h2D : m₂ ≤ D)
    (hge : f m₂ ≤ f m₁) :
    ∀ j, j ≤ D → ∃ i, i ≤ m₂ - 1 ∧ f j ≤ f i := by
  intro j hj
  by_cases hjm : m₂ - 1 ≤ j
  · exact ⟨m₂ - 1, le_refl _, discard_right f D m₁ m₂ hconc h12 h2D hge j hjm hj⟩
  · exact ⟨j, by omega, le_refl _⟩

/-- Trisection witness: f(x) = −(x−5)² + 25 on {0,...,10} with probes
    m₁ = 3, m₂ = 7. f(3) = 21 > f(7) = 21 is false (21 = 21), so the
    non-rising branch applies and the optimum (a* = 5) indeed survives in
    [0, 6]; with probes m₁ = 1, m₂ = 4, f(1) = 9 < f(4) = 24 rises and the
    optimum survives in [2, 10]. -/
theorem witness_trisection :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    -- non-rising probe pair (3, 7): keep [0, 6], which contains a* = 5
    (f 7 ≤ f 3 ∧ (∀ j, 6 ≤ j → j ≤ 10 → f j ≤ f 6)) ∧
    -- rising probe pair (1, 4): keep [2, 10], which contains a* = 5
    (f 1 < f 4 ∧ (∀ j, j ≤ 1 → f j < f 2)) := by
  constructor
  · constructor
    · norm_num
    · intro j hj₁ hj₂
      exact discard_right _ 10 3 7 witness_concave (by omega) (by omega)
        (by norm_num) j hj₁ hj₂
  · constructor
    · norm_num
    · intro j hj
      exact discard_left _ 10 1 4 witness_concave (by omega) (by omega)
        (by norm_num) j hj

/-! ## Part 2: Output sanity bounds -/

/-- CPMM output floor is bounded: y * net / (x + net) ≤ y, unconditionally.
    This proves the output never exceeds the reserve. -/
theorem cpmm_output_bounded (y net x : Nat) :
    y * net / (x + net) ≤ y := by
  have h1 : y * net ≤ (x + net) * y := by
    rw [Nat.mul_comm (x + net) y]
    apply Nat.mul_le_mul_left
    exact Nat.le_add_left net x
  exact Nat.div_le_of_le_mul h1

/-- The split objective at any point is bounded by the sum of reserves.
    g(a) = f₀(a) + f₁(D-a) ≤ y₀ + y₁. -/
theorem split_objective_bounded
    (y0 y1 net0 net1 x0 x1 : Nat) :
    y0 * net0 / (x0 + net0) + y1 * net1 / (x1 + net1) ≤ y0 + y1 := by
  have h0 := cpmm_output_bounded y0 net0 x0
  have h1 := cpmm_output_bounded y1 net1 x1
  omega

/-! ## Part 3: Floor perturbation stability -/

/-- Near-unimodality: if the integer objective g differs from a reference
    g_c by at most 1 per point, then a midpoint that dominates the
    min-of-endpoints for g_c is within 2 of doing so for g. This is the
    stability margin the DTSSR polish phase absorbs. -/
theorem near_unimodal_from_concave
    (g gc : Nat → Nat)
    (a1 a2 a3 : Nat)
    (_h_order : a1 < a2 ∧ a2 < a3)
    (h_concave_mid : gc a2 ≥ min (gc a1) (gc a3))
    (h_close : ∀ a, g a ≤ gc a + 1 ∧ gc a ≤ g a + 1) :
    g a2 + 2 ≥ min (g a1) (g a3) := by
  have hg2 := (h_close a2).2
  have hgc1 := (h_close a1).1
  have hgc3 := (h_close a3).1
  omega

/-! ## Part 4: Step-count budget

The local discard lemmas provide the logical side of a ternary step. This
section records the arithmetic side: if an implementation shrinks by a factor of
three per step, then 3^k > D steps suffice to reduce {0,...,D} to a
constant-size interval. `ternary_step_budget` shows
k = 2·(log₂ D + 1) is always enough for that arithmetic condition. -/

/-- Step budget: k = 2·(log₂ D + 1) trisection steps satisfy 3^k > D.
    (3^k ≥ 2^k and 2^(log₂ D + 1) > D.) -/
theorem ternary_step_budget
    (D : Nat) (_hD : D > 0) :
    ∃ k : Nat, k ≤ 2 * (Nat.log2 D + 1) ∧ 3 ^ k > D := by
  use 2 * (Nat.log2 D + 1)
  constructor
  · exact Nat.le_refl _
  ·
    have h1 : D < 2 ^ (Nat.log2 D + 1) := Nat.lt_log2_self
    have h2 : (2 : Nat) ≤ 3 := by omega
    have h3 : 2 ^ (2 * (Nat.log2 D + 1)) ≤ 3 ^ (2 * (Nat.log2 D + 1)) :=
      Nat.pow_le_pow_left h2 _
    have h4 : 2 ^ (Nat.log2 D + 1) ≤ 2 ^ (2 * (Nat.log2 D + 1)) := by
      apply Nat.pow_le_pow_right
      · omega
      · omega
    omega

/-- Concrete step budgets: D = 10⁴, 10⁶, 10⁹ need at most 160, 184, 224
    total evaluations (2 per ternary step + polish + canonicalize). -/
theorem witness_eval_budgets :
    4 * (Nat.log2 10000 + 1) + 104 ≤ 160 ∧
    4 * (Nat.log2 1000000 + 1) + 104 ≤ 184 ∧
    4 * (Nat.log2 1000000000 + 1) + 104 ≤ 224 := by
  decide

/-! ## Part 5: DTSSR dominates single-pool allocation -/

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
  · have hg0 := h_g 0 (Nat.zero_le D)
    simp at hg0
    omega
  · have hgD := h_g D (Nat.le_refl D)
    simp at hgD
    omega

end SplitRoutingUnimodality
end Proofs
