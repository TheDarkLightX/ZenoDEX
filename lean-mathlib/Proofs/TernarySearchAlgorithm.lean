/-
# Ternary Search Algorithm: One-Step Narrowing Invariant and Shrinkage

This file formalizes ONE STEP of the ternary search algorithm, proving:
1. **One-step narrowing invariant**: After a single step, the leftmost argmax
   remains within the surviving interval (for discretely concave functions).
2. **One-step interval shrinkage**: Each step strictly reduces the interval size.
3. **One-step termination bound**: Each step reduces size by at least 1.

**Scope**: This file proves the one-step properties. It does NOT prove the
recursive algorithm theorem (composing k steps to reach the argmax), nor does
it prove a log-style after-k bound as a checked theorem. The after-k bound at
the end of this file is an informal corollary (not a Lean theorem) derived by
induction from the one-step result.

Combined with `discrete_concave_has_unimodal_global_max` from
TernarySearchExactness.lean and `splitFunctionCont_concave` from
CpmmSplitConcavity.lean, this provides the one-step building blocks for
ternary search verification:
- CpmmSplitConcavity.lean: The CPMM split function has negative second
  forward difference (continuous, under valid-domain hypotheses)
- TernarySearchExactness.lean: Discrete concavity implies unimodal global max
- TernarySearchAlgorithm.lean: One-step narrowing + shrinkage (this file)

## Algorithm

Ternary search on a unimodal function f : ℤ → ℤ on [lo, hi]:
1. If hi - lo ≤ 2, return the argmax of f on {lo, lo+1, ..., hi}
2. Otherwise, compute m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3
3. If f(m1) < f(m2), recurse on [m1+1, hi]
4. If f(m1) ≥ f(m2), recurse on [lo, m2]

## One-Step Narrowing Invariant (for Discretely Concave Functions)

The key one-step invariant: the argmax p* remains in the surviving interval
after a single ternary search step.

Case 3 (f(m1) < f(m2) → [m1+1, hi]):
  If p* ≤ m1, then m1, m2 ≥ p*, so f is non-increasing on [p*, hi],
  giving f(m1) ≥ f(m2), contradiction. So p* > m1, i.e., p* ∈ [m1+1, hi].

Case 4 (f(m1) ≥ f(m2) → [lo, m2]):
  If p* > m2, then m1, m2 < p*, so f is non-decreasing on [lo, p*],
  giving f(m1) ≤ f(m2). Combined: f(m1) = f(m2).
  Since p* is the leftmost argmax, f(m2) < f(p*).
  But f(m1) = f(m2) means the forward differences sum to 0 on [m1, m2-1].
  By discrete concavity (d non-increasing), d(b) ≤ 0 for b ≥ m2,
  so f cannot increase after m2. Contradiction with f(p*) > f(m2).
  So p* ≤ m2, i.e., p* ∈ [lo, m2].

## Scope and Non-Claims

- This proves ONE-STEP narrowing for discretely concave functions
- The recursive algorithm theorem (k-step composition) is NOT proven here
- The continuous CPMM concavity is proven in CpmmSplitConcavity.lean
- The discrete (floor-rounded) version's non-concavity is characterized
  empirically; the one-step narrowing applies when the function IS
  discretely concave

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/TernarySearchAlgorithm.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.TernarySearchExactness

/-- Ternary search step: given f on [lo, hi] with hi - lo > 2,
    compute the next interval [lo', hi'] that contains the argmax.
    Returns (m1+1, hi) if f(m1) < f(m2), or (lo, m2) otherwise. -/
def ternaryStep (f : ℤ → ℤ) (lo hi : ℤ) : ℤ × ℤ :=
  let m1 := lo + (hi - lo) / 3
  let m2 := hi - (hi - lo) / 3
  if f m1 < f m2 then (m1 + 1, hi) else (lo, m2)

/-- Helper: if f is non-increasing on [p, hi] and p ≤ a, then f(a) ≤ f(p).
    This is just chain_nonpos, restated for convenience. -/
lemma noninc_at (f : ℤ → ℤ) (p hi a : ℤ)
    (h_dec : ∀ j : ℤ, p ≤ j → j < hi → f (j + 1) ≤ f j)
    (h_p_le_a : p ≤ a) (h_a_le_hi : a ≤ hi)
    : f a ≤ f p := chain_nonpos f p hi a h_dec h_p_le_a h_a_le_hi

/-- Helper: if f is non-decreasing on [lo, p] and a ≤ p, then f(a) ≤ f(p).
    This is just chain_nonneg, restated for convenience. -/
lemma nondec_at (f : ℤ → ℤ) (lo p a : ℤ)
    (h_inc : ∀ j : ℤ, lo ≤ j → j < p → f j ≤ f (j + 1))
    (h_lo_le_a : lo ≤ a) (h_a_le_p : a ≤ p)
    : f a ≤ f p := chain_nonneg f lo p a h_inc h_lo_le_a h_a_le_p

/-- **Narrowing Invariant**: If f is discretely concave on [lo, hi] with
    argmax p (the leftmost argmax), then after one ternary search step,
    p remains in the new interval.

    This is the key correctness property: the global maximum is never
    eliminated by the narrowing. The proof uses discrete concavity to
    handle the plateau case in step 4. -/
theorem ternary_narrowing_invariant
    (f : ℤ → ℤ) (lo hi p : ℤ)
    (hdc : DiscreteConcave f lo hi)
    (h_p_max : ∀ b : ℤ, lo ≤ b → b ≤ hi → f b ≤ f p)
    (h_p_leftmost : ∀ b : ℤ, lo ≤ b → b < p → f b < f p)
    (h_p_in : lo ≤ p ∧ p ≤ hi)
    (h_hi_gt_lo : hi - lo > 2)
    : (ternaryStep f lo hi).1 ≤ p ∧ p ≤ (ternaryStep f lo hi).2 := by
  obtain ⟨hp_lo, hp_hi⟩ := h_p_in
  -- Prove p is a unimodal peak using discrete concavity
  -- (same argument as discrete_concave_implies_unimodal)
  have h_inc_p : ∀ b : ℤ, lo ≤ b → b < p → f b ≤ f (b + 1) := by
    intro b hb_lo hb_lt_p
    by_contra h_not
    push_neg at h_not
    have h_db_neg : f (b + 1) - f b < 0 := by omega
    by_cases h_p_eq : p = b + 1
    · subst h_p_eq
      have := h_p_max b hb_lo (by omega)
      omega
    · have h_p_gt_b1 : p > b + 1 := by omega
      have h_d_noninc : f p - f (p - 1) ≤ f (b + 1) - f b := by
        have h_chain : ∀ n : ℕ, b + (n : ℤ) ≤ p - 1 →
          f (b + (n : ℤ) + 1) - f (b + (n : ℤ)) ≤ f (b + 1) - f b := by
          intro n
          induction' n with k ihk
          · intro _; simp
          · intro h_bound
            have h_ihk := ihk (by omega)
            have h_dc := hdc (b + (k : ℤ)) (by omega) (by omega)
            have h_eq : (b + ↑(k + 1) : ℤ) = b + ↑k + 1 := by omega
            rw [h_eq, show b + ↑k + 1 + 1 = b + ↑k + 2 from by omega]
            omega
        have h_chain_at := h_chain (p - 1 - b).toNat (by omega)
        rw [show b + ↑(p - 1 - b).toNat = p - 1 from by omega] at h_chain_at
        rw [show p - 1 + 1 = p from by omega] at h_chain_at
        exact h_chain_at
      have h_dp_neg : f p - f (p - 1) < 0 := by omega
      have := h_p_max (p - 1) (by omega) (by omega)
      omega
  have h_dec_p : ∀ b : ℤ, p ≤ b → b < hi → f (b + 1) ≤ f b := by
    intro b hb_p hb_lt_hi
    by_contra h_not
    push_neg at h_not
    have h_db_pos : f (b + 1) - f b > 0 := by omega
    have h_fb_le_fp := h_p_max b (by omega) (by omega)
    have h_fb1_le_fp := h_p_max (b + 1) (by omega) (by omega)
    by_cases h_b_eq_p : b = p
    · subst h_b_eq_p; omega
    · have h_b_gt_p : b > p := by omega
      have h_d_noninc : f (p + 1) - f p ≥ f (b + 1) - f b := by
        have h_chain : ∀ n : ℕ, p + (n : ℤ) ≤ b →
          f (p + 1) - f p ≥ f (p + (n : ℤ) + 1) - f (p + (n : ℤ)) := by
          intro n
          induction' n with k ihk
          · intro _; simp
          · intro h_bound
            have h_ihk := ihk (by omega)
            have h_dc := hdc (p + (k : ℤ)) (by omega) (by omega)
            have h_eq : (p + ↑(k + 1) : ℤ) = p + ↑k + 1 := by omega
            rw [h_eq, show p + ↑k + 1 + 1 = p + ↑k + 2 from by omega]
            omega
        have h_chain_at := h_chain (b - p).toNat (by omega)
        rw [show p + ↑(b - p).toNat = b from by omega] at h_chain_at
        exact h_chain_at
      have h_dp_pos : f (p + 1) - f p > 0 := by omega
      have h_fp1_le_fp := h_p_max (p + 1) (by omega) (by omega)
      omega

  -- Define m1 and m2 as explicit values
  let m1 := lo + (hi - lo) / 3
  let m2 := hi - (hi - lo) / 3
  have h_lo_le_m1 : lo ≤ m1 := by omega
  have h_m1_lt_hi : m1 < hi := by omega
  have h_lo_lt_m2 : lo < m2 := by omega
  have h_m2_le_hi : m2 ≤ hi := by omega
  have h_m1_lt_m2 : m1 < m2 := by omega
  have h_m1_le_m2 : m1 ≤ m2 := le_of_lt h_m1_lt_m2

  -- Unfold ternaryStep and split
  show (if f m1 < f m2 then (m1 + 1, hi) else (lo, m2)).1 ≤ p ∧
       p ≤ (if f m1 < f m2 then (m1 + 1, hi) else (lo, m2)).2
  split
  · -- Case f(m1) < f(m2): new interval is [m1+1, hi]
    -- Show p > m1 (i.e., p ≥ m1+1)
    refine ⟨?_, hp_hi⟩
    show m1 + 1 ≤ p
    by_contra h_not
    push_neg at h_not
    -- h_not : p ≤ m1, so m1, m2 ≥ p, f non-increasing on [p, hi]
    -- f(m1) ≥ f(m2) since m1 ≤ m2 and both ≥ p
    have h_fm1_ge_fm2 : f m1 ≥ f m2 := by
      -- f non-increasing on [p, hi]: f(m1) ≥ f(m2) when p ≤ m1 ≤ m2
      have h_chain : ∀ n : ℕ, m1 + (n : ℤ) ≤ m2 → f (m1 + (n : ℤ)) ≤ f m1 := by
        intro n
        induction' n with k ihk
        · intro _; simp
        · intro h_bound
          have h_ihk := ihk (by omega)
          have h_step := h_dec_p (m1 + (k : ℤ)) (by omega) (by omega)
          have h_eq : (m1 + ↑(k + 1) : ℤ) = m1 + ↑k + 1 := by omega
          rw [h_eq]
          omega
      have h_key := h_chain (m2 - m1).toNat (by omega)
      rw [show m1 + ↑(m2 - m1).toNat = m2 from by omega] at h_key
      exact h_key
    omega -- contradiction with f(m1) < f(m2)
  · -- Case f(m1) ≥ f(m2): new interval is [lo, m2]
    -- Show p ≤ m2
    refine ⟨hp_lo, ?_⟩
    show p ≤ m2
    by_contra h_not
    push_neg at h_not
    -- h_not : p > m2, so m1, m2 < p, f non-decreasing on [lo, p]
    -- f(m1) ≤ f(m2) since m1 ≤ m2 < p and f non-decreasing
    have h_fm1_le_fm2 : f m1 ≤ f m2 := by
      have h_chain : ∀ n : ℕ, m1 + (n : ℤ) ≤ m2 → f m1 ≤ f (m1 + (n : ℤ)) := by
        intro n
        induction' n with k ihk
        · intro _; simp
        · intro h_bound
          have h_ihk := ihk (by omega)
          have h_step := h_inc_p (m1 + (k : ℤ)) (by omega) (by omega)
          have h_eq : (m1 + ↑(k + 1) : ℤ) = m1 + ↑k + 1 := by omega
          rw [h_eq]
          omega
      have h_key := h_chain (m2 - m1).toNat (by omega)
      rw [show m1 + ↑(m2 - m1).toNat = m2 from by omega] at h_key
      exact h_key
    -- Combined with f(m1) ≥ f(m2): f(m1) = f(m2)
    have h_f_eq : f m1 = f m2 := by omega
    -- f(m2) < f(p) since p is leftmost argmax and m2 < p
    have h_fm2_lt_fp : f m2 < f p := h_p_leftmost m2 (by omega) (by omega)
    -- Key: f(m1) = f(m2) and f non-decreasing on [m1, m2] ⟹ f constant on [m1, m2]
    -- So d(m1) = f(m1+1) - f(m1) = 0. By discrete concavity, d(b) ≤ d(m1) = 0 for b ≥ m1.
    -- So f is non-increasing from m1, hence f(p) ≤ f(m2). Contradiction with f(m2) < f(p).

    -- Step 1: f is constant on [m1, m2], so d(m1) = 0
    have h_d_m1_eq_0 : f (m1 + 1) - f m1 = 0 := by
      -- f non-decreasing on [lo, p], m1 < m1+1 ≤ m2 < p
      have h_fm1_le_fm1p1 : f m1 ≤ f (m1 + 1) := h_inc_p m1 h_lo_le_m1 (by omega)
      -- f(m1) = f(m2) and f(m1) ≤ f(m1+1) ≤ ... ≤ f(m2) = f(m1)
      -- So f(m1+1) = f(m1)
      have h_fm1p1_le_fm2 : f (m1 + 1) ≤ f m2 := by
        have h_chain : ∀ n : ℕ, (m1 + 1) + (n : ℤ) ≤ m2 → f (m1 + 1) ≤ f ((m1 + 1) + (n : ℤ)) := by
          intro n
          induction' n with k ihk
          · intro _; simp
          · intro h_bound
            have h_ihk := ihk (by omega)
            have h_step := h_inc_p ((m1 + 1) + (k : ℤ)) (by omega) (by omega)
            have h_eq : ((m1 + 1) + ↑(k + 1) : ℤ) = (m1 + 1) + ↑k + 1 := by omega
            rw [h_eq]
            omega
        have h_key := h_chain (m2 - (m1 + 1)).toNat (by omega)
        rw [show (m1 + 1) + ↑(m2 - (m1 + 1)).toNat = m2 from by omega] at h_key
        exact h_key
      -- f(m1) ≤ f(m1+1) ≤ f(m2) = f(m1), so f(m1+1) = f(m1)
      omega
    -- Step 2: d non-increasing and d(m1) = 0 ⟹ d(b) ≤ 0 for b ≥ m1
    -- So f(b+1) ≤ f(b) for b ≥ m1, meaning f is non-increasing from m1
    have h_f_noninc_from_m1 : ∀ b : ℤ, m1 ≤ b → b < p → f (b + 1) ≤ f b := by
      intro b hb_lo hb_lt
      -- Chain: d(b) ≤ d(m1) = 0
      have h_d_chain : ∀ n : ℕ, m1 + (n : ℤ) ≤ b →
        f (m1 + (n : ℤ) + 1) - f (m1 + (n : ℤ)) ≤ f (m1 + 1) - f m1 := by
        intro n
        induction' n with k ihk
        · intro _; simp  -- n=0: d(m1) ≤ d(m1) ✓
        · intro h_bound
          have h_ihk := ihk (by omega)
          have h_dc := hdc (m1 + (k : ℤ)) (by omega) (by omega)
          have h_eq : (m1 + ↑(k + 1) : ℤ) = m1 + ↑k + 1 := by omega
          rw [h_eq, show m1 + ↑k + 1 + 1 = m1 + ↑k + 2 from by omega]
          omega
      have h_key := h_d_chain (b - m1).toNat (by omega)
      rw [show m1 + ↑(b - m1).toNat = b from by omega] at h_key
      -- h_key : d(b) ≤ d(m1) = 0, so f(b+1) ≤ f(b)
      omega
    -- Step 3: f(p) ≤ f(m2) by chaining non-increasing from m2 to p
    have h_fp_le_fm2 : f p ≤ f m2 := by
      have h_chain : ∀ n : ℕ, m2 + (n : ℤ) ≤ p → f (m2 + (n : ℤ)) ≤ f m2 := by
        intro n
        induction' n with k ihk
        · intro _; simp
        · intro h_bound
          have h_ihk := ihk (by omega)
          have h_step := h_f_noninc_from_m1 (m2 + (k : ℤ)) (by omega) (by omega)
          have h_eq : (m2 + ↑(k + 1) : ℤ) = m2 + ↑k + 1 := by omega
          rw [h_eq]
          omega
      have h_key := h_chain (p - m2).toNat (by omega)
      rw [show m2 + ↑(p - m2).toNat = p from by omega] at h_key
      exact h_key
    -- Contradiction: f(m2) < f(p) and f(p) ≤ f(m2)
    omega

/-- **Interval Shrinkage**: Each ternary search step reduces the interval size.
    The new interval is strictly smaller than the original. -/
theorem ternary_step_shrinks_interval
    (f : ℤ → ℤ) (lo hi : ℤ) (h_hi_gt_lo : hi - lo > 2)
    : (ternaryStep f lo hi).2 - (ternaryStep f lo hi).1 < hi - lo := by
  let m1 := lo + (hi - lo) / 3
  let m2 := hi - (hi - lo) / 3
  have h_third_pos : (hi - lo) / 3 ≥ 1 := by omega
  show (if f m1 < f m2 then (m1 + 1, hi) else (lo, m2)).2 -
       (if f m1 < f m2 then (m1 + 1, hi) else (lo, m2)).1 < hi - lo
  split
  · omega
  · omega

/-- **One-Step Termination Bound**: A single ternary search step reduces
    the interval size by at least 1.

    This is the one-step bound. The informal after-k corollary (interval
    size ≤ max(2, (hi-lo) - k) after k steps) follows by induction but is
    NOT proven as a checked theorem here. -/
theorem ternary_termination_bound
    (f : ℤ → ℤ) (lo hi : ℤ) (h_hi_gt_lo : hi - lo > 2)
    : (ternaryStep f lo hi).2 - (ternaryStep f lo hi).1 ≤ hi - lo - 1 := by
  have h := ternary_step_shrinks_interval f lo hi h_hi_gt_lo
  omega
