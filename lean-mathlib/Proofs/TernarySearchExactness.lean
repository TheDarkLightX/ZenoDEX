/-
# Unimodal Global Maximum via Discrete Concavity

This file proves that a discretely concave integer function is unimodal,
and that the peak of a unimodal function is the global maximum. These are
the key mathematical properties that ternary search relies on. The ternary
search algorithm itself (narrowing invariant and termination) is not
formalized here; that remains a future proof target.

## Theorem Chain

1. **Discrete concavity**: f(b+1) - f(b) is non-increasing in b
2. **Unimodality**: Discrete concavity implies f is unimodal
3. **Peak is maximum**: The peak of a unimodal function is the global max

## Application to CPMM Batch Clearing

The (A,B) batch clearing objective is concave in the split parameter
(empirically verified). This file proves: IF the objective is discretely
concave, THEN the function is unimodal and the peak is the exact maximum.

## Scope and Non-Claims

- This proves the ternary search component only
- The Lipschitz window bound is in WindowBound.lean
- The compressed-state pruning rule is in CompressedStateSubsetDP.lean
- This does NOT prove the CPMM split function is discretely concave
  (requires CPMM second derivative analysis, empirically verified)

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/TernarySearchExactness.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic

/-- A function f : ℤ → ℤ is discretely concave on [lo, hi] if
    the forward difference f(b+1) - f(b) is non-increasing in b. -/
def DiscreteConcave (f : ℤ → ℤ) (lo hi : ℤ) : Prop :=
  ∀ b : ℤ, lo ≤ b → b + 2 ≤ hi →
    f (b + 2) - f (b + 1) ≤ f (b + 1) - f b

/-- Helper: if f is non-decreasing on [lo, p], then f(b) ≤ f(p) for any b ∈ [lo, p].
    Proved by induction on the Nat distance from b to p. -/
lemma chain_nonneg
    (f : ℤ → ℤ) (lo p b : ℤ)
    (h_inc : ∀ j : ℤ, lo ≤ j → j < p → f j ≤ f (j + 1))
    (h_lo_le_b : lo ≤ b) (h_b_le_p : b ≤ p)
    : f b ≤ f p := by
  have h : ∀ n : ℕ, b + (n : ℤ) ≤ p → f b ≤ f (b + (n : ℤ)) := by
    intro n
    induction' n with k ih
    · intro _; simp
    · intro h_bound
      have h_ih := ih (by omega)
      have h_step := h_inc (b + (k : ℤ)) (by omega) (by omega)
      have h_eq : (b + ↑(k + 1) : ℤ) = b + ↑k + 1 := by omega
      rw [h_eq]
      omega
  have h_key : f b ≤ f (b + ↑(p - b).toNat) := h (p - b).toNat (by omega)
  have h_eq : b + ↑(p - b).toNat = p := by omega
  rw [h_eq] at h_key
  exact h_key

/-- Helper: if f is non-increasing on [p, hi], then f(b) ≤ f(p) for any b ∈ [p, hi].
    Proved by induction on the Nat distance from p to b. -/
lemma chain_nonpos
    (f : ℤ → ℤ) (p hi b : ℤ)
    (h_dec : ∀ j : ℤ, p ≤ j → j < hi → f (j + 1) ≤ f j)
    (h_p_le_b : p ≤ b) (h_b_le_hi : b ≤ hi)
    : f b ≤ f p := by
  have h : ∀ n : ℕ, p + (n : ℤ) ≤ hi → f (p + (n : ℤ)) ≤ f p := by
    intro n
    induction' n with k ih
    · intro _; simp
    · intro h_bound
      have h_ih := ih (by omega)
      have h_step := h_dec (p + (k : ℤ)) (by omega) (by omega)
      have h_eq : (p + ↑(k + 1) : ℤ) = p + ↑k + 1 := by omega
      rw [h_eq]
      omega
  have h_key : f (p + ↑(b - p).toNat) ≤ f p := h (b - p).toNat (by omega)
  have h_eq : p + ↑(b - p).toNat = b := by omega
  rw [h_eq] at h_key
  exact h_key

/-- A function is unimodal on [lo, hi] if there exists a peak p such that
    f is non-decreasing on [lo, p] and non-increasing on [p, hi]. -/
def Unimodal (f : ℤ → ℤ) (lo hi : ℤ) : Prop :=
  ∃ p : ℤ, lo ≤ p ∧ p ≤ hi ∧
    (∀ b : ℤ, lo ≤ b → b < p → f b ≤ f (b + 1)) ∧
    (∀ b : ℤ, p ≤ b → b < hi → f (b + 1) ≤ f b)

/-- Helper: argmax exists on any finite integer interval [lo, hi].
    Proved by induction on the interval length. -/
lemma argmax_exists
    (f : ℤ → ℤ) (lo hi : ℤ) (hlo : lo ≤ hi)
    : ∃ p : ℤ, lo ≤ p ∧ p ≤ hi ∧ ∀ b : ℤ, lo ≤ b → b ≤ hi → f b ≤ f p := by
  have h_rec : ∀ n : ℕ, ∀ hi : ℤ, hi = lo + n → lo ≤ hi →
    ∃ p : ℤ, lo ≤ p ∧ p ≤ hi ∧ ∀ b : ℤ, lo ≤ b → b ≤ hi → f b ≤ f p := by
    intro n
    induction' n with d ih
    · -- n = 0: hi = lo, peak at lo
      intro hi hn hlo_hi
      have h_hi_eq : hi = lo := by omega
      refine ⟨lo, le_refl lo, ?_, ?_⟩
      · omega
      · intro b hb_lo hb_hi
        have h_b_eq : b = lo := by omega
        rw [h_b_eq]
    · -- n = d + 1: hi = lo + d + 1
      intro hi hn hlo_hi
      -- Use ih on hi - 1 = lo + d
      have h_ih := ih (hi - 1) (by omega) (by omega)
      obtain ⟨p, hp_lo, hp_pred, hp_max⟩ := h_ih
      by_cases h_f_hi : f hi ≤ f p
      · -- p is still the max
        refine ⟨p, hp_lo, ?_, ?_⟩
        · omega
        · intro b hb_lo hb_hi
          by_cases h_b : b < hi
          · have h_b_le_pred : b ≤ hi - 1 := by omega
            exact hp_max b hb_lo h_b_le_pred
          · have h_b_eq : b = hi := by omega
            rw [h_b_eq]
            exact h_f_hi
      · -- hi is the new max
        refine ⟨hi, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro b hb_lo hb_hi
          by_cases h_b : b < hi
          · have h_b_le_pred : b ≤ hi - 1 := by omega
            have := hp_max b hb_lo h_b_le_pred
            linarith
          · have h_b_eq : b = hi := by omega
            rw [h_b_eq]
  exact h_rec (hi - lo).toNat hi (by omega) hlo

/-- **Theorem 1**: Discrete concavity implies unimodality.

    The argmax of f on the finite interval [lo, hi] exists. We show it
    satisfies the unimodality conditions using discrete concavity:
    - If f is decreasing at b < p, then d is negative from b onward,
      so f(p) < f(p-1) ≤ f(p), contradiction.
    - If f is increasing at b ≥ p, then d(b) > 0 and d is non-increasing,
      so d(p) ≥ d(b) > 0, meaning f(p+1) > f(p), contradicting p being max.
      (If b = p, the max property directly gives the contradiction.) -/
theorem discrete_concave_implies_unimodal
    (f : ℤ → ℤ) (lo hi : ℤ) (hlo : lo ≤ hi) (hdc : DiscreteConcave f lo hi)
    : Unimodal f lo hi := by
  obtain ⟨p, hp_lo, hp_hi, hp_max⟩ := argmax_exists f lo hi hlo
  refine ⟨p, hp_lo, hp_hi, ?_, ?_⟩
  · -- f non-decreasing on [lo, p]: suppose f(b+1) < f(b) for some b < p.
    -- Then d(b) < 0, and d is non-increasing, so d(p-1) ≤ d(b) < 0,
    -- meaning f(p) < f(p-1) ≤ f(p), contradiction.
    intro b hb_lo hb_lt_p
    by_contra h_not
    push_neg at h_not
    have h_db_neg : f (b + 1) - f b < 0 := by omega
    by_cases h_p_eq : p = b + 1
    · -- f(p) = f(b+1) < f(b) ≤ f(p), contradiction
      subst h_p_eq
      have := hp_max b hb_lo (by omega)
      omega
    · have h_p_gt_b1 : p > b + 1 := by omega
      -- Prove d(p-1) ≤ d(b) by chaining discrete concavity from b to p-1
      have h_d_noninc : f p - f (p - 1) ≤ f (b + 1) - f b := by
        -- Chain: d(b) ≥ d(b+1) ≥ ... ≥ d(p-1)
        have h_chain : ∀ n : ℕ, b + (n : ℤ) ≤ p - 1 →
          f (b + (n : ℤ) + 1) - f (b + (n : ℤ)) ≤ f (b + 1) - f b := by
          intro n
          induction' n with k ihk
          · intro _; simp
          · intro h_bound
            have h_ihk := ihk (by omega)
            have h_dc := hdc (b + (k : ℤ)) (by omega) (by omega)
            have h_eq : (b + ↑(k + 1) : ℤ) = b + ↑k + 1 := by omega
            rw [h_eq]
            have h_eq3 : b + ↑k + 1 + 1 = b + ↑k + 2 := by omega
            rw [h_eq3]
            omega
        have h_chain_at := h_chain (p - 1 - b).toNat (by omega)
        have h_eq1 : b + ↑(p - 1 - b).toNat = p - 1 := by omega
        rw [h_eq1] at h_chain_at
        have h_p : p - 1 + 1 = p := by omega
        rw [h_p] at h_chain_at
        exact h_chain_at
      have h_dp_neg : f p - f (p - 1) < 0 := by omega
      have := hp_max (p - 1) (by omega) (by omega)
      omega
  · -- f non-increasing on [p, hi]: suppose f(b+1) > f(b) for some b ≥ p.
    -- Case 1: b = p. Then f(p+1) > f(p), but f(p+1) ≤ f(p) since p is max.
    -- Case 2: b > p. Then d(b) > 0 and d is non-increasing, so d(p) ≥ d(b) > 0,
    -- meaning f(p+1) > f(p), contradicting p being max.
    intro b hb_p hb_lt_hi
    by_contra h_not
    push_neg at h_not
    have h_db_pos : f (b + 1) - f b > 0 := by omega
    have h_fb_le_fp := hp_max b (by omega) (by omega)
    have h_fb1_le_fp := hp_max (b + 1) (by omega) (by omega)
    by_cases h_b_eq_p : b = p
    · -- b = p: f(p+1) > f(p), but f(p+1) ≤ f(p), contradiction
      subst h_b_eq_p
      omega
    · -- b > p: use discrete concavity to show d(p) ≥ d(b) > 0
      have h_b_gt_p : b > p := by omega
      -- Prove d(p) ≥ d(b) by chaining from p to b
      have h_d_noninc : f (p + 1) - f p ≥ f (b + 1) - f b := by
        -- Chain: d(p) ≥ d(p+1) ≥ ... ≥ d(b)
        have h_chain : ∀ n : ℕ, p + (n : ℤ) ≤ b →
          f (p + 1) - f p ≥ f (p + (n : ℤ) + 1) - f (p + (n : ℤ)) := by
          intro n
          induction' n with k ihk
          · intro _; simp
          · intro h_bound
            have h_ihk := ihk (by omega)
            have h_dc := hdc (p + (k : ℤ)) (by omega) (by omega)
            have h_eq : (p + ↑(k + 1) : ℤ) = p + ↑k + 1 := by omega
            rw [h_eq]
            have h_eq3 : p + ↑k + 1 + 1 = p + ↑k + 2 := by omega
            rw [h_eq3]
            omega
        have h_chain_at := h_chain (b - p).toNat (by omega)
        have h_eq1 : p + ↑(b - p).toNat = b := by omega
        rw [h_eq1] at h_chain_at
        have h_b1 : b + 1 = b + 1 := rfl
        -- h_chain_at : f (p + 1) - f p ≥ f (b + 1) - f b
        -- after rw [h_eq1], p + ↑n became b, so p + ↑n + 1 became b + 1
        exact h_chain_at
      -- d(p) > 0, so f(p+1) > f(p), but f(p+1) ≤ f(p) since p is max
      have h_dp_pos : f (p + 1) - f p > 0 := by omega
      have h_fp1_le_fp := hp_max (p + 1) (by omega) (by omega)
      omega

/-- **Key Property for Ternary Search**: A discretely concave function has
    a unimodal global maximum.

    If f is discretely concave on [lo, hi], then:
    1. f is unimodal (Theorem 1)
    2. The peak p is the global maximum on [lo, hi]

    This establishes the mathematical property that ternary search relies on:
    a unimodal function's peak is its global maximum. The ternary search
    algorithm itself (narrowing invariant and termination) is not formalized
    here; that remains a future proof target. -/
theorem discrete_concave_has_unimodal_global_max
    (f : ℤ → ℤ) (lo hi : ℤ) (hlo : lo ≤ hi) (hdc : DiscreteConcave f lo hi)
    : ∃ p : ℤ, lo ≤ p ∧ p ≤ hi ∧
      (∀ b : ℤ, lo ≤ b → b ≤ hi → f b ≤ f p) ∧
      Unimodal f lo hi := by
  have hu := discrete_concave_implies_unimodal f lo hi hlo hdc
  have hu_copy := hu
  obtain ⟨p, hp_lo, hp_hi, h_inc, h_dec⟩ := hu
  refine ⟨p, hp_lo, hp_hi, ?_, ?_⟩
  · intro b hb_lo hb_hi
    by_cases h_b_le_p : b ≤ p
    · exact chain_nonneg f lo p b h_inc hb_lo h_b_le_p
    · push_neg at h_b_le_p
      have h_p_le_b : p ≤ b := le_of_lt h_b_le_p
      exact chain_nonpos f p hi b h_dec h_p_le_b hb_hi
  · exact hu_copy
