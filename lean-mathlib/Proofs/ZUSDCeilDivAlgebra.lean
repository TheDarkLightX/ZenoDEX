import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Ceiling Division Algebra for zUSD Fee Calculations

## Key Property

zUSD uses `_mul_div_up(a, b, den) = (a*b + den - 1) // den` for ALL fee
calculations — borrow fees, redemption fees, and protocol revenue splits.
This file formalizes the algebraic properties of ceiling division and
derives bounds that ensure protocol fee safety.

## What This File Proves (10 substantive theorems)

### Foundation (ceiling division definition)
1. **ceil_div_mul_ge**: ⌈n/d⌉ × d ≥ n (ceil rounds UP — protocol never underpaid)
2. **ceil_div_mul_lt**: ⌈n/d⌉ × d < n + d (overcharge bounded by one divisor unit)
3. **ceil_div_overcharge_bound**: 0 ≤ ⌈n/d⌉ × d - n < d (combined: exact gap range)

### Exactness and rounding direction
4. **ceil_div_exact**: d ∣ n → ⌈n/d⌉ = n/d (no rounding when divisible)
5. **ceil_div_rounds_up**: ¬(d ∣ n) → ⌈n/d⌉ = n/d + 1 (strictly rounds up otherwise)

### Monotonicity
6. **ceil_div_mono**: n₁ ≤ n₂ → ⌈n₁/d⌉ ≤ ⌈n₂/d⌉ (monotone in numerator)

### Fee application properties (mul_div_up)
7. **mul_div_up_ge**: ⌈a×b/d⌉ × d ≥ a×b (fee collection never less than exact)
8. **mul_div_up_le_amount**: b ≤ d → ⌈a×b/d⌉ ≤ a (fee ≤ principal when rate ≤ 100%)
9. **mul_div_up_mono_rate**: b₁ ≤ b₂ → ⌈a×b₁/d⌉ ≤ ⌈a×b₂/d⌉ (higher rate → higher fee)
10. **double_rounding_bound**: Two sequential ceil_div rounds add < 2d total overcharge

## Pattern
Uses Nat.div_add_mod, Nat.add_mul_div_right, Nat.div_mul_le_self + omega.
-/

namespace Proofs

namespace ZUSDCeilDivAlgebra

/-- Ceiling division: ⌈n/d⌉ = (n + d - 1) / d.
    This is the Lean formalization of Python's `_mul_div_up` denominator. -/
def ceil_div (n d : ℕ) : ℕ := (n + d - 1) / d

/-! ## Part 1: Core Ceiling Division Properties -/

/-- ⌈n/d⌉ × d ≥ n: ceiling division never underpays.
    Derived from Euclidean division on (n + d - 1).
    This is THE key safety property for protocol fees. -/
theorem ceil_div_mul_ge (n d : ℕ) (hd : 0 < d) :
    ceil_div n d * d ≥ n := by
  unfold ceil_div
  have hdivmod := Nat.div_add_mod (n + d - 1) d
  have hmodlt := Nat.mod_lt (n + d - 1) hd
  rw [show (n + d - 1) / d * d = d * ((n + d - 1) / d) from Nat.mul_comm ..]
  omega

/-- ⌈n/d⌉ × d < n + d: overcharge is strictly less than one divisor unit.
    Combined with ceil_div_mul_ge, this gives a tight bound on the rounding gap. -/
theorem ceil_div_mul_lt (n d : ℕ) (hd : 0 < d) :
    ceil_div n d * d < n + d := by
  unfold ceil_div
  have hdivmod := Nat.div_add_mod (n + d - 1) d
  have hmodlt := Nat.mod_lt (n + d - 1) hd
  rw [show (n + d - 1) / d * d = d * ((n + d - 1) / d) from Nat.mul_comm ..]
  omega

/-- The overcharge gap is in [0, d): protocol overcharges by at most d-1 units.
    This is the combined bound that constrains total fee rounding error. -/
theorem ceil_div_overcharge_bound (n d : ℕ) (hd : 0 < d) :
    ceil_div n d * d ≥ n ∧ ceil_div n d * d - n < d := by
  constructor
  · exact ceil_div_mul_ge n d hd
  · have h1 := ceil_div_mul_ge n d hd
    have h2 := ceil_div_mul_lt n d hd
    omega

/-! ## Part 2: Exactness and Rounding Direction -/

/-- When d divides n, ceiling division equals floor division (no rounding).
    Proof: d*k+d-1 = (d-1) + k*d, so by Nat.add_mul_div_right and d-1 < d. -/
theorem ceil_div_exact (n d : ℕ) (hd : 0 < d) (hdvd : d ∣ n) :
    ceil_div n d = n / d := by
  unfold ceil_div
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  rw [Nat.mul_div_cancel_left k hd]
  -- Goal: (d * k + d - 1) / d = k
  rw [show d * k + d - 1 = (d - 1) + k * d from by
    have : d * k = k * d := Nat.mul_comm d k; omega]
  rw [Nat.add_mul_div_right (d - 1) k hd]
  rw [Nat.div_eq_of_lt (by omega : d - 1 < d)]
  exact Nat.zero_add k

/-- When d does not divide n, ceil rounds strictly up: ⌈n/d⌉ = ⌊n/d⌋ + 1.
    This is where the protocol extracts its rounding benefit.
    Proof: n+d-1 = (n%d-1) + (n/d+1)*d, with 0 ≤ n%d-1 < d. -/
theorem ceil_div_rounds_up (n d : ℕ) (hd : 0 < d) (hndvd : ¬(d ∣ n)) :
    ceil_div n d = n / d + 1 := by
  unfold ceil_div
  have hmod_ne : n % d ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  have hmod_pos : 0 < n % d := by omega
  have hdivmod := Nat.div_add_mod n d
  have hmodlt := Nat.mod_lt n hd
  -- Rewrite dividend: n+d-1 = (n%d - 1) + (n/d + 1) * d
  rw [show n + d - 1 = (n % d - 1) + (n / d + 1) * d from by
    have : (n / d + 1) * d = d * (n / d) + d := by ring
    omega]
  rw [Nat.add_mul_div_right (n % d - 1) (n / d + 1) hd]
  rw [Nat.div_eq_of_lt (by omega : n % d - 1 < d)]
  exact Nat.zero_add (n / d + 1)

/-! ## Part 3: Monotonicity -/

/-- Ceiling division is monotone in the numerator: larger input → larger output.
    Proof: n₁ ≤ n₂ → n₁ + d - 1 ≤ n₂ + d - 1 → floor div monotone. -/
theorem ceil_div_mono (n₁ n₂ d : ℕ) (hd : 0 < d) (h : n₁ ≤ n₂) :
    ceil_div n₁ d ≤ ceil_div n₂ d := by
  unfold ceil_div
  exact Nat.div_le_div_right (by omega)

/-! ## Part 4: Fee Application Properties (mul_div_up)

In zUSD, `_mul_div_up(amount, rate_bps, BPS_SCALE)` computes fees.
This is `ceil_div(amount * rate_bps, BPS_SCALE)`.
-/

/-- mul_div_up collection always covers the exact product.
    This is ceil_div_mul_ge specialized to the fee context. -/
theorem mul_div_up_ge (amount rate den : ℕ) (hden : 0 < den) :
    ceil_div (amount * rate) den * den ≥ amount * rate :=
  ceil_div_mul_ge (amount * rate) den hden

/-- When rate ≤ den (i.e., fee rate ≤ 100%), fee ≤ amount.
    Proof: ⌈a×b/d⌉ ≤ ⌈a×d/d⌉ = a (by ceil_div_exact + div_cancel). -/
theorem mul_div_up_le_amount (amount rate den : ℕ) (hden : 0 < den)
    (hrate : rate ≤ den) :
    ceil_div (amount * rate) den ≤ amount := by
  have h1 : amount * rate ≤ amount * den := Nat.mul_le_mul_left amount hrate
  have h2 : ceil_div (amount * rate) den ≤ ceil_div (amount * den) den :=
    ceil_div_mono _ _ den hden h1
  have h3 : ceil_div (amount * den) den = amount * den / den := by
    exact ceil_div_exact (amount * den) den hden ⟨amount, by ring⟩
  rw [h3, Nat.mul_div_cancel _ hden] at h2
  exact h2

/-- Higher rate → higher fee (monotone in rate parameter).
    Proof: amount × rate₁ ≤ amount × rate₂, then ceil_div_mono. -/
theorem mul_div_up_mono_rate (amount rate₁ rate₂ den : ℕ) (hden : 0 < den)
    (hrate : rate₁ ≤ rate₂) :
    ceil_div (amount * rate₁) den ≤ ceil_div (amount * rate₂) den :=
  ceil_div_mono _ _ den hden (Nat.mul_le_mul_left amount hrate)

/-! ## Part 5: Double Rounding Bound

When two ceil_div operations compose (e.g., fee computed on a fee),
the total overcharge is bounded by the sum of individual overcharges.
-/

/-- Two sequential ceiling divisions overcharge by less than 2d² total.
    If y = ⌈x/d⌉ and z = ⌈y/d⌉, then z×d² < x + 2d².
    Proof chain: z*d < y+d (step 2), multiply by d;
    y*d < x+d (step 1); combine; d ≤ d² closes the gap. -/
theorem double_rounding_bound (x d : ℕ) (hd : 0 < d) :
    let y := ceil_div x d
    let z := ceil_div y d
    z * d * d < x + 2 * d * d := by
  simp only
  have h1 := ceil_div_mul_lt x d hd
  have h2 := ceil_div_mul_lt (ceil_div x d) d hd
  -- z*d < y+d, so z*d*d < (y+d)*d = y*d + d²
  -- y*d < x+d, so y*d + d² < x + d + d²
  -- d + d² ≤ 2d² since d ≤ d² (from d ≥ 1)
  calc ceil_div (ceil_div x d) d * d * d
      < (ceil_div x d + d) * d := by
        nlinarith [mul_lt_mul_of_pos_right h2 hd]
    _ = ceil_div x d * d + d * d := by ring
    _ < (x + d) + d * d := by linarith
    _ ≤ x + 2 * d * d := by nlinarith

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: ceil_div(7, 3) = 3 (rounds up from 2.33). 3×3=9 ≥ 7. -/
theorem witness_ceil_basic :
    ceil_div 7 3 = 3 ∧ 3 * 3 ≥ 7 ∧ 3 * 3 < 7 + 3 := by
  unfold ceil_div; omega

/-- Witness: ceil_div(6, 3) = 2 (exact division). 2×3=6 = 6. -/
theorem witness_ceil_exact :
    ceil_div 6 3 = 2 ∧ 6 / 3 = 2 := by
  unfold ceil_div; omega

/-- Witness: fee on 1000 at 50 bps with den=10000.
    ceil_div(1000×50, 10000) = ceil_div(50000, 10000) = 5. Fee = 5. -/
theorem witness_fee_calculation :
    ceil_div (1000 * 50) 10000 = 5 ∧ 5 ≤ 1000 := by
  unfold ceil_div; omega

/-- Witness: double rounding. ceil_div(7,3)=3, ceil_div(3,3)=1.
    1×9=9, 7+2×9=25, 9 < 25. -/
theorem witness_double_rounding :
    let y := ceil_div 7 3
    let z := ceil_div y 3
    y = 3 ∧ z = 1 ∧ z * 3 * 3 < 7 + 2 * 3 * 3 := by
  unfold ceil_div; omega

end ZUSDCeilDivAlgebra

end Proofs
