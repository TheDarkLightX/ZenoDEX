/-
  Fee Dust Carry Conservation (H-FV-009)

  Models the ZenoDEX fee split with dust carry mechanism.
  The fee is split across 3 buckets (buyback, treasury, rewards) using floor division.
  Rounding remainders accumulate as "dust" carried to the next split.

  Key Results:
  1. fee_split_conservation: buyback + treasury + rewards + dust = fee + old_dust  (exact)
  2. fee_split_dust_bounded: dust ≤ 2  (for 3-way split with any D ≥ 1)
  3. fee_split_outputs_nonneg: all outputs ≥ 0

  The bound dust ≤ 2 follows from:
    D * dust = Σᵢ (total * bᵢ) % D
    Each remainder < D, with 3 terms: sum < 3D, so dust < 3, i.e. dust ≤ 2.

  Non-vacuity: witnessed by concrete numeric examples via native_decide.
-/

import Mathlib.Tactic

namespace FeeDustCarry

/-- The fee split computation: floor-divide total across 3 buckets, carry remainder.
    Takes D (denominator), b1 b2 b3 (bps shares), fee, old_dust as explicit ℕ args. -/
def feeSplit (D b1 b2 b3 fee old_dust : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let total := fee + old_dust
  let out1 := (total * b1) / D
  let out2 := (total * b2) / D
  let out3 := (total * b3) / D
  let distributed := out1 + out2 + out3
  let dust := total - distributed
  (out1, out2, out3, dust)

-- ============================================================================
-- CORE LEMMA: distributed ≤ total
-- ============================================================================

/-- Sum of 3 floor-division terms does not exceed total when b1+b2+b3=D. -/
theorem distributed_le_total (D b1 b2 b3 total : ℕ) (hD : 0 < D)
    (hsum : b1 + b2 + b3 = D) :
    (total * b1) / D + (total * b2) / D + (total * b3) / D ≤ total := by
  suffices h : D * ((total * b1) / D + (total * b2) / D + (total * b3) / D) ≤ D * total by
    exact Nat.le_of_mul_le_mul_left h hD
  have h1 := Nat.div_mul_le_self (total * b1) D
  have h2 := Nat.div_mul_le_self (total * b2) D
  have h3 := Nat.div_mul_le_self (total * b3) D
  calc D * ((total * b1) / D + (total * b2) / D + (total * b3) / D)
      = D * ((total * b1) / D) + D * ((total * b2) / D) + D * ((total * b3) / D) := by ring
    _ ≤ total * b1 + total * b2 + total * b3 := by
        have ha : D * ((total * b1) / D) ≤ total * b1 := by linarith [mul_comm D ((total * b1) / D)]
        have hb : D * ((total * b2) / D) ≤ total * b2 := by linarith [mul_comm D ((total * b2) / D)]
        have hc : D * ((total * b3) / D) ≤ total * b3 := by linarith [mul_comm D ((total * b3) / D)]
        linarith
    _ = total * (b1 + b2 + b3) := by ring
    _ = total * D := by rw [hsum]
    _ = D * total := by ring

-- ============================================================================
-- THEOREM 1: Conservation
-- ============================================================================

/-- Conservation: distributed + dust = fee + old_dust. -/
theorem fee_split_conservation (D b1 b2 b3 fee old_dust : ℕ) (hD : 0 < D)
    (hsum : b1 + b2 + b3 = D) :
    let (o1, o2, o3, dust) := feeSplit D b1 b2 b3 fee old_dust
    o1 + o2 + o3 + dust = fee + old_dust := by
  simp only [feeSplit]
  have hle := distributed_le_total D b1 b2 b3 (fee + old_dust) hD hsum
  omega

-- ============================================================================
-- THEOREM 2: Dust bounded by 2
-- ============================================================================

/-- Dust is at most 2 for any 3-way split. -/
theorem fee_split_dust_bounded (D b1 b2 b3 fee old_dust : ℕ) (hD : 0 < D)
    (hsum : b1 + b2 + b3 = D) :
    let (_, _, _, dust) := feeSplit D b1 b2 b3 fee old_dust
    dust ≤ 2 := by
  simp only [feeSplit]
  set total := fee + old_dust
  set f1 := (total * b1) / D
  set f2 := (total * b2) / D
  set f3 := (total * b3) / D
  set distributed := f1 + f2 + f3
  suffices total ≤ distributed + 2 by omega
  have hmod1 := Nat.div_add_mod (total * b1) D
  have hmod2 := Nat.div_add_mod (total * b2) D
  have hmod3 := Nat.div_add_mod (total * b3) D
  set r1 := (total * b1) % D
  set r2 := (total * b2) % D
  set r3 := (total * b3) % D
  have hr1 := Nat.mod_lt (total * b1) hD
  have hr2 := Nat.mod_lt (total * b2) hD
  have hr3 := Nat.mod_lt (total * b3) hD
  -- Sum the 3 div_add_mod equations: D*fi + ri = total*bi
  have h1 : D * f1 + r1 = total * b1 := hmod1
  have h2 : D * f2 + r2 = total * b2 := hmod2
  have h3 : D * f3 + r3 = total * b3 := hmod3
  have hsum_eq : D * f1 + D * f2 + D * f3 + (r1 + r2 + r3) =
      total * b1 + total * b2 + total * b3 := by linarith
  -- total*b1 + total*b2 + total*b3 = total*D (since b1+b2+b3=D)
  have htb : total * b1 + total * b2 + total * b3 = total * D := by
    nlinarith [mul_add total b1 (b2 + b3), mul_add total b2 b3]
  -- Combine: D*(f1+f2+f3) + (r1+r2+r3) = total*D
  have hle := distributed_le_total D b1 b2 b3 total hD hsum
  have hdmul : D * distributed ≤ D * total := Nat.mul_le_mul_left D hle
  -- D * (total - distributed) = r1+r2+r3
  have hrsum : r1 + r2 + r3 < 3 * D := by omega
  -- Contradiction argument: if total - distributed ≥ 3
  -- then D * 3 ≤ D * (total - distributed) = r1+r2+r3 < 3*D = D*3
  by_contra h
  push_neg at h
  have h3 : distributed + 3 ≤ total := by omega
  have hD3 : D * (distributed + 3) ≤ D * total := Nat.mul_le_mul_left D h3
  -- D*distributed + 3*D ≤ D*total = D*distributed + (r1+r2+r3) + (gap from htb alignment)
  -- More directly: D*distributed + 3*D ≤ total*D (from hD3 after commuting)
  have : D * distributed + 3 * D ≤ D * total := by linarith
  -- But D*distributed + (r1+r2+r3) = total*D (from hsum_eq and htb)
  -- So 3*D ≤ r1+r2+r3, contradicting hrsum
  have hkey2 : D * f1 + D * f2 + D * f3 = D * distributed := by ring
  have : D * distributed + (r1 + r2 + r3) = D * total := by linarith [hsum_eq, htb, hkey2]
  omega

-- ============================================================================
-- THEOREM 3: All outputs non-negative (trivial for ℕ)
-- ============================================================================

/-- All outputs are non-negative. -/
theorem fee_split_outputs_nonneg (D b1 b2 b3 fee old_dust : ℕ) :
    let (o1, o2, o3, dust) := feeSplit D b1 b2 b3 fee old_dust
    0 ≤ o1 ∧ 0 ≤ o2 ∧ 0 ≤ o3 ∧ 0 ≤ dust := by
  simp only [feeSplit]
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

-- ============================================================================
-- NON-VACUITY WITNESSES
-- ============================================================================

/-- Witness: Standard fee split with clean division (dust=0). -/
theorem witness_clean_split :
    feeSplit 10000 3000 3000 4000 1000 0 = (300, 300, 400, 0) := by native_decide

/-- Witness: Fee split producing maximum dust (dust=2). -/
theorem witness_max_dust :
    feeSplit 10000 3333 3333 3334 3 0 = (0, 0, 1, 2) := by native_decide

/-- Witness: Conservation with nonzero dust carry. -/
theorem witness_conservation_with_carry :
    let r := feeSplit 10000 5000 3000 2000 7 0
    r.1 + r.2.1 + r.2.2.1 + r.2.2.2 = 7 := by native_decide

/-- Witness: Dust carry forward enables output from tiny fees. -/
theorem witness_dust_carry_enables_output :
    feeSplit 10000 5000 3000 2000 1 1 = (1, 0, 0, 1) := by native_decide

/-- Witness: Multi-step dust carry conservation over 3 splits. -/
theorem witness_multi_step_conservation :
    let step := fun (acc : ℕ × ℕ) (fee : ℕ) =>
      let (o1, o2, o3, d) := feeSplit 10000 5000 3000 2000 fee acc.2
      (acc.1 + o1 + o2 + o3, d)
    let result := [100, 200, 50, 300, 75].foldl step (0, 0)
    result.1 + result.2 = 100 + 200 + 50 + 300 + 75 := by native_decide

/-- Witness: Dust bounded by 2 even with large dust carry-in. -/
theorem witness_dust_bounded_with_carry :
    let r := feeSplit 10000 3333 3333 3334 0 2
    r.2.2.2 ≤ 2 := by native_decide

end FeeDustCarry
