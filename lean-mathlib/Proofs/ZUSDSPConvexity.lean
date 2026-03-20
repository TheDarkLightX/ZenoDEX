import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Stability Pool Convexity Under Liquidation (H-MO-002)

Phase 3 (Mathematical Discovery) formalization of the stability pool's
convex combination property during liquidation.

## Key Property

When a vault with collateral ratio `vault_coll/vault_debt` is liquidated
into the stability pool (SP):
- SP absorbs the vault's debt and collateral
- The new SP ratio is a weighted average of the old SP ratio and the vault ratio

This means the SP ratio after liquidation lies between the old SP ratio and
the liquidated vault's ratio -- the classic convex combination property.

## What This File Proves

1. **weighted_avg_lower_bound**: Weighted average >= m when both values >= m
2. **weighted_avg_upper_bound**: Weighted average <= M when both values <= M
3. **sp_ratio_convex_lower**: After liquidation, SP ratio >= min bound m
4. **sp_ratio_convex_upper**: After liquidation, SP ratio <= max bound M
5. **overcollateralized_liq_improves_sp**: If vault ratio > SP ratio, SP improves
6. **undercollateralized_liq_bounded_below**: SP ratio stays above vault ratio
7. **multi_liquidation_lower_bound**: SP ratio stays above m across sequence
8. Non-vacuity witnesses for all key properties

## Mathematical Structure

For SP with (sp_coll, sp_debt) and liquidated vault (v_coll, v_debt):
  sp_coll' = sp_coll + v_coll
  sp_debt' = sp_debt + v_debt
  r_new = sp_coll' / sp_debt' = (sp_coll + v_coll) / (sp_debt + v_debt)

This is a weighted average of sp_coll/sp_debt and v_coll/v_debt
with weights sp_debt and v_debt respectively.
-/

namespace Proofs

namespace ZUSDSPConvexity

/-! ## Part 1: Weighted Average Bounds

The core mathematical fact: a weighted average of two values lies
between the minimum and maximum of those values.

We work over ℚ for clean division semantics.
-/

/-- Weighted average of two rational values with positive weights.
    wa = (w₁ * v₁ + w₂ * v₂) / (w₁ + w₂) -/
noncomputable def weightedAvg (v₁ v₂ w₁ w₂ : ℚ) : ℚ :=
  (w₁ * v₁ + w₂ * v₂) / (w₁ + w₂)

/-- Weighted average lower bound: wa >= m when both values >= m and weights positive. -/
theorem weighted_avg_lower_bound (v₁ v₂ w₁ w₂ m : ℚ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hv₁ : m ≤ v₁) (hv₂ : m ≤ v₂) :
    m ≤ weightedAvg v₁ v₂ w₁ w₂ := by
  unfold weightedAvg
  rw [le_div_iff₀ (by linarith : (0 : ℚ) < w₁ + w₂)]
  nlinarith [mul_le_mul_of_nonneg_left hv₁ (le_of_lt hw₁),
             mul_le_mul_of_nonneg_left hv₂ (le_of_lt hw₂)]

/-- Weighted average upper bound: wa <= M when both values <= M and weights positive. -/
theorem weighted_avg_upper_bound (v₁ v₂ w₁ w₂ M : ℚ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hv₁ : v₁ ≤ M) (hv₂ : v₂ ≤ M) :
    weightedAvg v₁ v₂ w₁ w₂ ≤ M := by
  unfold weightedAvg
  rw [div_le_iff₀ (by linarith : (0 : ℚ) < w₁ + w₂)]
  nlinarith [mul_le_mul_of_nonneg_left hv₁ (le_of_lt hw₁),
             mul_le_mul_of_nonneg_left hv₂ (le_of_lt hw₂)]

/-! ## Part 2: SP Ratio After Liquidation

Model: SP has (sp_coll, sp_debt) and absorbs a vault with (v_coll, v_debt).
The new SP ratio is:
  sp_ratio' = (sp_coll + v_coll) / (sp_debt + v_debt)

We prove this is bounded by min and max of the component ratios.
-/

/-- SP ratio after absorbing a liquidated vault's collateral and debt. -/
noncomputable def sp_ratio_after (sp_coll sp_debt v_coll v_debt : ℚ) : ℚ :=
  (sp_coll + v_coll) / (sp_debt + v_debt)

/-- SP ratio after liquidation is at least m, given both component ratios >= m.
    This is the key convex combination lower bound. -/
theorem sp_ratio_convex_lower
    (sp_coll sp_debt v_coll v_debt m : ℚ)
    (hsp : 0 < sp_debt) (hv : 0 < v_debt)
    (hm_sp : m * sp_debt ≤ sp_coll)
    (hm_v : m * v_debt ≤ v_coll) :
    m ≤ sp_ratio_after sp_coll sp_debt v_coll v_debt := by
  unfold sp_ratio_after
  rw [le_div_iff₀ (by linarith : (0 : ℚ) < sp_debt + v_debt)]
  nlinarith

/-- SP ratio after liquidation is at most M, given both component ratios <= M.
    This is the convex combination upper bound. -/
theorem sp_ratio_convex_upper
    (sp_coll sp_debt v_coll v_debt M : ℚ)
    (hsp : 0 < sp_debt) (hv : 0 < v_debt)
    (hM_sp : sp_coll ≤ M * sp_debt)
    (hM_v : v_coll ≤ M * v_debt) :
    sp_ratio_after sp_coll sp_debt v_coll v_debt ≤ M := by
  unfold sp_ratio_after
  rw [div_le_iff₀ (by linarith : (0 : ℚ) < sp_debt + v_debt)]
  nlinarith

/-- Overcollateralized liquidation improves SP: if the vault being
    liquidated has a higher ratio than the SP, the SP ratio improves.
    Specifically: if v_coll/v_debt >= sp_coll/sp_debt (cross-multiplied),
    then sp_ratio_after >= sp_coll/sp_debt. -/
theorem overcollateralized_liq_improves_sp
    (sp_coll sp_debt v_coll v_debt : ℚ)
    (hsp : 0 < sp_debt) (hv : 0 < v_debt)
    (h_over : sp_coll * v_debt ≤ v_coll * sp_debt) :
    sp_coll / sp_debt ≤ sp_ratio_after sp_coll sp_debt v_coll v_debt := by
  unfold sp_ratio_after
  have hsum : (0 : ℚ) < sp_debt + v_debt := by linarith
  rw [div_le_div_iff₀ hsp hsum]
  nlinarith

/-- Undercollateralized liquidation degrades SP: if the vault has a
    lower ratio, the SP ratio decreases but stays above the vault ratio. -/
theorem undercollateralized_liq_bounded_below
    (sp_coll sp_debt v_coll v_debt : ℚ)
    (hsp : 0 < sp_debt) (hv : 0 < v_debt)
    (h_under : v_coll * sp_debt ≤ sp_coll * v_debt) :
    v_coll / v_debt ≤ sp_ratio_after sp_coll sp_debt v_coll v_debt := by
  unfold sp_ratio_after
  have hsum : (0 : ℚ) < sp_debt + v_debt := by linarith
  rw [div_le_div_iff₀ hv hsum]
  nlinarith

/-! ## Part 3: Multi-Liquidation Lower Bound

Across a sequence of liquidations, the SP ratio stays above the
minimum vault ratio in the sequence (induction on the list).

Model: each liquidation contributes (v_coll, v_debt). We track
cumulative SP state using sum-based accounting (no division).
-/

/-- Multi-liquidation: if the SP ratio starts at or above m, and
    every liquidated vault has ratio at or above m, then the SP
    ratio after all liquidations is at or above m.

    Uses cumulative collateral/debt accounting to avoid division. -/
theorem multi_liquidation_lower_bound
    (sp_coll₀ sp_debt₀ : ℚ)
    (vaults : List (ℚ × ℚ))
    (m : ℚ)
    (_hsp₀ : 0 < sp_debt₀)
    (hm₀ : m * sp_debt₀ ≤ sp_coll₀)
    (hv_pos : ∀ v ∈ vaults, 0 < v.2)
    (hv_ratio : ∀ v ∈ vaults, m * v.2 ≤ v.1) :
    let total_debt := sp_debt₀ + (vaults.map Prod.snd).sum
    let total_coll := sp_coll₀ + (vaults.map Prod.fst).sum
    m * total_debt ≤ total_coll := by
  simp only
  induction vaults with
  | nil => simp; linarith
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd_pos := hv_pos hd (List.mem_cons_self ..)
    have hhd_ratio := hv_ratio hd (List.mem_cons_self ..)
    have htl_pos : ∀ v ∈ tl, 0 < v.2 := fun v hv =>
      hv_pos v (List.mem_cons_of_mem hd hv)
    have htl_ratio : ∀ v ∈ tl, m * v.2 ≤ v.1 := fun v hv =>
      hv_ratio v (List.mem_cons_of_mem hd hv)
    have ih_result := ih htl_pos htl_ratio
    nlinarith

/-! ## Part 4: Non-Vacuity Witnesses -/

/-- Witness: weighted average bounds with concrete values.
    v₁=3/2, v₂=2, w₁=100, w₂=50. wa = (150+100)/150 = 250/150 = 5/3.
    min=3/2, max=2. Check: 3/2 <= 5/3 <= 2. -/
theorem witness_weighted_avg_bounds :
    let v₁ : ℚ := 3/2
    let v₂ : ℚ := 2
    let w₁ : ℚ := 100
    let w₂ : ℚ := 50
    let wa := (w₁ * v₁ + w₂ * v₂) / (w₁ + w₂)
    3/2 ≤ wa ∧ wa ≤ 2 := by
  norm_num

/-- Witness: SP ratio improves after absorbing an overcollateralized vault.
    SP: (1000, 1000) ratio=1. Vault: (300, 200) ratio=3/2.
    After: (1300, 1200) ratio=13/12 > 1. -/
theorem witness_overcollateralized_liq :
    let sp_c : ℚ := 1000
    let sp_d : ℚ := 1000
    let v_c : ℚ := 300
    let v_d : ℚ := 200
    sp_c / sp_d = 1 ∧
    v_c / v_d = 3/2 ∧
    (sp_c + v_c) / (sp_d + v_d) = 13/12 ∧
    1 ≤ (sp_c + v_c) / (sp_d + v_d) := by
  norm_num

/-- Witness: SP ratio degrades but stays bounded after undercollateralized vault.
    SP: (2000, 1000) ratio=2. Vault: (100, 200) ratio=1/2.
    After: (2100, 1200) ratio=7/4=1.75. Still above 1/2. -/
theorem witness_undercollateralized_liq :
    let sp_c : ℚ := 2000
    let sp_d : ℚ := 1000
    let v_c : ℚ := 100
    let v_d : ℚ := 200
    sp_c / sp_d = 2 ∧
    v_c / v_d = 1/2 ∧
    (sp_c + v_c) / (sp_d + v_d) = 7/4 ∧
    1/2 ≤ (sp_c + v_c) / (sp_d + v_d) ∧
    (sp_c + v_c) / (sp_d + v_d) ≤ 2 := by
  norm_num

/-- Witness: multi-liquidation lower bound with 3 vaults.
    SP₀: (1000, 1000). Vaults: [(150,100), (300,200), (120,100)].
    All have ratio >= 1. After: (1570, 1400) = 157/140 >= 1. -/
theorem witness_multi_liquidation :
    let sp_c : ℚ := 1000
    let sp_d : ℚ := 1000
    let v₁ : ℚ × ℚ := ⟨150, 100⟩
    let v₂ : ℚ × ℚ := ⟨300, 200⟩
    let v₃ : ℚ × ℚ := ⟨120, 100⟩
    let total_c := sp_c + v₁.1 + v₂.1 + v₃.1
    let total_d := sp_d + v₁.2 + v₂.2 + v₃.2
    total_c = 1570 ∧
    total_d = 1400 ∧
    1 * total_d ≤ total_c := by
  norm_num

/-- Witness: convex combination property with exact values.
    Demonstrates that the result lies strictly between the two ratios
    (not at either extreme) when both weights are positive. -/
theorem witness_strict_interior :
    let sp_c : ℚ := 500
    let sp_d : ℚ := 1000
    let v_c : ℚ := 400
    let v_d : ℚ := 200
    let after := (sp_c + v_c) / (sp_d + v_d)
    after = 3/4 ∧
    1/2 < after ∧ after < 2 := by
  norm_num

end ZUSDSPConvexity

end Proofs
