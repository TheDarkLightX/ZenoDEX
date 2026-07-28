import Std

namespace FCISFeeApportionmentSRGD

/-- One coordinate of the signed-deficit update. -/
def updateDeficit (D deficit fraction bonus : Int) : Int :=
  deficit + fraction - D * bonus

/-- A residual-seat indicator is an exact bit. -/
def IsBonusBit (bonus : Int) : Prop :=
  bonus = 0 ∨ bonus = 1

/--
The exact support-respecting, fixed-tie-order SRGD bonus relation.
Role order is buyback, treasury, rewards.
-/
def SRGDBonusRel
    (D d0 d1 d2 f0 f1 f2 b0 b1 b2 : Int) : Prop :=
  IsBonusBit b0 ∧
    IsBonusBit b1 ∧
    IsBonusBit b2 ∧
    f0 + f1 + f2 = D * (b0 + b1 + b2) ∧
    (b0 = 1 → 0 < f0) ∧
    (b1 = 1 → 0 < f1) ∧
    (b2 = 1 → 0 < f2) ∧
    (b0 = 1 → b1 = 0 → 0 < f1 → d1 + f1 ≤ d0 + f0) ∧
    (b0 = 1 → b2 = 0 → 0 < f2 → d2 + f2 ≤ d0 + f0) ∧
    (b1 = 1 → b0 = 0 → 0 < f0 → d0 + f0 < d1 + f1) ∧
    (b1 = 1 → b2 = 0 → 0 < f2 → d2 + f2 ≤ d1 + f1) ∧
    (b2 = 1 → b0 = 0 → 0 < f0 → d0 + f0 < d2 + f2) ∧
    (b2 = 1 → b1 = 0 → 0 < f1 → d1 + f1 < d2 + f2)

private theorem bit_triple_swap
    (b0 b1 b2 c0 c1 c2 : Int)
    (hb0 : IsBonusBit b0) (hb1 : IsBonusBit b1) (hb2 : IsBonusBit b2)
    (hc0 : IsBonusBit c0) (hc1 : IsBonusBit c1) (hc2 : IsBonusBit c2)
    (hSum : b0 + b1 + b2 = c0 + c1 + c2)
    (hDifferent : ¬(c0 = b0 ∧ c1 = b1 ∧ c2 = b2)) :
    (b0 = 1 ∧ c0 = 0 ∧ b1 = 0 ∧ c1 = 1) ∨
    (b0 = 1 ∧ c0 = 0 ∧ b2 = 0 ∧ c2 = 1) ∨
    (b1 = 1 ∧ c1 = 0 ∧ b0 = 0 ∧ c0 = 1) ∨
    (b1 = 1 ∧ c1 = 0 ∧ b2 = 0 ∧ c2 = 1) ∨
    (b2 = 1 ∧ c2 = 0 ∧ b0 = 0 ∧ c0 = 1) ∨
    (b2 = 1 ∧ c2 = 0 ∧ b1 = 0 ∧ c1 = 1) := by
  rcases hb0 with rfl | rfl <;>
    rcases hb1 with rfl | rfl <;>
    rcases hb2 with rfl | rfl <;>
    rcases hc0 with rfl | rfl <;>
    rcases hc1 with rfl | rfl <;>
    rcases hc2 with rfl | rfl <;>
    simp_all

/-- Two bonus tuples satisfying the exact SRGD relation are equal. -/
theorem srgd_bonus_rel_unique
    (D d0 d1 d2 f0 f1 f2 b0 b1 b2 c0 c1 c2 : Int)
    (hD : 0 < D)
    (hb : SRGDBonusRel D d0 d1 d2 f0 f1 f2 b0 b1 b2)
    (hc : SRGDBonusRel D d0 d1 d2 f0 f1 f2 c0 c1 c2) :
    c0 = b0 ∧ c1 = b1 ∧ c2 = b2 := by
  rcases hb with ⟨hb0, hb1, hb2, hbCount, hbS0, hbS1, hbS2,
    hb01, hb02, hb10, hb12, hb20, hb21⟩
  rcases hc with ⟨hc0, hc1, hc2, hcCount, hcS0, hcS1, hcS2,
    hc01, hc02, hc10, hc12, hc20, hc21⟩
  have hDne : D ≠ 0 := by omega
  have hMul :
      D * (b0 + b1 + b2) = D * (c0 + c1 + c2) := by
    calc
      D * (b0 + b1 + b2) = f0 + f1 + f2 := hbCount.symm
      _ = D * (c0 + c1 + c2) := hcCount
  have hSum : b0 + b1 + b2 = c0 + c1 + c2 :=
    Int.eq_of_mul_eq_mul_left hDne hMul
  apply Classical.byContradiction
  intro hDifferent
  have hSwap :
      (b0 = 1 ∧ c0 = 0 ∧ b1 = 0 ∧ c1 = 1) ∨
      (b0 = 1 ∧ c0 = 0 ∧ b2 = 0 ∧ c2 = 1) ∨
      (b1 = 1 ∧ c1 = 0 ∧ b0 = 0 ∧ c0 = 1) ∨
      (b1 = 1 ∧ c1 = 0 ∧ b2 = 0 ∧ c2 = 1) ∨
      (b2 = 1 ∧ c2 = 0 ∧ b0 = 0 ∧ c0 = 1) ∨
      (b2 = 1 ∧ c2 = 0 ∧ b1 = 0 ∧ c1 = 1) := by
    exact bit_triple_swap b0 b1 b2 c0 c1 c2
      hb0 hb1 hb2 hc0 hc1 hc2 hSum hDifferent
  rcases hSwap with hSwap | hSwap | hSwap | hSwap | hSwap | hSwap
  · rcases hSwap with ⟨hb0Eq, hc0Eq, hb1Eq, hc1Eq⟩
    have hf0 : 0 < f0 := hbS0 hb0Eq
    have hf1 : 0 < f1 := hcS1 hc1Eq
    have hLe := hb01 hb0Eq hb1Eq hf1
    have hLt := hc10 hc1Eq hc0Eq hf0
    omega
  · rcases hSwap with ⟨hb0Eq, hc0Eq, hb2Eq, hc2Eq⟩
    have hf0 : 0 < f0 := hbS0 hb0Eq
    have hf2 : 0 < f2 := hcS2 hc2Eq
    have hLe := hb02 hb0Eq hb2Eq hf2
    have hLt := hc20 hc2Eq hc0Eq hf0
    omega
  · rcases hSwap with ⟨hb1Eq, hc1Eq, hb0Eq, hc0Eq⟩
    have hf1 : 0 < f1 := hbS1 hb1Eq
    have hf0 : 0 < f0 := hcS0 hc0Eq
    have hLt := hb10 hb1Eq hb0Eq hf0
    have hLe := hc01 hc0Eq hc1Eq hf1
    omega
  · rcases hSwap with ⟨hb1Eq, hc1Eq, hb2Eq, hc2Eq⟩
    have hf1 : 0 < f1 := hbS1 hb1Eq
    have hf2 : 0 < f2 := hcS2 hc2Eq
    have hLe := hb12 hb1Eq hb2Eq hf2
    have hLt := hc21 hc2Eq hc1Eq hf1
    omega
  · rcases hSwap with ⟨hb2Eq, hc2Eq, hb0Eq, hc0Eq⟩
    have hf2 : 0 < f2 := hbS2 hb2Eq
    have hf0 : 0 < f0 := hcS0 hc0Eq
    have hLt := hb20 hb2Eq hb0Eq hf0
    have hLe := hc02 hc0Eq hc2Eq hf2
    omega
  · rcases hSwap with ⟨hb2Eq, hc2Eq, hb1Eq, hc1Eq⟩
    have hf2 : 0 < f2 := hbS2 hb2Eq
    have hf1 : 0 < f1 := hcS1 hc1Eq
    have hLt := hb21 hb2Eq hb1Eq hf1
    have hLe := hc12 hc1Eq hc2Eq hf2
    omega

/--
For every valid three-role residual quota, exactly one support-respecting
fixed-order SRGD bonus tuple exists. Deficit bounds and zero-sum are unnecessary
for selector totality.
-/
theorem srgd_bonus_exists_unique
    (D d0 d1 d2 f0 f1 f2 : Int)
    (hD : 0 < D)
    (hf0 : 0 ≤ f0 ∧ f0 < D)
    (hf1 : 0 ≤ f1 ∧ f1 < D)
    (hf2 : 0 ≤ f2 ∧ f2 < D)
    (hResidual :
      f0 + f1 + f2 = 0 ∨
      f0 + f1 + f2 = D ∨
      f0 + f1 + f2 = 2 * D) :
    ∃ b0 b1 b2 : Int,
      SRGDBonusRel D d0 d1 d2 f0 f1 f2 b0 b1 b2 ∧
      ∀ c0 c1 c2 : Int,
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 c0 c1 c2 →
        c0 = b0 ∧ c1 = b1 ∧ c2 = b2 := by
  rcases hf0 with ⟨hf0Lo, hf0Hi⟩
  rcases hf1 with ⟨hf1Lo, hf1Hi⟩
  rcases hf2 with ⟨hf2Lo, hf2Hi⟩
  rcases hResidual with hZero | hOne | hTwo
  · refine ⟨0, 0, 0, ?_, ?_⟩
    · simp [SRGDBonusRel, IsBonusBit]
      omega
    · intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 0 0 0 c0 c1 c2 hD
        (by
          simp [SRGDBonusRel, IsBonusBit]
          omega)
        hc
  · have hChoice :
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 1 0 0 ∨
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 0 1 0 ∨
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 0 0 1 := by
      simp [SRGDBonusRel, IsBonusBit]
      omega
    rcases hChoice with hChoice | hChoice | hChoice
    · refine ⟨1, 0, 0, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 1 0 0 c0 c1 c2 hD hChoice hc
    · refine ⟨0, 1, 0, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 0 1 0 c0 c1 c2 hD hChoice hc
    · refine ⟨0, 0, 1, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 0 0 1 c0 c1 c2 hD hChoice hc
  · have hChoice :
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 1 1 0 ∨
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 1 0 1 ∨
        SRGDBonusRel D d0 d1 d2 f0 f1 f2 0 1 1 := by
      simp [SRGDBonusRel, IsBonusBit]
      omega
    rcases hChoice with hChoice | hChoice | hChoice
    · refine ⟨1, 1, 0, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 1 1 0 c0 c1 c2 hD hChoice hc
    · refine ⟨1, 0, 1, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 1 0 1 c0 c1 c2 hD hChoice hc
    · refine ⟨0, 1, 1, hChoice, ?_⟩
      intro c0 c1 c2 hc
      exact srgd_bonus_rel_unique D d0 d1 d2 f0 f1 f2 0 1 1 c0 c1 c2 hD hChoice hc

/--
The relational SRGD bonus rule preserves zero-sum signed deficit and keeps
every scaled-deficit coordinate strictly inside `(-D, D)` for three roles.
The cumulative-discrepancy interpretation additionally requires the
history-derived deficit identity specified by the SRGD-v1 amendment.
Equal-score precedence is buyback, treasury, rewards.
-/
theorem step_preserves_strict_deficit
    (D d0 d1 d2 f0 f1 f2 b0 b1 b2 : Int)
    (hD : 0 < D)
    (hdSum : d0 + d1 + d2 = 0)
    (hd0Lo : -D < d0) (hd0Hi : d0 < D)
    (hd1Lo : -D < d1) (hd1Hi : d1 < D)
    (hd2Lo : -D < d2) (hd2Hi : d2 < D)
    (hf0Lo : 0 ≤ f0) (hf0Hi : f0 < D)
    (hf1Lo : 0 ≤ f1) (hf1Hi : f1 < D)
    (hf2Lo : 0 ≤ f2) (hf2Hi : f2 < D)
    (hBonus : SRGDBonusRel D d0 d1 d2 f0 f1 f2 b0 b1 b2) :
    let d0' := d0 + f0 - D * b0
    let d1' := d1 + f1 - D * b1
    let d2' := d2 + f2 - D * b2
    d0' + d1' + d2' = 0 ∧
      -D < d0' ∧ d0' < D ∧
      -D < d1' ∧ d1' < D ∧
      -D < d2' ∧ d2' < D := by
  dsimp
  rcases hBonus with ⟨hb0, hb1, hb2, hCount, hSupport0, hSupport1, hSupport2,
    h01, h02, h10, h12, h20, h21⟩
  rcases hb0 with hb0 | hb0 <;>
    rcases hb1 with hb1 | hb1 <;>
    rcases hb2 with hb2 | hb2 <;>
    subst b0 <;> subst b1 <;> subst b2 <;>
    simp_all <;>
    omega

/-- The zero deficit state satisfies the strict invariant for every positive denominator. -/
theorem zero_state_valid (D : Int) (hD : 0 < D) :
    (0 : Int) + 0 + 0 = 0 ∧
      -D < 0 ∧ 0 < D ∧
      -D < 0 ∧ 0 < D ∧
      -D < 0 ∧ 0 < D := by
  omega

/--
The score `deficit + current fraction` chooses rewards in the minimized
two-step witness and keeps every coordinate strictly inside `(-D, D)`.
-/
theorem witness_score_includes_current_fraction :
    (updateDeficit 3 (-2) 0 0,
      updateDeficit 3 1 1 0,
      updateDeficit 3 1 2 1) = (-2, 2, 0) := by
  decide

/--
Selecting from stored deficit alone chooses treasury in the same witness and
reaches the forbidden boundary. This is the mutation SRGD-v1 must reject.
-/
theorem witness_deficit_only_reaches_boundary :
    (updateDeficit 3 (-2) 0 0,
      updateDeficit 3 1 1 1,
      updateDeficit 3 1 2 0) = (-2, -1, 3) := by
  decide

/-- A concrete non-vacuity witness satisfies every premise of the relational theorem. -/
theorem witness_valid_score_transition :
    let d0' := (-2 : Int) + 0 - 3 * 0
    let d1' := (1 : Int) + 1 - 3 * 0
    let d2' := (1 : Int) + 2 - 3 * 1
    d0' + d1' + d2' = 0 ∧
      -3 < d0' ∧ d0' < 3 ∧
      -3 < d1' ∧ d1' < 3 ∧
      -3 < d2' ∧ d2' < 3 := by
  apply step_preserves_strict_deficit
  all_goals try decide
  simp [SRGDBonusRel, IsBonusBit]

end FCISFeeApportionmentSRGD
