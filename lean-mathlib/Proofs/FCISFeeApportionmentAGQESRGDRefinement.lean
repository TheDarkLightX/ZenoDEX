import Proofs.FCISFeeApportionmentSRGD

namespace FCISFeeApportionmentAGQESRGDRefinement

open FCISFeeApportionmentSRGD

/-- One coordinate of the AGQE cumulative-surplus update. -/
def updateSurplus (D surplus remainder bonus : Int) : Int :=
  surplus - remainder + D * bonus

/--
The exact three-role AGQE bonus relation. Roles are ordered buyback, treasury,
rewards. Eligible roles minimize `surplus - remainder`; the role index resolves
equal scores.
-/
def AGQEBonusRel
    (D s0 s1 s2 r0 r1 r2 b0 b1 b2 : Int) : Prop :=
  IsBonusBit b0 ∧
    IsBonusBit b1 ∧
    IsBonusBit b2 ∧
    r0 + r1 + r2 = D * (b0 + b1 + b2) ∧
    (b0 = 1 → 0 < r0) ∧
    (b1 = 1 → 0 < r1) ∧
    (b2 = 1 → 0 < r2) ∧
    (b0 = 1 → b1 = 0 → 0 < r1 → s0 - r0 ≤ s1 - r1) ∧
    (b0 = 1 → b2 = 0 → 0 < r2 → s0 - r0 ≤ s2 - r2) ∧
    (b1 = 1 → b0 = 0 → 0 < r0 → s1 - r1 < s0 - r0) ∧
    (b1 = 1 → b2 = 0 → 0 < r2 → s1 - r1 ≤ s2 - r2) ∧
    (b2 = 1 → b0 = 0 → 0 < r0 → s2 - r2 < s0 - r0) ∧
    (b2 = 1 → b1 = 0 → 0 < r1 → s2 - r2 < s1 - r1)

/--
Negating SRGD deficit converts its descending score order into AGQE's
ascending surplus order, including the fixed role-index tie break.
-/
theorem bonus_relation_sign_dual
    (D d0 d1 d2 r0 r1 r2 b0 b1 b2 : Int) :
    AGQEBonusRel D (-d0) (-d1) (-d2) r0 r1 r2 b0 b1 b2 ↔
      SRGDBonusRel D d0 d1 d2 r0 r1 r2 b0 b1 b2 := by
  constructor
  · intro h
    rcases h with ⟨hb0, hb1, hb2, hCount, hSupport0, hSupport1, hSupport2,
      h01, h02, h10, h12, h20, h21⟩
    refine ⟨hb0, hb1, hb2, hCount, hSupport0, hSupport1, hSupport2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hb0Eq hb1Eq hr1
      have h := h01 hb0Eq hb1Eq hr1
      omega
    · intro hb0Eq hb2Eq hr2
      have h := h02 hb0Eq hb2Eq hr2
      omega
    · intro hb1Eq hb0Eq hr0
      have h := h10 hb1Eq hb0Eq hr0
      omega
    · intro hb1Eq hb2Eq hr2
      have h := h12 hb1Eq hb2Eq hr2
      omega
    · intro hb2Eq hb0Eq hr0
      have h := h20 hb2Eq hb0Eq hr0
      omega
    · intro hb2Eq hb1Eq hr1
      have h := h21 hb2Eq hb1Eq hr1
      omega
  · intro h
    rcases h with ⟨hb0, hb1, hb2, hCount, hSupport0, hSupport1, hSupport2,
      h01, h02, h10, h12, h20, h21⟩
    refine ⟨hb0, hb1, hb2, hCount, hSupport0, hSupport1, hSupport2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hb0Eq hb1Eq hr1
      have h := h01 hb0Eq hb1Eq hr1
      omega
    · intro hb0Eq hb2Eq hr2
      have h := h02 hb0Eq hb2Eq hr2
      omega
    · intro hb1Eq hb0Eq hr0
      have h := h10 hb1Eq hb0Eq hr0
      omega
    · intro hb1Eq hb2Eq hr2
      have h := h12 hb1Eq hb2Eq hr2
      omega
    · intro hb2Eq hb0Eq hr0
      have h := h20 hb2Eq hb0Eq hr0
      omega
    · intro hb2Eq hb1Eq hr1
      have h := h21 hb2Eq hb1Eq hr1
      omega

/-- The coordinate updates are exact negatives under the sign-dual state map. -/
theorem update_sign_dual (D deficit remainder bonus : Int) :
    updateSurplus D (-deficit) remainder bonus =
      -updateDeficit D deficit remainder bonus := by
  simp [updateSurplus, updateDeficit]
  omega

/--
One exact SRGD bonus transition is the corresponding AGQE transition after
mapping every pre- and post-state coordinate by `surplus = -deficit`.
-/
theorem transition_sign_dual
    (D d0 d1 d2 r0 r1 r2 b0 b1 b2 : Int)
    (hBonus : SRGDBonusRel D d0 d1 d2 r0 r1 r2 b0 b1 b2) :
    AGQEBonusRel D (-d0) (-d1) (-d2) r0 r1 r2 b0 b1 b2 ∧
      updateSurplus D (-d0) r0 b0 = -updateDeficit D d0 r0 b0 ∧
      updateSurplus D (-d1) r1 b1 = -updateDeficit D d1 r1 b1 ∧
      updateSurplus D (-d2) r2 b2 = -updateDeficit D d2 r2 b2 := by
  exact ⟨
    (bonus_relation_sign_dual D d0 d1 d2 r0 r1 r2 b0 b1 b2).2 hBonus,
    update_sign_dual D d0 r0 b0,
    update_sign_dual D d1 r1 b1,
    update_sign_dual D d2 r2 b2
  ⟩

/-- Every valid three-role residual quota has one exact AGQE bonus tuple. -/
theorem agqe_bonus_exists_unique
    (D s0 s1 s2 r0 r1 r2 : Int)
    (hD : 0 < D)
    (hr0 : 0 ≤ r0 ∧ r0 < D)
    (hr1 : 0 ≤ r1 ∧ r1 < D)
    (hr2 : 0 ≤ r2 ∧ r2 < D)
    (hResidual :
      r0 + r1 + r2 = 0 ∨
      r0 + r1 + r2 = D ∨
      r0 + r1 + r2 = 2 * D) :
    ∃ b0 b1 b2 : Int,
      AGQEBonusRel D s0 s1 s2 r0 r1 r2 b0 b1 b2 ∧
      ∀ c0 c1 c2 : Int,
        AGQEBonusRel D s0 s1 s2 r0 r1 r2 c0 c1 c2 →
        c0 = b0 ∧ c1 = b1 ∧ c2 = b2 := by
  obtain ⟨b0, b1, b2, hBonus, hUnique⟩ :=
    srgd_bonus_exists_unique D (-s0) (-s1) (-s2) r0 r1 r2
      hD hr0 hr1 hr2 hResidual
  refine ⟨b0, b1, b2, ?_, ?_⟩
  · have hMapped :=
      (bonus_relation_sign_dual D (-s0) (-s1) (-s2) r0 r1 r2 b0 b1 b2).2 hBonus
    simpa using hMapped
  · intro c0 c1 c2 hCandidate
    apply hUnique c0 c1 c2
    have hMapped :
        AGQEBonusRel D (-(-s0)) (-(-s1)) (-(-s2)) r0 r1 r2 c0 c1 c2 := by
      simpa using hCandidate
    exact
      (bonus_relation_sign_dual D (-s0) (-s1) (-s2) r0 r1 r2 c0 c1 c2).1
        hMapped

/--
The AGQE relation preserves zero-sum surplus and every coordinate's strict
`(-D, D)` discrepancy bound for one transition.
-/
theorem agqe_step_preserves_strict_surplus
    (D s0 s1 s2 r0 r1 r2 b0 b1 b2 : Int)
    (hD : 0 < D)
    (hsSum : s0 + s1 + s2 = 0)
    (hs0Lo : -D < s0) (hs0Hi : s0 < D)
    (hs1Lo : -D < s1) (hs1Hi : s1 < D)
    (hs2Lo : -D < s2) (hs2Hi : s2 < D)
    (hr0Lo : 0 ≤ r0) (hr0Hi : r0 < D)
    (hr1Lo : 0 ≤ r1) (hr1Hi : r1 < D)
    (hr2Lo : 0 ≤ r2) (hr2Hi : r2 < D)
    (hBonus : AGQEBonusRel D s0 s1 s2 r0 r1 r2 b0 b1 b2) :
    let s0' := updateSurplus D s0 r0 b0
    let s1' := updateSurplus D s1 r1 b1
    let s2' := updateSurplus D s2 r2 b2
    s0' + s1' + s2' = 0 ∧
      -D < s0' ∧ s0' < D ∧
      -D < s1' ∧ s1' < D ∧
      -D < s2' ∧ s2' < D := by
  have hMapped :
      AGQEBonusRel D (-(-s0)) (-(-s1)) (-(-s2)) r0 r1 r2 b0 b1 b2 := by
    simpa using hBonus
  have hSRGD :=
    (bonus_relation_sign_dual D (-s0) (-s1) (-s2) r0 r1 r2 b0 b1 b2).1
      hMapped
  have hDeficit := step_preserves_strict_deficit
    D (-s0) (-s1) (-s2) r0 r1 r2 b0 b1 b2
    hD
    (by omega)
    (by omega) (by omega)
    (by omega) (by omega)
    (by omega) (by omega)
    hr0Lo hr0Hi hr1Lo hr1Hi hr2Lo hr2Hi hSRGD
  dsimp [updateSurplus] at hDeficit ⊢
  omega

/-- SRGD deficit and AGQE surplus are opposite views of one history identity. -/
theorem history_identity_sign_dual
    (D cumulativeActual idealNumerator : Int) :
    D * cumulativeActual - idealNumerator =
      -(idealNumerator - D * cumulativeActual) := by
  omega

/-- The zero-sum invariant is preserved by the sign-dual state map. -/
theorem zero_sum_sign_dual
    (d0 d1 d2 : Int)
    (hSum : d0 + d1 + d2 = 0) :
    (-d0) + (-d1) + (-d2) = 0 := by
  omega

/-- The strict discrepancy interval is preserved by the sign-dual state map. -/
theorem strict_bound_sign_dual
    (D deficit : Int)
    (hLower : -D < deficit)
    (hUpper : deficit < D) :
    -D < -deficit ∧ -deficit < D := by
  omega

/-- Concrete evidence that the refinement theorem has a non-vacuous bonus case. -/
theorem witness_sign_dual_transition :
    AGQEBonusRel 3 2 (-1) (-1) 0 1 2 0 0 1 ∧
      (updateSurplus 3 2 0 0,
        updateSurplus 3 (-1) 1 0,
        updateSurplus 3 (-1) 2 1) = (2, -2, 0) := by
  simp [AGQEBonusRel, IsBonusBit, updateSurplus]

end FCISFeeApportionmentAGQESRGDRefinement
