import Mathlib

/-!
# UPBA V2 Score Order

This file promotes the Aristotle-checked order facts for canonical UPBA v2
fill-vector scoring. It proves only the local score-order contract: higher
volume wins, then higher surplus, then lower deterministic tie-break key.

It does not prove candidate-set completeness, grid sufficiency, omitted
candidate rejection, or global UPBA optimality.
-/

namespace Proofs
namespace UPBAV2ScoreOrder

/--
Certificate-facing score for a candidate fill vector.

Higher volume is better. For equal volume, higher surplus is better. For equal
volume and surplus, the lower deterministic tie-break key is better.
-/
structure FillScore where
  volume : Nat
  surplus : Nat
  tieBreak : Nat
deriving DecidableEq, Repr

/-- Weak lexicographic no-worse relation for certificate comparison. -/
def WeakNoWorse (winner other : FillScore) : Prop :=
  other.volume <= winner.volume ∧
    (other.volume = winner.volume -> other.surplus <= winner.surplus) ∧
    (other.volume = winner.volume -> other.surplus = winner.surplus ->
      winner.tieBreak <= other.tieBreak)

/-- Strict lexicographic improvement for candidate selection. -/
def StrictBetter (candidate incumbent : FillScore) : Prop :=
  incumbent.volume < candidate.volume ∨
    (incumbent.volume = candidate.volume ∧ incumbent.surplus < candidate.surplus) ∨
    (incumbent.volume = candidate.volume ∧ incumbent.surplus = candidate.surplus ∧
      candidate.tieBreak < incumbent.tieBreak)

theorem weakNoWorse_refl (score : FillScore) :
    WeakNoWorse score score := by
  exact ⟨Nat.le.refl, (fun _ => Nat.le.refl), (fun _ _ => Nat.le.refl)⟩

theorem weakNoWorse_trans {a b c : FillScore}
    (hab : WeakNoWorse a b)
    (hbc : WeakNoWorse b c) :
    WeakNoWorse a c := by
  obtain ⟨hv1, hs1, ht1⟩ := hab
  obtain ⟨hv2, hs2, ht2⟩ := hbc
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.le_trans hv2 hv1
  · intro hvc
    have hcb : c.volume = b.volume := by omega
    have hba : b.volume = a.volume := by omega
    exact Nat.le_trans (hs2 hcb) (hs1 hba)
  · intro hvc hsc
    have hcb : c.volume = b.volume := by omega
    have hba : b.volume = a.volume := by omega
    have hcsb : c.surplus = b.surplus := by
      have := hs2 hcb
      have := hs1 hba
      omega
    have hbsa : b.surplus = a.surplus := by
      have := hs2 hcb
      have := hs1 hba
      omega
    exact Nat.le_trans (ht1 hba hbsa) (ht2 hcb hcsb)

theorem weakNoWorse_antisymm {a b : FillScore}
    (hab : WeakNoWorse a b)
    (hba : WeakNoWorse b a) :
    a = b := by
  obtain ⟨hv1, hs1, ht1⟩ := hab
  obtain ⟨hv2, hs2, ht2⟩ := hba
  have hv : a.volume = b.volume := by omega
  have hvba : b.volume = a.volume := hv.symm
  have hs : a.surplus = b.surplus := by
    have := hs1 hvba
    have := hs2 hv
    omega
  have ht : a.tieBreak = b.tieBreak := by
    have := ht1 hvba hs.symm
    have := ht2 hv hs
    omega
  cases a
  cases b
  simp_all

theorem strictBetter_irrefl (score : FillScore) :
    ¬ StrictBetter score score := by
  intro h
  unfold StrictBetter at h
  rcases h with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega

theorem strictBetter_asymm {a b : FillScore}
    (hab : StrictBetter a b) :
    ¬ StrictBetter b a := by
  intro hba
  unfold StrictBetter at hab hba
  rcases hab with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
    rcases hba with h4 | ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega

theorem strictBetter_implies_weakNoWorse {a b : FillScore}
    (hab : StrictBetter a b) :
    WeakNoWorse a b := by
  unfold StrictBetter at hab
  unfold WeakNoWorse
  rcases hab with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact ⟨by omega, (fun h' => by omega), (fun h' _ => by omega)⟩
  · exact ⟨by omega, (fun _ => by omega), (fun _ h' => by omega)⟩
  · exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩

/--
If a candidate strictly improves on an incumbent, and the incumbent is already
weakly no worse than a third candidate, then the candidate is weakly no worse
than that third candidate. This is the local update invariant a streaming
canonical scorer needs.
-/
theorem strict_update_preserves_dominance {candidate incumbent other : FillScore}
    (hStrict : StrictBetter candidate incumbent)
    (hIncumbent : WeakNoWorse incumbent other) :
    WeakNoWorse candidate other :=
  weakNoWorse_trans (strictBetter_implies_weakNoWorse hStrict) hIncumbent

end UPBAV2ScoreOrder
end Proofs
