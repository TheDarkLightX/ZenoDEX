import Std.Tactic

/-!
Arithmetic lift for custody-complete wrapper scalars. Connecting these natural
numbers to the exact runtime projection sums, unchanged custody rows and the
existing leaf's conservation theorem is an explicit representation premise.
This file proves no hashing, authorization, receipt or publication statement.
-/
namespace Proofs.AssetTransferCustodyCompletionV1

def maxAtoms : Nat := 2 ^ 128 - 1

def complete (before after custodyBefore custodyAfter : Nat) : Nat × Nat :=
  (before + custodyBefore, after + custodyAfter)

def completeChecked (before after custodyBefore custodyAfter : Nat) : Option (Nat × Nat) :=
  let totals := complete before after custodyBefore custodyAfter
  if totals.1 ≤ maxAtoms ∧ totals.2 ≤ maxAtoms then some totals else none

theorem completed_totals_preserve_supply
    {before after custodyBefore custodyAfter supply : Nat}
    (accountConserved : after = before) (custodyFrame : custodyAfter = custodyBefore)
    (preProjection : before + custodyBefore = supply) (bounded : supply ≤ maxAtoms) :
    complete before after custodyBefore custodyAfter = (supply, supply) ∧
    (complete before after custodyBefore custodyAfter).1 ≤ maxAtoms ∧
    (complete before after custodyBefore custodyAfter).2 ≤ maxAtoms := by
  simp [complete, accountConserved, custodyFrame, preProjection, bounded]

theorem checked_completion_accepts_valid_projection
    {before after custodyBefore custodyAfter supply : Nat}
    (accountConserved : after = before) (custodyFrame : custodyAfter = custodyBefore)
    (preProjection : before + custodyBefore = supply) (bounded : supply ≤ maxAtoms) :
    completeChecked before after custodyBefore custodyAfter = some (supply, supply) := by
  have h := completed_totals_preserve_supply accountConserved custodyFrame preProjection bounded
  simp only [completeChecked, h.1, bounded, and_self, ↓reduceIte]

theorem checked_success_is_u128 {b a c d : Nat} {totals : Nat × Nat}
    (accepted : completeChecked b a c d = some totals) :
    totals.1 ≤ maxAtoms ∧ totals.2 ≤ maxAtoms := by
  dsimp only [completeChecked] at accepted
  split at accepted
  · rename_i guard
    cases accepted
    exact guard
  · contradiction

theorem maximum_total_accepts :
    completeChecked 115 115 (maxAtoms - 115) (maxAtoms - 115) = some (maxAtoms, maxAtoms) := by decide

theorem overflow_neighbor_rejects :
    completeChecked 115 115 (maxAtoms - 114) (maxAtoms - 114) = none := by decide

theorem custody_frame_is_necessary : complete 115 115 1 2 = (116, 117) := by decide

end Proofs.AssetTransferCustodyCompletionV1
