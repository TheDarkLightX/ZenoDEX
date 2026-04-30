import Proofs.ZenoDEXExactOutCanonicalMinimizer

open scoped Classical

/-!
# ZenoDEX Exact-Out Many-Pool Key-Cover Bridge

This file reformulates the many-pool exact-out contraction bridge at the
canonical-key level.

Instead of lifting selected-domain minimality through allocation semantics, it
works directly over finite key sets:

- `selectedKeys`: keys accepted by a repaired selected-domain surface
- `fullKeys`: keys accepted by the bounded full-domain audit surface

If every full-domain key is dominated by some selected-domain key, then any
selected-domain minimum already lifts to a full-domain minimum.

This is closer to the current runtime audit shape than the existing
allocation-level contraction bridge.
-/

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolKeyCoverBridge

open ExactOutCanonicalMinimizer

/-- The selected key set safely covers the full bounded key set when every full
key is dominated by some selected key. -/
def KeyCover {PoolId : Type} [LinearOrder PoolId]
    (selectedKeys fullKeys : Finset (Key PoolId)) : Prop :=
  ∀ k, k ∈ fullKeys → ∃ ks, ks ∈ selectedKeys ∧ ks ≤ k

/-- A minimum key over the selected-domain key set also minimizes the full
bounded key set when the selected key set is included in the full set and
key-cover holds. -/
theorem keyCover_implies_selected_min_lifts_to_full
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    {kStar : Key PoolId}
    (hStarSel : kStar ∈ selectedKeys)
    (hMinSel : ∀ k, k ∈ selectedKeys → kStar ≤ k)
    (hSelSubsetFull : ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover : KeyCover selectedKeys fullKeys) :
    kStar ∈ fullKeys ∧ ∀ k, k ∈ fullKeys → kStar ≤ k := by
  constructor
  · exact hSelSubsetFull kStar hStarSel
  · intro k hkFull
    rcases hCover k hkFull with ⟨ks, hksSel, hksLe⟩
    exact le_trans (hMinSel ks hksSel) hksLe

/-- The same key-cover hypothesis is enough to lift a selected-domain minimum
into the unique canonical minimum of the full bounded key set. -/
theorem keyCover_implies_exists_unique_full_canonical
    {PoolId : Type} [LinearOrder PoolId]
    {selectedKeys fullKeys : Finset (Key PoolId)}
    {kStar : Key PoolId}
    (hStarSel : kStar ∈ selectedKeys)
    (hMinSel : ∀ k, k ∈ selectedKeys → kStar ≤ k)
    (hSelSubsetFull : ∀ k, k ∈ selectedKeys → k ∈ fullKeys)
    (hCover : KeyCover selectedKeys fullKeys) :
    ∃! k, k ∈ fullKeys ∧ ∀ y, y ∈ fullKeys → k ≤ y := by
  have hFull :
      kStar ∈ fullKeys ∧ ∀ k, k ∈ fullKeys → kStar ≤ k :=
    keyCover_implies_selected_min_lifts_to_full
      hStarSel hMinSel hSelSubsetFull hCover
  exact ⟨kStar, hFull, by
    intro k hk
    exact le_antisymm (hk.2 _ hFull.1) (hFull.2 _ hk.1)⟩

end ExactOutManyPoolKeyCoverBridge
end ZenoDEX
end TauSwap
