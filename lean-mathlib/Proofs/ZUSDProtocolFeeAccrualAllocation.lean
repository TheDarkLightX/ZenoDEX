import Mathlib

/-!
# zUSD protocol-fee accrual-allocation algebra

This file proves the local partition equations used when one exact positive
borrowing-fee occurrence is allocated into buyback, treasury, and rewards
claims at accrual time.

It does not prove SRGD selection, occurrence extraction from authenticated
borrowing, U256 refinement, configuration activation against current state,
destination lineage, publication, mounting, or no-bypass.
-/

namespace ZUSDProtocolFeeAccrualAllocation

/-- Scalar current/cumulative claims and their three semantic-role partitions. -/
structure State where
  scalarOutstanding : Nat
  scalarCumulative : Nat
  buybackOutstanding : Nat
  treasuryOutstanding : Nat
  rewardsOutstanding : Nat
  buybackCumulative : Nat
  treasuryCumulative : Nat
  rewardsCumulative : Nat
  deriving DecidableEq, Repr

/-- One exact occurrence amount and the three amounts chosen by the allocator. -/
structure Allocation where
  amount : Nat
  buyback : Nat
  treasury : Nat
  rewards : Nat
  deriving DecidableEq, Repr

/-- The allocator neither creates nor destroys atoms within this occurrence. -/
def Conserved (a : Allocation) : Prop :=
  a.amount = a.buyback + a.treasury + a.rewards

/-- Scalar current and cumulative claims equal their complete role partitions. -/
def Partitioned (s : State) : Prop :=
  s.scalarOutstanding =
      s.buybackOutstanding + s.treasuryOutstanding + s.rewardsOutstanding ∧
    s.scalarCumulative =
      s.buybackCumulative + s.treasuryCumulative + s.rewardsCumulative

/-- No current role claim exceeds the amount cumulatively accrued to that role. -/
def RoleClaimsValid (s : State) : Prop :=
  s.buybackOutstanding ≤ s.buybackCumulative ∧
    s.treasuryOutstanding ≤ s.treasuryCumulative ∧
    s.rewardsOutstanding ≤ s.rewardsCumulative

/-- Accrue the scalar occurrence and its already-chosen three-role allocation. -/
def accrue (s : State) (a : Allocation) : State :=
  { scalarOutstanding := s.scalarOutstanding + a.amount
    scalarCumulative := s.scalarCumulative + a.amount
    buybackOutstanding := s.buybackOutstanding + a.buyback
    treasuryOutstanding := s.treasuryOutstanding + a.treasury
    rewardsOutstanding := s.rewardsOutstanding + a.rewards
    buybackCumulative := s.buybackCumulative + a.buyback
    treasuryCumulative := s.treasuryCumulative + a.treasury
    rewardsCumulative := s.rewardsCumulative + a.rewards }

/-- A conserved allocation preserves both scalar-to-role partition equations. -/
theorem accrue_preserves_partitioned
    (s : State)
    (a : Allocation)
    (hpartitioned : Partitioned s)
    (hconserved : Conserved a) :
    Partitioned (accrue s a) := by
  simp [Partitioned, Conserved, accrue] at *
  omega

/-- Adding the same amount to a role's current and cumulative claims preserves validity. -/
theorem accrue_preserves_role_claims_valid
    (s : State)
    (a : Allocation)
    (hvalid : RoleClaimsValid s) :
    RoleClaimsValid (accrue s a) := by
  simp [RoleClaimsValid, accrue] at *
  omega

/-- The local composition invariant is preserved by one conserved occurrence. -/
theorem accrue_preserves_complete_local_invariant
    (s : State)
    (a : Allocation)
    (hinvariant : Partitioned s ∧ RoleClaimsValid s)
    (hconserved : Conserved a) :
    Partitioned (accrue s a) ∧ RoleClaimsValid (accrue s a) := by
  exact ⟨
    accrue_preserves_partitioned s a hinvariant.1 hconserved,
    accrue_preserves_role_claims_valid s a hinvariant.2
  ⟩

/-- The same local invariant lifts through an ordered word of exact occurrences. -/
theorem fold_preserves_complete_local_invariant
    (allocations : List Allocation)
    (s : State)
    (hall : ∀ a ∈ allocations, Conserved a)
    (hinvariant : Partitioned s ∧ RoleClaimsValid s) :
    let post := allocations.foldl accrue s
    Partitioned post ∧ RoleClaimsValid post := by
  induction allocations generalizing s with
  | nil => simpa
  | cons a tail ih =>
      simp only [List.foldl_cons]
      apply ih (accrue s a)
      · intro candidate hmember
        exact hall candidate (by simp [hmember])
      · exact accrue_preserves_complete_local_invariant s a hinvariant (hall a (by simp))

#print axioms accrue_preserves_partitioned
#print axioms accrue_preserves_complete_local_invariant
#print axioms fold_preserves_complete_local_invariant

end ZUSDProtocolFeeAccrualAllocation
