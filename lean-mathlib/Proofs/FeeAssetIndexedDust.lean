import Mathlib.Tactic

/-!
# Asset-indexed fee-dust isolation

This module models fee accounting as three pointwise ledgers over an arbitrary
asset type with decidable equality.  A one-asset update records the fee,
distributed amount, and residual dust only at its target key.  Admissibility
requires the distributed amount to be no greater than the current fee plus the
target asset's carried dust.

The arithmetic is over `Nat`, so the results are not restricted to a bounded
test domain.  The proved scope is local semantic algebra: exact target-asset
conservation, non-target isolation, commutation at distinct keys, and rejection
of a denomination-tagged dust witness at a different asset's equation.

Nonclaims: this module does not prove Python immutable-map ownership, canonical
map serialization, state-root encoding, or a full refinement from the runtime
fee implementation to this model.  It proves the distinct-key adjacent swap
needed for a permutation lift, without claiming arbitrary-list fold invariance.
-/

namespace ZenoDEX.FeeAssetIndexedDust

variable {Asset : Type*} [DecidableEq Asset]

/-- Pointwise fee-accounting state.  Every quantity is denominated by its key. -/
@[ext]
structure State (Asset : Type*) where
  fees : Asset -> Nat
  distributed : Asset -> Nat
  dust : Asset -> Nat

/-- The one-asset update cannot distribute more than the newly available amount. -/
def Admissible (state : State Asset) (asset : Asset) (fee distributed : Nat) : Prop :=
  distributed <= fee + state.dust asset

/-- Every asset's cumulative distributed value plus carry equals cumulative fees. -/
def Conserved (state : State Asset) : Prop :=
  ∀ asset, state.distributed asset + state.dust asset = state.fees asset

/--
Apply one admitted asset-local fee update.

The proof argument is a construction boundary: callers cannot build an accepted
transition with a distributed amount above `fee + oldDust`.
-/
def applyOne
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (_admitted : Admissible state asset fee distributed) : State Asset where
  fees := Function.update state.fees asset (state.fees asset + fee)
  distributed :=
    Function.update state.distributed asset (state.distributed asset + distributed)
  dust := Function.update state.dust asset (fee + state.dust asset - distributed)

@[simp]
theorem apply_one_target_fees
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed) :
    (applyOne state asset fee distributed admitted).fees asset =
      state.fees asset + fee := by
  simp [applyOne]

@[simp]
theorem apply_one_target_distributed
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed) :
    (applyOne state asset fee distributed admitted).distributed asset =
      state.distributed asset + distributed := by
  simp [applyOne]

@[simp]
theorem apply_one_target_dust
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed) :
    (applyOne state asset fee distributed admitted).dust asset =
      fee + state.dust asset - distributed := by
  simp [applyOne]

/-- The target asset conserves exactly: distributed value plus new dust is available value. -/
theorem target_asset_exact_conservation
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed) :
    distributed + (applyOne state asset fee distributed admitted).dust asset =
      fee + state.dust asset := by
  simp only [apply_one_target_dust]
  exact Nat.add_sub_of_le admitted

/-- Every pointwise ledger entry at a non-target asset is unchanged. -/
theorem all_other_assets_unchanged
    (state : State Asset)
    (asset other : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed)
    (other_ne_target : other ≠ asset) :
    (applyOne state asset fee distributed admitted).fees other = state.fees other ∧
      (applyOne state asset fee distributed admitted).distributed other =
        state.distributed other ∧
      (applyOne state asset fee distributed admitted).dust other = state.dust other := by
  simp [applyOne, other_ne_target]

/-- An admitted one-asset update preserves the complete pointwise ledger invariant. -/
theorem apply_one_preserves_conserved
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (conserved : Conserved state)
    (admitted : Admissible state asset fee distributed) :
    Conserved (applyOne state asset fee distributed admitted) := by
  intro key
  by_cases key_eq : key = asset
  · subst key
    simp only [apply_one_target_distributed, apply_one_target_dust,
      apply_one_target_fees]
    have local_conservation :
        distributed + (fee + state.dust asset - distributed) =
          fee + state.dust asset := Nat.add_sub_of_le admitted
    rw [Nat.add_assoc, local_conservation]
    have pre_conservation := conserved asset
    omega
  · have unchanged :=
      all_other_assets_unchanged state asset key fee distributed admitted key_eq
    rw [unchanged.1, unchanged.2.1, unchanged.2.2]
    exact conserved key

/-- Updating one asset preserves admissibility of an update at a distinct asset. -/
theorem admissible_after_distinct_update
    (state : State Asset)
    (assetA assetB : Asset)
    (feeA distributedA feeB distributedB : Nat)
    (assetA_ne_assetB : assetA ≠ assetB)
    (admittedA : Admissible state assetA feeA distributedA)
    (admittedB : Admissible state assetB feeB distributedB) :
    Admissible
      (applyOne state assetA feeA distributedA admittedA)
      assetB
      feeB
      distributedB := by
  simpa [Admissible, applyOne, assetA_ne_assetB.symm] using admittedB

/-- Valid updates on distinct asset keys commute exactly as state values. -/
theorem distinct_asset_updates_commute
    (state : State Asset)
    (assetA assetB : Asset)
    (feeA distributedA feeB distributedB : Nat)
    (assetA_ne_assetB : assetA ≠ assetB)
    (admittedA : Admissible state assetA feeA distributedA)
    (admittedB : Admissible state assetB feeB distributedB) :
    let admittedBafterA :=
      admissible_after_distinct_update
        state assetA assetB feeA distributedA feeB distributedB
        assetA_ne_assetB admittedA admittedB
    let admittedAafterB :=
      admissible_after_distinct_update
        state assetB assetA feeB distributedB feeA distributedA
        assetA_ne_assetB.symm admittedB admittedA
    applyOne
        (applyOne state assetA feeA distributedA admittedA)
        assetB feeB distributedB admittedBafterA =
      applyOne
        (applyOne state assetB feeB distributedB admittedB)
        assetA feeA distributedA admittedAafterB := by
  dsimp only
  have assetB_ne_assetA := assetA_ne_assetB.symm
  ext key <;>
    simp [applyOne, assetA_ne_assetB, assetB_ne_assetA,
      Function.update_comm assetA_ne_assetB]

/-- A quantity carries its denomination in addition to its numeric units. -/
structure TaggedAmount (Asset : Type*) where
  asset : Asset
  units : Nat

/-- The tagged dust value read from one point of the dust ledger. -/
def dustClaim (state : State Asset) (asset : Asset) : TaggedAmount Asset :=
  { asset := asset, units := state.dust asset }

/--
A conservation equation accepts old and new dust only when both denomination
tags equal the asset whose fee equation is being checked.
-/
def SatisfiesAssetEquation
    (expectedAsset : Asset)
    (oldDust newDust : TaggedAmount Asset)
    (fee distributed : Nat) : Prop :=
  oldDust.asset = expectedAsset ∧
    newDust.asset = expectedAsset ∧
    distributed + newDust.units = fee + oldDust.units

/-- The target asset's tagged pre/post dust values satisfy its admitted equation. -/
theorem target_dust_claim_satisfies_asset_equation
    (state : State Asset)
    (asset : Asset)
    (fee distributed : Nat)
    (admitted : Admissible state asset fee distributed) :
    SatisfiesAssetEquation
      asset
      (dustClaim state asset)
      (dustClaim (applyOne state asset fee distributed admitted) asset)
      fee
      distributed := by
  constructor
  · rfl
  constructor
  · rfl
  exact target_asset_exact_conservation state asset fee distributed admitted

omit [DecidableEq Asset] in
/-- Dust tagged as asset A cannot be supplied as the old dust in asset B's equation. -/
theorem no_asset_a_dust_can_satisfy_asset_b_equation
    (state nextState : State Asset)
    (assetA assetB : Asset)
    (fee distributed : Nat)
    (assetA_ne_assetB : assetA ≠ assetB) :
    ¬ (SatisfiesAssetEquation
      assetB
      (dustClaim state assetA)
      (dustClaim nextState assetB)
      fee
      distributed) := by
  intro satisfies
  exact assetA_ne_assetB satisfies.1

/-- Concrete non-vacuity witness for an accepted update with nonzero residual dust. -/
theorem witness_target_conservation :
    let state : State Bool :=
      { fees := fun _ => 0, distributed := fun _ => 0, dust := fun _ => 1 }
    let admitted : Admissible state true 7 5 := by
      change 5 ≤ 7 + 1
      omega
    5 + (applyOne state true 7 5 admitted).dust true = 8 := by
  native_decide

/-- Concrete witness that a `true`-tagged dust value is rejected at `false`. -/
theorem witness_cross_asset_dust_rejected :
    let state : State Bool :=
      { fees := fun _ => 0, distributed := fun _ => 0, dust := fun _ => 3 }
    ¬ (SatisfiesAssetEquation
      false
      (dustClaim state true)
      (dustClaim state false)
      0
      0) := by
  dsimp only
  simp [SatisfiesAssetEquation, dustClaim]

end ZenoDEX.FeeAssetIndexedDust
