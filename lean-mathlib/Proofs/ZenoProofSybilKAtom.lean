import Proofs.ZenoProofSybilBondBound

/-!
# ZenoProof k-Atom Sybil Bound

Checked companion to `ZenoProofSybilBondBound.lean`.

The two-atom split is the binding case for equal-split rewards. This file records
the k-atom cross-multiplied condition used by runtime and tokenomics notes, plus
small checked witnesses that keep the imported module non-empty and hash-bound by
the proof toolchain lock.
-/

namespace Internal
namespace ZenoProofSybilKAtom

/-- Cross-multiplied k-atom Sybil unprofitability condition.

`n` is the original cohort size, `k` is the number of identities controlled by
the splitter after registration, `V` is the reward pool, and `B` is the
per-additional-identity bond. The post-split population is `n + k - 1`, and the
attacker pays `(k - 1) * B` in additional bonds.
-/
def kAtomUnprofitable (V B n k : Nat) : Prop :=
  k * V * n ≤ V * (n + k - 1) + (k - 1) * B * n * (n + k - 1)

/-- For `k = 2`, the k-atom condition is exactly the existing two-atom
Sybil-bond condition. -/
theorem two_atom_condition_matches_bond_bound (V B n : Nat) :
    kAtomUnprofitable V B n 2 ↔
      ZenoProofSybilBondBound.sybilUnprofitable V B n := by
  unfold kAtomUnprofitable ZenoProofSybilBondBound.sybilUnprofitable
  norm_num

/-- Larger splits have a denominator at least as large as the two-atom split
when `k ≥ 2`. -/
theorem denominator_ge_two_atom (n k : Nat) (hk : 2 ≤ k) :
    n + 1 ≤ n + k - 1 := by
  omega

/-- Witness inherited from the two-atom file: `B = 15` blocks the `V = 100`,
`n = 4`, `k = 2` Sybil split. -/
theorem witness_two_atom_bond_blocks_sybil :
    kAtomUnprofitable 100 15 4 2 := by
  unfold kAtomUnprofitable
  decide

/-- The same bond also blocks a three-atom split in the checked witness. -/
theorem witness_three_atom_bond_blocks_sybil :
    kAtomUnprofitable 100 15 4 3 := by
  unfold kAtomUnprofitable
  decide

/-- A deficient bond remains rejected at the binding two-atom boundary. -/
theorem witness_deficient_two_atom_bond_admits_sybil :
    ¬ kAtomUnprofitable 100 10 4 2 := by
  unfold kAtomUnprofitable
  decide

end ZenoProofSybilKAtom
end Internal
