import Mathlib

/-!
# ZenoProof Collusion Bound for Oracle Dispute Games

## Motivation

The dispute game bound (`ZenoProofDisputeGameBound.lean`) proves that a single
reporter's frivolous dispute is deterred when the bond `D` satisfies:

```text
p_f * G + (BPS - p_f) * M_rej < D * BPS
```

where `G = R + M_up` is the honest gain, `p_f` is the probability the frivolous
dispute is upheld, and `M_rej` is the MEV from a rejected dispute.

This file answers: does the same bond deter *collusion* among `k` reporters?

## Three Bonding Models

We analyze three models of collusion:

1. **Per-identity bond, per-head reward**: Each colluder posts bond `D` and
   receives the full reward `G`. Per-colluder profit equals the single-reporter
   profit. Collusion is *invariant*: the bond that deters one deters all.

2. **Per-identity bond, split reward**: Each colluder posts bond `D` but the
   total reward `G` is split among `k` colluders. Per-colluder profit is
   *lower* than single-reporter. Collusion is *harder* to profit from.

3. **Shared bond, per-head reward**: The coalition posts a single bond `D`
   shared among `k` colluders, but each receives the full reward `G`.
   Per-colluder profit is *higher* than single-reporter. Collusion is
   *easier*: the bond must scale linearly with `k`.

## Main Results

- `collusion_invariance_per_head`: Model 1 deterrence = single-reporter deterrence
- `split_reward_amplifies_deterrence`: Model 2 deterrence ≥ single-reporter deterrence
- `shared_bond_requires_scaling`: Model 3 deterrence requires bond scaled by `k`
- `per_identity_bond_blocks_all_collusion`: Model 1 + Model 2 combined: per-identity
  bonding blocks all collusion regardless of reward allocation

## Protocol Design Implication

Per-identity bonding is the correct design: the bond `D` sized for
single-reporter deterrence blocks all collusion sizes under any reward
allocation. Shared bonding is insecure and requires unbounded bond growth.
-/

namespace Internal
namespace ZenoProofCollusionBound

/-- Basis points scale (10000). -/
abbrev BPS : Nat := 10000

/-- Frivolous dispute MEV gain (scaled by BPS):
`p_f * G + (BPS - p_f) * M_rej` where `G` is honest gain. -/
def frivolousScaled (G M_rej p_f : Nat) : Nat :=
  p_f * G + (BPS - p_f) * M_rej

/-- Bond cost (scaled by BPS): `D * BPS`. -/
def bondScaled (D : Nat) : Nat := D * BPS

/-- Single-reporter frivolous dispute is deterred.
Requires `p_f ≤ BPS` for the probability domain to be valid. -/
def singleDeterred (G M_rej D p_f : Nat) : Prop :=
  p_f ≤ BPS ∧ frivolousScaled G M_rej p_f < bondScaled D

/-- Model 1: per-identity bond, per-head reward.
Each colluder posts bond `D`, each receives full reward `G`.
Per-colluder profit = single-reporter profit. -/
def collusionDeterredPerHead (G M_rej D p_f : Nat) (_k : Nat) : Prop :=
  p_f ≤ BPS ∧ frivolousScaled G M_rej p_f < bondScaled D

/-- Model 2: per-identity bond, split reward.
Each colluder posts bond `D`, reward `G` split among `k`.
Per-colluder profit scaled by `k`: `frivolousScaled - k * bondScaled`.
Deterred iff `frivolousScaled < k * bondScaled`. -/
def collusionDeterredSplit (G M_rej D p_f k : Nat) : Prop :=
  p_f ≤ BPS ∧ frivolousScaled G M_rej p_f < k * bondScaled D

/-- Model 3: shared bond, per-head reward.
Coalition posts single bond `D`, each receives full reward `G`.
Per-colluder profit scaled by `k`: `k * frivolousScaled - bondScaled`.
Deterred iff `k * frivolousScaled < bondScaled`. -/
def collusionDeterredShared (G M_rej D p_f k : Nat) : Prop :=
  p_f ≤ BPS ∧ k * frivolousScaled G M_rej p_f < bondScaled D

/-! ## Theorem 1: Collusion Invariance (Per-Identity Bond, Per-Head Reward) -/

/-- **Collusion Invariance**: under per-identity bonding with per-head reward,
the deterrence condition is identical for any coalition size `k ≥ 1`.
The bond that deters a single reporter deters all coalitions. -/
theorem collusion_invariance_per_head
    (G M_rej D p_f k : Nat) (_hk : 1 ≤ k) :
    collusionDeterredPerHead G M_rej D p_f k ↔
    singleDeterred G M_rej D p_f := by
  unfold collusionDeterredPerHead singleDeterred
  rfl

/-! ## Theorem 2: Split-Reward Deterrence Amplification -/

/-- **Deterrence Amplification**: under per-identity bonding with split reward,
if the single reporter is deterred, then any coalition of `k ≥ 2` is also
deterred. Splitting the reward makes collusion *less* profitable. -/
theorem split_reward_amplifies_deterrence
    (G M_rej D p_f k : Nat) (hk : 2 ≤ k)
    (hSingle : singleDeterred G M_rej D p_f) :
    collusionDeterredSplit G M_rej D p_f k := by
  unfold singleDeterred collusionDeterredSplit frivolousScaled bondScaled at *
  refine ⟨hSingle.1, ?_⟩
  have hMono : D * BPS ≤ k * (D * BPS) := by
    have hk1 : 1 ≤ k := by omega
    have h := Nat.mul_le_mul_right (D * BPS) hk1
    rw [Nat.one_mul] at h
    exact h
  exact Nat.lt_of_lt_of_le hSingle.2 hMono

/-! ## Theorem 3: Shared Bond Requires Scaling -/

/-- **Shared Bond Condition**: under shared bonding with per-head reward,
deterrence of `k` colluders requires `k * frivolousScaled < D * BPS`.
This is a stronger condition than single-reporter deterrence for `k ≥ 2`. -/
theorem shared_bond_condition
    (G M_rej D p_f k : Nat) (_hk : 1 ≤ k)
    (hShared : collusionDeterredShared G M_rej D p_f k) :
    k * frivolousScaled G M_rej p_f < D * BPS := by
  unfold collusionDeterredShared bondScaled at hShared
  exact hShared.2

/-- **Shared Bond Scales Linearly**: if bond `D` deters a single reporter,
then bond `k * D` deters `k` colluders under shared bonding.
This proves the linear scaling factor: the shared bond must grow
proportionally with coalition size. -/
theorem shared_bond_scales_linearly
    (G M_rej D p_f k : Nat) (hk : 1 ≤ k)
    (hSingle : singleDeterred G M_rej D p_f) :
    collusionDeterredShared G M_rej (k * D) p_f k := by
  refine ⟨hSingle.1, ?_⟩
  unfold bondScaled
  have hFriv : frivolousScaled G M_rej p_f < D * BPS := hSingle.2
  have hScaled : k * frivolousScaled G M_rej p_f < k * (D * BPS) :=
    Nat.mul_lt_mul_of_pos_left hFriv (by omega)
  have hDistrib : k * (D * BPS) = (k * D) * BPS := by ring
  exact hScaled.trans_le (Nat.le_of_eq hDistrib)

/-- **Shared Bond Scaling Factor**: if a single reporter is deterred at bond
`D`, then deterring `k` colluders under shared bonding requires
`k * frivolousScaled < D * BPS`. For `k ≥ 2` this is strictly stronger than
the single-reporter condition: the shared bond must exceed `k` times the
per-colluder frivolous gain. The bond grows linearly with coalition size. -/
theorem shared_bond_scaling_factor
    (G M_rej D p_f k : Nat) (_hk : 1 ≤ k)
    (hSingle : singleDeterred G M_rej D p_f)
    (hShared : collusionDeterredShared G M_rej D p_f k) :
    k * frivolousScaled G M_rej p_f < D * BPS ∧
    frivolousScaled G M_rej p_f < D * BPS := by
  exact ⟨hShared.2, hSingle.2⟩

/-- **Shared Bond Implies Single Deterred**: if `k` colluders are deterred
under shared bonding, then `D * BPS > k * frivolousScaled ≥ frivolousScaled`
(since `k ≥ 1`). Therefore the single reporter is also deterred. -/
theorem shared_bond_implies_single_deterred
    (G M_rej D p_f k : Nat) (hk : 1 ≤ k)
    (hShared : collusionDeterredShared G M_rej D p_f k) :
    singleDeterred G M_rej D p_f := by
  refine ⟨hShared.1, ?_⟩
  unfold collusionDeterredShared at hShared
  have hk_f : frivolousScaled G M_rej p_f ≤ k * frivolousScaled G M_rej p_f := by
    exact Nat.le_mul_of_pos_left (frivolousScaled G M_rej p_f) (by omega)
  exact Nat.lt_of_le_of_lt hk_f hShared.2

/-! ## Theorem 4: Per-Identity Bond Blocks All Collusion -/

/-- **Universal Collusion Resistance**: under per-identity bonding, if the
single reporter is deterred, then:
- Model 1 (per-head reward): all coalitions are deterred (invariance)
- Model 2 (split reward): all coalitions of `k ≥ 2` are deterred (amplification)

The bond `D` sized for single-reporter deterrence blocks all collusion
regardless of reward allocation. -/
theorem per_identity_bond_blocks_all_collusion
    (G M_rej D p_f k : Nat) (hk : 1 ≤ k)
    (hSingle : singleDeterred G M_rej D p_f) :
    collusionDeterredPerHead G M_rej D p_f k ∧
    (2 ≤ k → collusionDeterredSplit G M_rej D p_f k) := by
  refine ⟨?_, ?_⟩
  · exact (collusion_invariance_per_head G M_rej D p_f k hk).mpr hSingle
  · intro hk2
    exact split_reward_amplifies_deterrence G M_rej D p_f k hk2 hSingle

/-! ## Non-Vacuity Witnesses -/

/-- Witness: single reporter deterred with `G = 100`, `M_rej = 10`,
`D = 20`, `p_f = 1000` (10%).
`frivolousScaled = 1000 * 100 + 9000 * 10 = 190000`
`bondScaled = 20 * 10000 = 200000 > 190000`. Deterred. -/
theorem witness_single_deterred :
    singleDeterred 100 10 20 1000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-- Witness: same parameters, k = 5 colluders, per-head reward.
Collusion is also deterred (invariance). -/
theorem witness_collusion_deterred_per_head :
    collusionDeterredPerHead 100 10 20 1000 5 := by
  unfold collusionDeterredPerHead frivolousScaled bondScaled BPS
  decide

/-- Witness: same parameters, k = 5 colluders, split reward.
Collusion is even more deterred (amplification). -/
theorem witness_collusion_deterred_split :
    collusionDeterredSplit 100 10 20 1000 5 := by
  unfold collusionDeterredSplit frivolousScaled bondScaled BPS
  decide

/-- Witness: shared bond with k = 5 is NOT deterred by D = 20.
`5 * 190000 = 950000 > 200000`. Shared bond is vulnerable. -/
theorem witness_shared_bond_vulnerable :
    ¬ collusionDeterredShared 100 10 20 1000 5 := by
  unfold collusionDeterredShared frivolousScaled bondScaled BPS
  decide

/-- Witness: shared bond needs D = 100 to deter k = 5.
`5 * 190000 = 950000 < 100 * 10000 = 1000000`. Just barely deterred. -/
theorem witness_shared_bond_deterred_at_5x :
    collusionDeterredShared 100 10 100 1000 5 := by
  unfold collusionDeterredShared frivolousScaled bondScaled BPS
  decide

/-- Witness: deficient per-identity bond D = 10 admits single reporter.
`frivolousScaled = 190000 > 100000 = bondScaled`. Not deterred. -/
theorem witness_deficient_bond_admits_single :
    ¬ singleDeterred 100 10 10 1000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-- Witness: `k = 1` split reward equals single-reporter deterrence.
Split reward with `k = 1` is the same as per-head with `k = 1`. -/
theorem witness_k1_split_equals_single :
    collusionDeterredSplit 100 10 20 1000 1 ↔
    singleDeterred 100 10 20 1000 := by
  unfold collusionDeterredSplit singleDeterred
  rfl

/-- Witness: `k = 2` split reward is strictly stronger than single-reporter.
At the boundary `frivolousScaled = bondScaled` (single NOT deterred),
`k = 2` split IS deterred: `frivolousScaled < 2 * bondScaled`. -/
theorem witness_k2_split_deterred_at_boundary :
    ¬ singleDeterred 190 0 19 1000 ∧
    collusionDeterredSplit 190 0 19 1000 2 := by
  refine ⟨?_, ?_⟩
  · unfold singleDeterred frivolousScaled bondScaled BPS
    decide
  · unfold collusionDeterredSplit frivolousScaled bondScaled BPS
    decide

/-! ## Tightness: Boundary Cases -/

/-- Boundary: at `frivolousScaled = bondScaled`, the single reporter is
exactly indifferent (zero profit). This is the tight boundary.
`G = 190, M_rej = 0, p_f = 1000, D = 19`:
`frivolousScaled = 1000 * 190 + 9000 * 0 = 190000`
`bondScaled = 19 * 10000 = 190000`
Not strictly deterred (equality, not strict inequality). -/
theorem witness_boundary_equality_not_deterred :
    ¬ singleDeterred 190 0 19 1000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-- Boundary: one unit above the boundary, deterrence holds.
`D = 20`: `bondScaled = 200000 > 190000`. -/
theorem witness_boundary_plus_one_deterred :
    singleDeterred 190 0 20 1000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-! ## BPS Endpoint Witnesses: p_f = 0 and p_f = BPS -/

/-- Witness: `p_f = 0` (frivolous dispute never upheld).
`frivolousScaled = 0 * G + BPS * M_rej = BPS * M_rej`.
With `M_rej = 10`, `D = 11`: `frivolousScaled = 100000 < 110000`. Deterred.
The `p_f ≤ BPS` precondition holds trivially. -/
theorem witness_p_f_zero_deterred :
    singleDeterred 100 10 11 0 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-- Witness: `p_f = BPS` (frivolous dispute always upheld).
`frivolousScaled = BPS * G + 0 * M_rej = BPS * G`.
With `G = 100`, `D = 101`: `frivolousScaled = 1000000 < 1010000`. Deterred.
The `p_f ≤ BPS` precondition holds with equality. -/
theorem witness_p_f_bps_deterred :
    singleDeterred 100 10 101 10000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-- Witness: `p_f = BPS` is NOT deterred when bond is too small.
`G = 100`, `D = 100`: `frivolousScaled = 1000000 = 1000000`. Equality, not deterred. -/
theorem witness_p_f_bps_not_deterred_at_boundary :
    ¬ singleDeterred 100 10 100 10000 := by
  unfold singleDeterred frivolousScaled bondScaled BPS
  decide

/-! ## Protocol Design Corollary -/

/-- **Protocol Design Rule**: to block all collusion under per-identity
bonding, size the bond `D` to satisfy the single-reporter deterrence
condition. This is sufficient for all coalition sizes and reward allocations. -/
theorem protocol_design_rule
    (G M_rej D p_f : Nat)
    (hDeterrence : singleDeterred G M_rej D p_f) :
    ∀ k : Nat, 1 ≤ k →
      collusionDeterredPerHead G M_rej D p_f k ∧
      (2 ≤ k → collusionDeterredSplit G M_rej D p_f k) := by
  intro k hk
  exact per_identity_bond_blocks_all_collusion G M_rej D p_f k hk hDeterrence

end ZenoProofCollusionBound
end Internal
