import Std

/-!
Cumulative, independently floored entitlements with fixed weights summing to D.
Carry remains reserved under that same entitlement policy. This model does not
reassign per-occurrence residue already owned by another beneficiary. It proves
integer accounting, without service authenticity or economic utility premises.
-/

namespace ServiceFeeCarryV1

def payouts (F D : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => F * w / D + payouts F D ws

def remainders (F D : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => F * w % D + remainders F D ws

def carry (F D : Nat) (ws : List Nat) : Nat := F - payouts F D ws

theorem quotient_remainder_identity (F D : Nat) (ws : List Nat) :
    D * payouts F D ws + remainders F D ws = F * ws.sum := by
  induction ws with
  | nil => simp [payouts, remainders]
  | cons w ws ih =>
      simp only [payouts, remainders, List.sum_cons, Nat.mul_add]
      have h := Nat.div_add_mod (F * w) D
      omega

theorem remainders_lt_count (F D : Nat) (ws : List Nat)
    (hD : 0 < D) (hne : ws ≠ []) :
    remainders F D ws < D * ws.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
      cases ws with
      | nil => simpa [remainders] using Nat.mod_lt (F * w) hD
      | cons v vs =>
          have ht := ih (by simp)
          have h := Nat.add_lt_add (Nat.mod_lt (F * w) hD) ht
          simpa [remainders, Nat.mul_add, Nat.add_comm] using h

theorem payouts_le_fees (F D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    payouts F D ws ≤ F := by
  have h := quotient_remainder_identity F D ws
  rw [hweights, Nat.mul_comm F D] at h
  apply Nat.le_of_mul_le_mul_left (c := D) _ hD
  omega

theorem owned_partition (F D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    payouts F D ws + carry F D ws = F := by
  have h := payouts_le_fees F D ws hD hweights
  simp only [carry]
  omega

theorem carry_scaled (F D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    D * carry F D ws = remainders F D ws := by
  have h := quotient_remainder_identity F D ws
  rw [hweights, Nat.mul_comm F D] at h
  have hp := congrArg (fun n => D * n) (owned_partition F D ws hD hweights)
  simp only [Nat.mul_add] at hp
  omega

theorem carry_lt_claimant_count (F D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    carry F D ws < ws.length := by
  have hne : ws ≠ [] := by
    intro he
    simp [he] at hweights
    omega
  have h := remainders_lt_count F D ws hD hne
  rw [← carry_scaled F D ws hD hweights] at h
  exact Nat.lt_of_mul_lt_mul_left h

theorem payouts_monotone (F W D : Nat) (ws : List Nat) :
    payouts F D ws ≤ payouts (F + W) D ws := by
  induction ws with
  | nil => simp [payouts]
  | cons w ws ih =>
      simp only [payouts]
      exact Nat.add_le_add
        (Nat.div_le_div_right (Nat.mul_le_mul_right w (by omega : F ≤ F + W))) ih

/-- Incremental claims are funded by new fees plus release of reserved old carry. -/
theorem incremental_carry_identity (F W D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    payouts (F + W) D ws - payouts F D ws + carry (F + W) D ws =
      W + carry F D ws := by
  have hpre := owned_partition F D ws hD hweights
  have hpost := owned_partition (F + W) D ws hD hweights
  have hmono := payouts_monotone F W D ws
  omega

/-- At most m-1 old carry atoms can supplement W newly assigned fee atoms. -/
theorem incremental_payout_bound (F W D : Nat) (ws : List Nat)
    (hD : 0 < D) (hweights : ws.sum = D) :
    payouts (F + W) D ws - payouts F D ws ≤ W + (ws.length - 1) := by
  have hi := incremental_carry_identity F W D ws hD hweights
  have hc := carry_lt_claimant_count F D ws hD hweights
  omega

example : payouts 2 2 [1, 1] - payouts 1 2 [1, 1] = 2 := by decide
example : carry 1 2 [1, 1] = 1 ∧ carry 2 2 [1, 1] = 0 := by decide

end ServiceFeeCarryV1
