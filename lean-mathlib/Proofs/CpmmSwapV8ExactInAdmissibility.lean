import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

import Proofs.CPMMInvariants
import Proofs.CpmmSwapV8ExactOutMinimality

namespace TauSwap
namespace CPMM
namespace V8

open CPMMInvariants

def BPS : Nat := 10000

def exactInNet (gross fee_bps : Nat) : Nat :=
  gross - ((gross * fee_bps) ⌈/⌉ BPS)

def exactInNetFloor (gross fee_bps : Nat) : Nat :=
  (gross * (BPS - fee_bps)) / BPS

def exactInOutput (rin rout gross fee_bps : Nat) : Nat :=
  swapOutput rin rout (exactInNet gross fee_bps)

def exactInOutputFloor (rin rout gross fee_bps : Nat) : Nat :=
  swapOutput rin rout (exactInNetFloor gross fee_bps)

lemma exactInNet_eq_floor (gross fee_bps : Nat) (_hfee : fee_bps ≤ BPS) :
    exactInNet gross fee_bps = exactInNetFloor gross fee_bps := by
  simpa [BPS, exactInNet, exactInNetFloor] using
    (net_actual_eq_floor_mul gross fee_bps BPS (by decide))

lemma exactInNetFloor_mono {fee_bps a b : Nat} (hab : a ≤ b) :
    exactInNetFloor a fee_bps ≤ exactInNetFloor b fee_bps := by
  unfold exactInNetFloor BPS
  exact Nat.div_le_div_right (Nat.mul_le_mul_right (10000 - fee_bps) hab)

lemma exactInNet_mono {fee_bps a b : Nat} (hfee : fee_bps ≤ BPS) (hab : a ≤ b) :
    exactInNet a fee_bps ≤ exactInNet b fee_bps := by
  rw [exactInNet_eq_floor _ _ hfee, exactInNet_eq_floor _ _ hfee]
  exact exactInNetFloor_mono hab

lemma exactInNet_positive_suffix {fee_bps a b : Nat}
    (hfee : fee_bps ≤ BPS)
    (hab : a ≤ b)
    (hpos : 0 < exactInNet a fee_bps) :
    0 < exactInNet b fee_bps := by
  have hmono : exactInNet a fee_bps ≤ exactInNet b fee_bps := exactInNet_mono hfee hab
  exact lt_of_lt_of_le hpos hmono

lemma swapOutput_mono_in_net {rin rout netSmall netLarge : Nat}
    (hrin : 0 < rin)
    (hnet : netSmall ≤ netLarge) :
    swapOutput rin rout netSmall ≤ swapOutput rin rout netLarge := by
  set outSmall := swapOutput rin rout netSmall
  have houtSmall_le_rout : outSmall ≤ rout := by
    dsimp [outSmall, swapOutput]
    apply Nat.div_le_of_le_mul
    calc
      rout * netSmall ≤ rout * (rin + netSmall) :=
        Nat.mul_le_mul_left rout (Nat.le_add_left netSmall rin)
      _ = (rin + netSmall) * rout := by
        rw [Nat.mul_comm]
  have hdiv : outSmall * (rin + netSmall) ≤ rout * netSmall := by
    simpa [outSmall, swapOutput] using Nat.div_mul_le_self (rout * netSmall) (rin + netSmall)
  have hgap : outSmall * (netLarge - netSmall) ≤ rout * (netLarge - netSmall) := by
    exact Nat.mul_le_mul_right (netLarge - netSmall) houtSmall_le_rout
  have hdecomp : netLarge = netSmall + (netLarge - netSmall) := by
    exact (Nat.add_sub_of_le hnet).symm
  have hsplit_left :
      outSmall * (rin + netLarge) =
        outSmall * (rin + netSmall) + outSmall * (netLarge - netSmall) := by
    conv_lhs => rw [hdecomp]
    rw [← Nat.add_assoc, Nat.mul_add]
  have hsplit_right : rout * netLarge = rout * netSmall + rout * (netLarge - netSmall) := by
    conv_lhs => rw [hdecomp]
    rw [Nat.mul_add]
  have hden : 0 < rin + netLarge := Nat.add_pos_left hrin netLarge
  exact (Nat.le_div_iff_mul_le hden).2 <| by
    calc
      outSmall * (rin + netLarge)
          = outSmall * (rin + netSmall) + outSmall * (netLarge - netSmall) := hsplit_left
      _ ≤ rout * netSmall + rout * (netLarge - netSmall) := add_le_add hdiv hgap
      _ = rout * netLarge := hsplit_right.symm

lemma exactInOutput_eq_floor (rin rout gross fee_bps : Nat) (hfee : fee_bps ≤ BPS) :
    exactInOutput rin rout gross fee_bps = exactInOutputFloor rin rout gross fee_bps := by
  simp [exactInOutput, exactInOutputFloor, exactInNet_eq_floor _ _ hfee]

lemma exactInOutput_mono {rin rout fee_bps a b : Nat}
    (hfee : fee_bps ≤ BPS)
    (hrin : 0 < rin)
    (hab : a ≤ b) :
    exactInOutput rin rout a fee_bps ≤ exactInOutput rin rout b fee_bps := by
  rw [exactInOutput_eq_floor _ _ _ _ hfee, exactInOutput_eq_floor _ _ _ _ hfee]
  exact swapOutput_mono_in_net hrin (exactInNetFloor_mono hab)

theorem exactInPositiveOutput_suffix {rin rout fee_bps a b : Nat}
    (hfee : fee_bps ≤ BPS)
    (hrin : 0 < rin)
    (hab : a ≤ b)
    (hpos : 0 < exactInOutput rin rout a fee_bps) :
    0 < exactInOutput rin rout b fee_bps := by
  have hmono : exactInOutput rin rout a fee_bps ≤ exactInOutput rin rout b fee_bps :=
    exactInOutput_mono hfee hrin hab
  exact lt_of_lt_of_le hpos hmono

end V8
end CPMM
end TauSwap
