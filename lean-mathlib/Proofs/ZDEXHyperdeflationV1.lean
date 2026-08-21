import Mathlib

/-!
Restricted integer theorems for the experimental ZDEX hyperdeflation core.

The runtime retained amount is

  retainedSupply S p q = 1 + floor((p*S - 1) / q)

for positive `S`, `p`, and `q`.  This is the positive-integer form of
`ceil(p*S/q)`.  The theorems prove positivity, the retained lower bound for an
accepted burn, exact scaling conservation, and finite geometric positivity.

They do not prove market demand, route authenticity, complete bucket coverage,
u128 admission, migration authority, or an infinite execution on finite
hardware.
-/

namespace Proofs
namespace ZDEXHyperdeflationV1

/-- Runtime-aligned positive-integer retained-supply formula. -/
def retainedSupply (supply numerator denominator : Nat) : Nat :=
  1 + (numerator * supply - 1) / denominator

/-- Burn headroom under the retained-supply policy. -/
def burnHeadroom (supply numerator denominator : Nat) : Nat :=
  supply - retainedSupply supply numerator denominator

/-- The retained amount is positive by construction. -/
theorem retained_supply_positive
    (supply numerator denominator : Nat) :
    0 < retainedSupply supply numerator denominator := by
  simp [retainedSupply]

/-- The runtime subtraction formula is exactly natural-number ceiling division. -/
theorem retained_supply_eq_ceil_div
    (supply numerator denominator : Nat)
    (hsupply : 0 < supply)
    (hnumerator : 0 < numerator)
    (hdenominator : 0 < denominator) :
    retainedSupply supply numerator denominator =
      (numerator * supply) ⌈/⌉ denominator := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hproduct : 0 < numerator * supply := Nat.mul_pos hnumerator hsupply
  have hreassociate :
      numerator * supply + denominator - 1 =
        (numerator * supply - 1) + denominator := by
    omega
  rw [hreassociate, Nat.add_div_right _ hdenominator]
  simp [retainedSupply, Nat.add_comm]

/-- A strict fraction `0 < p/q < 1` never retains more than live supply. -/
theorem retained_supply_le_supply
    (supply numerator denominator : Nat)
    (hsupply : 0 < supply)
    (hnumerator : 0 < numerator)
    (hfraction : numerator < denominator) :
    retainedSupply supply numerator denominator ≤ supply := by
  have hdenominator : 0 < denominator := lt_trans hnumerator hfraction
  have hproduct : numerator * supply < denominator * supply :=
    Nat.mul_lt_mul_of_pos_right hfraction hsupply
  have hnumerator_bound : numerator * supply - 1 < supply * denominator := by
    rw [Nat.mul_comm supply denominator]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hproduct
  have hdivision : (numerator * supply - 1) / denominator < supply :=
    (Nat.div_lt_iff_lt_mul hdenominator).2 hnumerator_bound
  simp only [retainedSupply]
  omega

/--
Burn capacity is positive exactly when live supply reaches the policy threshold
`q ≤ (q - p) * supply`.  Equivalently, the first live atom with headroom is
`ceil(q / (q - p))`.
-/
theorem burn_headroom_positive_iff_threshold
    (supply numerator denominator : Nat)
    (hsupply : 0 < supply)
    (hnumerator : 0 < numerator)
    (hfraction : numerator < denominator) :
    0 < burnHeadroom supply numerator denominator ↔
      denominator ≤ (denominator - numerator) * supply := by
  have hdenominator : 0 < denominator := lt_trans hnumerator hfraction
  have hgap_identity :
      (denominator - numerator) * supply + numerator * supply =
        denominator * supply := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hfraction)]
  have hstep_identity :
      denominator * (supply - 1) + denominator = denominator * supply := by
    have hpredecessor : supply - 1 + 1 = supply := by omega
    calc
      denominator * (supply - 1) + denominator =
          denominator * ((supply - 1) + 1) := by simp [Nat.mul_add]
      _ = denominator * supply := by rw [hpredecessor]
  constructor
  · intro hheadroom
    have hretained_lt :
        retainedSupply supply numerator denominator < supply := by
      simp only [burnHeadroom] at hheadroom
      omega
    have hceil_le :
        (numerator * supply) ⌈/⌉ denominator ≤ supply - 1 := by
      rw [← retained_supply_eq_ceil_div supply numerator denominator
        hsupply hnumerator hdenominator]
      omega
    have hproduct_le :
        numerator * supply ≤ denominator * (supply - 1) :=
      (ceilDiv_le_iff_le_mul hdenominator).1 hceil_le
    omega
  · intro hthreshold
    have hproduct_le :
        numerator * supply ≤ denominator * (supply - 1) := by
      omega
    have hceil_le :
        (numerator * supply) ⌈/⌉ denominator ≤ supply - 1 :=
      (ceilDiv_le_iff_le_mul hdenominator).2 hproduct_le
    have hretained_le :
        retainedSupply supply numerator denominator ≤ supply - 1 := by
      rw [retained_supply_eq_ceil_div supply numerator denominator
        hsupply hnumerator hdenominator]
      exact hceil_le
    simp only [burnHeadroom]
    omega

/-- The headroom guard leaves at least the declared retained amount. -/
theorem burn_at_or_below_headroom_preserves_retained
    (supply retained burn : Nat)
    (hretained : retained ≤ supply)
    (hburn : burn ≤ supply - retained) :
    retained ≤ supply - burn := by
  omega

/-- Every accepted finite burn leaves strictly positive integer supply. -/
theorem accepted_burn_preserves_positive_supply
    (supply numerator denominator burn : Nat)
    (hsupply : 0 < supply)
    (hnumerator : 0 < numerator)
    (hfraction : numerator < denominator)
    (hburn : burn ≤ burnHeadroom supply numerator denominator) :
    0 < supply - burn := by
  have hretained_le := retained_supply_le_supply
    supply numerator denominator hsupply hnumerator hfraction
  have hretained_after :
      retainedSupply supply numerator denominator ≤ supply - burn := by
    exact burn_at_or_below_headroom_preserves_retained
      supply (retainedSupply supply numerator denominator) burn
      hretained_le hburn
  exact lt_of_lt_of_le
    (retained_supply_positive supply numerator denominator)
    hretained_after

/-- Removing the headroom guard is observable whenever the burn still fits supply. -/
theorem burn_above_headroom_violates_retained
    (supply retained burn : Nat)
    (hretained : retained ≤ supply)
    (hburn_fits : burn ≤ supply)
    (hexceeds : supply - retained < burn) :
    supply - burn < retained := by
  omega

/-- Exact rescaling preserves a bucket's represented value by cross multiplication. -/
theorem exact_rescale_preserves_bucket_value
    (atoms scaleFactor oldScale : Nat) :
    (atoms * scaleFactor) * oldScale = atoms * (oldScale * scaleFactor) := by
  ac_rfl

/-- Scaling all buckets distributes over their conserved sum. -/
theorem exact_rescale_preserves_two_bucket_sum
    (leftAtoms rightAtoms scaleFactor : Nat) :
    (leftAtoms + rightAtoms) * scaleFactor =
      leftAtoms * scaleFactor + rightAtoms * scaleFactor := by
  exact Nat.add_mul leftAtoms rightAtoms scaleFactor

/-- The all-bucket list sum scales by the same exact factor. -/
theorem exact_rescale_preserves_bucket_sum
    (bucketAtoms : List Nat)
    (scaleFactor : Nat) :
    (bucketAtoms.map (fun atoms => atoms * scaleFactor)).sum =
      bucketAtoms.sum * scaleFactor := by
  induction bucketAtoms with
  | nil => simp
  | cons head tail ih => simp [ih, Nat.add_mul]

/-- The real-valued Zeno ideal remains positive at every finite index. -/
theorem finite_geometric_supply_positive
    (initialSupply retainedRatio : Real)
    (epoch : Nat)
    (hinitial : 0 < initialSupply)
    (hratio : 0 < retainedRatio) :
    0 < initialSupply * retainedRatio ^ epoch := by
  exact mul_pos hinitial (pow_pos hratio epoch)

end ZDEXHyperdeflationV1
end Proofs
