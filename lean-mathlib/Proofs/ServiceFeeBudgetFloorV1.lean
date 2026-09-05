import Std

/-!
Exact natural-number fee participation for one frozen aggregate entitlement.
This arithmetic result does not authenticate eligibility, establish service
delivery, select a policy rate, or prove general trading incentive compatibility.
-/

namespace ServiceFeeBudgetFloorV1

/-- A fixed rate at most one cannot increase its floored payout by more than W. -/
theorem floor_growth_le (F W l D : Nat) (hD : 0 < D) (hl : l ≤ D) :
    l * (F + W) / D ≤ l * F / D + W := by
  calc
    l * (F + W) / D = (l * F + l * W) / D := by rw [Nat.mul_add]
    _ ≤ (l * F + D * W) / D :=
      Nat.div_le_div_right (Nat.add_le_add_left (Nat.mul_le_mul_right W hl) (l * F))
    _ = l * F / D + W := Nat.add_mul_div_left (l * F) W hD

/-- Natural subtraction measures incremental payout under a frozen rate. -/
theorem floor_increment_le (F W l D : Nat) (hD : 0 < D) (hl : l ≤ D) :
    l * (F + W) / D - l * F / D ≤ W := by
  have h := floor_growth_le F W l D hD hl
  omega

/-- A fixed aggregate cap preserves the incremental bound. -/
theorem capped_increment_le (F W l D C : Nat) (hD : 0 < D) (hl : l ≤ D) :
    min C (l * (F + W) / D) - min C (l * F / D) ≤ W := by
  have h := floor_growth_le F W l D hD hl
  omega

/-- The increment above cannot hide a payout decrease behind Nat subtraction. -/
theorem capped_monotone (F W l D C : Nat) :
    min C (l * F / D) ≤ min C (l * (F + W) / D) := by
  have hmul : l * F ≤ l * (F + W) := Nat.mul_le_mul_left l (by omega)
  have hdiv : l * F / D ≤ l * (F + W) / D := Nat.div_le_div_right hmul
  omega

/-- Live positive payout and a tight boundary demonstrate non-vacuous premises. -/
example : (min 100 (3 * 30 / 10) : Nat) - min 100 (3 * 20 / 10) = 3 := by decide
example : (7 * (20 + 1) / 7 : Nat) - 7 * 20 / 7 = 1 := by decide

/-- Independently rounded entitlements can also release a previously owned atom. -/
example : (2 * (2 / 2) - 2 * (1 / 2) : Nat) > 1 := by decide

end ServiceFeeBudgetFloorV1
