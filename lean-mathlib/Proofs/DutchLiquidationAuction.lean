import Mathlib.Tactic
import Proofs.PerpGameTheory

/-!
# Dutch-Auction Liquidation

`PerpGameTheory` Tier 6 proves the fixed-penalty keeper race dissipates
essentially the entire penalty into gas (`race_dissipation_bounds`): with
prize `R` and gas `c`, equilibrium aggregate spend lands in `(R − c, R]`,
and the waste grows linearly in `R`.

This file analyzes the standard remedy: a **Dutch (ascending) penalty
ramp**.  Instead of a fixed penalty, the claimable penalty starts at zero
when the account crosses below maintenance and rises by `step` per epoch.
A keeper with cost `c` first finds liquidation profitable at the ramp's
first crossing of `c`, and:

* the winner's rent is below one ramp step (`dutch_rent_lt_step`) — the
  account pays ≈ the marginal keeper's cost instead of a fixed worst-case
  penalty;
* with `step ≤ c`, the race itself collapses: the unique equilibrium
  attempter count at the crossing epoch is ONE (`dutch_collapses_race`,
  via the Tier-6 `RaceEquilibriumCount`), so there is no gas-burning
  competition left to dissipate the prize;
* the ramp composes with the funded-liquidation cap: the (FUNDED-LIQ)
  inequality is monotone in the penalty (`funded_monotone_in_penalty`),
  so capping the ramp at a funded `penalty_max` keeps every intermediate
  ramp value funded.

Model boundary: epochs are discrete, keepers are myopic profit-maximizers
with a common known cost floor `c` (the cheapest keeper), and exactly one
liquidation opportunity is modeled.  Heterogeneous private costs change
the winner's identity, not the rent bound.
-/

namespace Proofs
namespace DutchLiquidationAuction

open PerpGameTheory

/-- Penalty ramp: claimable penalty after `t` epochs below maintenance. -/
def ramp (step t : ℕ) : ℕ := step * t

/-- First epoch at which the ramp reaches the keeper cost `c`:
    `⌈c / step⌉` in ceiling arithmetic. -/
def firstCross (step c : ℕ) : ℕ := (c + step - 1) / step

/-- The ramp covers the keeper cost at the first crossing. -/
theorem firstCross_crosses (step c : ℕ) (hstep : 0 < step) :
    c ≤ ramp step (firstCross step c) := by
  unfold ramp firstCross
  have hdm : step * ((c + step - 1) / step) + (c + step - 1) % step
      = c + step - 1 := Nat.div_add_mod _ _
  have hmod : (c + step - 1) % step < step := Nat.mod_lt _ hstep
  generalize hA : step * ((c + step - 1) / step) = A at *
  omega

/-- Before the first crossing the ramp is strictly below the keeper cost:
    no rational keeper enters early. -/
theorem firstCross_minimal (step c t : ℕ) (hstep : 0 < step)
    (ht : t < firstCross step c) :
    ramp step t < c := by
  unfold ramp
  unfold firstCross at ht
  obtain ⟨q', hq'⟩ : ∃ q', (c + step - 1) / step = q' + 1 :=
    ⟨(c + step - 1) / step - 1, by omega⟩
  have hdm : step * ((c + step - 1) / step) + (c + step - 1) % step
      = c + step - 1 := Nat.div_add_mod _ _
  rw [hq'] at hdm ht
  have hmul : step * t ≤ step * q' := Nat.mul_le_mul_left step (by omega)
  have hexp : step * (q' + 1) = step * q' + step := by ring
  rw [hexp] at hdm
  generalize hB : step * q' = B at *
  omega

/-- **Rent bound**: the winner's net profit at the first crossing is below
    one ramp step.  The liquidated account pays the marginal keeper cost
    plus at most `step − 1`, instead of a fixed worst-case penalty. -/
theorem dutch_rent_lt_step (step c : ℕ) (hstep : 0 < step) :
    ramp step (firstCross step c) - c < step := by
  unfold ramp firstCross
  have hdm : step * ((c + step - 1) / step) + (c + step - 1) % step
      = c + step - 1 := Nat.div_add_mod _ _
  generalize hA : step * ((c + step - 1) / step) = A at *
  omega

/-- **The race collapses.**  With `step ≤ c`, the prize at the first
    crossing satisfies `c ≤ R* < 2c`, so in the Tier-6 race model the
    unique equilibrium attempter count at that epoch is ONE: a second
    entrant would be strictly unprofitable.  The Dutch ramp removes the
    rent-dissipating competition entirely. -/
theorem dutch_collapses_race (step c : ℕ) (hstep : 0 < step)
    (hsc : step ≤ c) :
    RaceEquilibriumCount ((ramp step (firstCross step c) : ℕ) : ℚ) (c : ℚ) 1 := by
  have hlow : c ≤ ramp step (firstCross step c) := firstCross_crosses step c hstep
  have hrent : ramp step (firstCross step c) - c < step := dutch_rent_lt_step step c hstep
  have hhigh : ramp step (firstCross step c) < 2 * c := by omega
  constructor
  · intro _
    have hQ : (c : ℚ) ≤ ((ramp step (firstCross step c) : ℕ) : ℚ) := by
      exact_mod_cast hlow
    simp only [raceAttemptPayoff, Nat.cast_one]
    rw [div_one]
    linarith
  · have hQ : ((ramp step (firstCross step c) : ℕ) : ℚ) < 2 * c := by
      exact_mod_cast hhigh
    simp only [raceAttemptPayoff]
    have h2 : ((1 + 1 : ℕ) : ℚ) = 2 := by norm_num
    rw [h2]
    have : ((ramp step (firstCross step c) : ℕ) : ℚ) / 2 < c := by linarith
    linarith

/-- The funded-liquidation inequality
    `penalty · (10⁴ + m) ≤ 10⁴ · (maint − m)`
    (`PerpEpochSafety.liquidation_penalty_funded_after_bounded_move`) is
    monotone in the penalty: a ramp capped at a funded `penalty_max` is
    funded at every intermediate value. -/
theorem funded_monotone_in_penalty (penalty penalty_max m maint : ℚ)
    (hm : 0 ≤ 10000 + m)
    (hle : penalty ≤ penalty_max)
    (hcap : penalty_max * (10000 + m) ≤ 10000 * (maint - m)) :
    penalty * (10000 + m) ≤ 10000 * (maint - m) := by
  have h := mul_le_mul_of_nonneg_right hle hm
  linarith

/-- Non-vacuity: step 3, cost 10.  First crossing at epoch 4, prize 12,
    rent 2 < 3, and the equilibrium attempter count at the crossing is 1
    (a second entrant nets `12/2 − 10 < 0`). -/
theorem witness_dutch :
    firstCross 3 10 = 4 ∧
    ramp 3 (firstCross 3 10) = 12 ∧
    ramp 3 (firstCross 3 10) - 10 < 3 ∧
    RaceEquilibriumCount ((12 : ℕ) : ℚ) (10 : ℚ) 1 := by
  constructor
  · norm_num [firstCross]
  constructor
  · norm_num [ramp, firstCross]
  constructor
  · norm_num [ramp, firstCross]
  constructor
  · intro _
    norm_num [raceAttemptPayoff]
  · norm_num [raceAttemptPayoff]

end DutchLiquidationAuction
end Proofs
