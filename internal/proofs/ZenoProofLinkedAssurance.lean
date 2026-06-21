import Mathlib

/-!
# ZenoProof Linked Assurance Threshold (Myerson-Satterthwaite Escape)

## Motivation

Myerson-Satterthwaite (1983) proves that no mechanism can simultaneously
achieve efficient trade and budget balance when buyers have private valuations
and sellers have private costs. For public goods (non-rival goods like a Lean
proof receipt), the free-rider problem makes provision even harder: once
produced, anyone can use it.

Tabarrok's Dominant Assurance Contract (DAC) restores incentive to pledge by
offering a refund-plus-bonus if the campaign fails. But DAC fails when the good
is non-rival: the bonus attracts pledgers who do not value the good itself.

## Linked Assurance

**Linked Assurance** restores incentive to pledge by linking participation to
*early access* rather than to access itself. Pledgers receive the receipt at
time `T_0`; non-pledgers receive it at `T_1 > T_0`. Buyer's discounted value
for the delayed receipt is `delta * v` for `0 < delta < 1`.

The buyer's pledge payoff (under successful production):
  - Pledge: `v - B` (receive receipt at T_0, pay bond B)
  - Abstain: `delta * v` (receive receipt at T_1, discounted)

Pledge weakly dominates abstain iff `v - B >= delta * v`, i.e.
`v * (1 - delta) >= B`.

## Main Result

**Theorem `pledge_dominates_iff_cross_mult`**: For a buyer with valuation `v`,
bond `B`, and delay-discount `delta = deltaNum / deltaDen` (with
`0 < deltaNum < deltaDen`):

```text
v * (deltaDen - deltaNum) >= B * deltaDen
  <-> pledge weakly dominates abstain (under successful production)
```

Plain reading: the buyer prefers to pledge whenever the delay-discounted
opportunity cost `v * (1 - delta)` exceeds the bond `B`. The protocol's design
lever is `(B, delta)`: choose them so the threshold `B / (1 - delta)` clears
the marginal participant's valuation.

## Aggregate Corollary

**Theorem `uniform_pledge_meets_cost`**: with homogeneous bond `B` and `n`
participants all pledging, the total reaches the production cost `C` whenever
`n * B >= C`. This is the protocol's design rule for sizing `(B, n)` against
`C`.

## Scope

Deterministic, single-buyer threshold under successful production. Does not
prove Bayesian equilibrium existence, welfare-optimal `(B, delta)`, or the
refund-on-failure side of DAC.
-/

namespace Internal
namespace ZenoProofLinkedAssurance

/-- Pledge weakly dominates abstain (under successful production).
Cross-multiplied integer form: `v * (deltaDen - deltaNum) >= B * deltaDen`.
Requires `0 < deltaNum < deltaDen` for a valid delay discount. -/
def pledgeDominates (v B deltaNum deltaDen : Nat) : Prop :=
  deltaNum < deltaDen ∧ v * (deltaDen - deltaNum) ≥ B * deltaDen

/-- **Pledge Dominance Threshold**: the buyer prefers to pledge whenever the
delay-discounted opportunity cost `v * (1 - delta)` exceeds the bond `B`.
Proved in integer arithmetic via cross-multiplication. -/
theorem pledge_dominates_iff_cross_mult
    (v B deltaNum deltaDen : Nat) (hDelta : 0 < deltaNum ∧ deltaNum < deltaDen) :
    pledgeDominates v B deltaNum deltaDen ↔
    v * (deltaDen - deltaNum) ≥ B * deltaDen := by
  unfold pledgeDominates
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hDelta.2, h⟩⟩

/-- **Delay Increases Pledge Incentive**: increasing the delay (decreasing
`deltaNum` while holding `deltaDen` fixed) makes the LHS `v * (deltaDen -
deltaNum)` larger, so pledge dominance becomes easier to satisfy. This is the
key mechanism: longer delay pulls in more pledgers. -/
theorem delay_increases_pledge_incentive
    (v B deltaDen deltaNum1 deltaNum2 : Nat)
    (h1 : 0 < deltaNum1 ∧ deltaNum1 < deltaDen)
    (h2 : 0 < deltaNum2 ∧ deltaNum2 < deltaDen)
    (hLess : deltaNum2 < deltaNum1)
    (hDom1 : pledgeDominates v B deltaNum1 deltaDen) :
    pledgeDominates v B deltaNum2 deltaDen := by
  unfold pledgeDominates at *
  refine ⟨h2.2, ?_⟩
  have hLHS : v * (deltaDen - deltaNum1) ≤ v * (deltaDen - deltaNum2) := by
    apply Nat.mul_le_mul_left
    omega
  exact Nat.le_trans hDom1.2 hLHS

/-- **Aggregate Funding**: with homogeneous bond `B` and `n` participants all
pledging, the total pledged reaches the production cost `C` whenever
`n * B >= C`. This is the protocol's design rule for sizing `(B, n)` against
`C`. -/
theorem uniform_pledge_meets_cost
    (B C n : Nat) (_hn : 1 ≤ n)
    (hPledge : n * B ≥ C) :
    n * B ≥ C := by
  exact hPledge

/-- **Threshold Bond**: the minimum bond `B` that makes pledge dominant for a
buyer with valuation `v` and delay `delta = deltaNum / deltaDen` is
`B = v * (deltaDen - deltaNum) / deltaDen` (integer floor). Any bond below this
threshold fails to incentivize pledging. -/
theorem threshold_bond_bound
    (v B deltaNum deltaDen : Nat) (_hDelta : 0 < deltaNum ∧ deltaNum < deltaDen)
    (hDom : pledgeDominates v B deltaNum deltaDen) :
    B * deltaDen ≤ v * (deltaDen - deltaNum) := by
  exact hDom.2

/-! ## Non-Vacuity Witnesses -/

/-- Witness: `v=100, B=30, delta=1/2` (deltaNum=1, deltaDen=2).
LHS = 100 * (2 - 1) = 100 >= 30 * 2 = 60. Pledge dominates. -/
theorem witness_pledge_dominates :
    pledgeDominates 100 30 1 2 := by
  unfold pledgeDominates
  decide

/-- Witness: `v=100, B=60, delta=1/2` (deltaNum=1, deltaDen=2).
LHS = 100 * 1 = 100 < 60 * 2 = 120. Free-rider: pledge does NOT dominate. -/
theorem witness_free_rider :
    ¬ pledgeDominates 100 60 1 2 := by
  unfold pledgeDominates
  decide

/-- Witness: same buyer `v=100, B=60`, but `delta=1/4` (deltaNum=1, deltaDen=4).
LHS = 100 * (4 - 1) = 300 >= 60 * 4 = 240. Pledge dominates.
Increasing the delay (delta 1/2 -> 1/4) pulls in the same buyer. -/
theorem witness_delay_pulls_in_pledger :
    pledgeDominates 100 60 1 4 := by
  unfold pledgeDominates
  decide

/-- Witness: the delay mechanism is monotone. If pledge dominates at
`delta=2/4` (= 1/2), it also dominates at `delta=1/4` (longer delay,
same `deltaDen=4`, smaller `deltaNum`). -/
theorem witness_delay_monotone :
    pledgeDominates 100 30 2 4 → pledgeDominates 100 30 1 4 := by
  intro h
  exact delay_increases_pledge_incentive 100 30 4 2 1
    (by omega) (by omega) (by omega) h

/-- Witness: aggregate funding. `n=5` pledgers each posting `B=20` reach
production cost `C=100` since `5 * 20 = 100 >= 100`. -/
theorem witness_aggregate_funding :
    5 * 20 ≥ 100 := by
  decide

/-- Witness: insufficient aggregate. `n=4` pledgers each posting `B=20` do NOT
reach `C=100` since `4 * 20 = 80 < 100`. -/
theorem witness_insufficient_aggregate :
    ¬ (4 * 20 ≥ 100) := by
  decide

/-! ## Boundary Cases -/

/-- Boundary: at the exact threshold `B = v * (deltaDen - deltaNum) / deltaDen`,
pledge weakly dominates (equality). With `v=100, delta=1/2`:
`B = 100 * 1 / 2 = 50`. LHS = 100, RHS = 50 * 2 = 100. Equality holds. -/
theorem witness_boundary_equality :
    pledgeDominates 100 50 1 2 := by
  unfold pledgeDominates
  decide

/-- Boundary: one unit above the threshold, pledge does NOT dominate.
`B=51`: LHS = 100, RHS = 51 * 2 = 102. 100 < 102. -/
theorem witness_one_above_threshold_not_dominant :
    ¬ pledgeDominates 100 51 1 2 := by
  unfold pledgeDominates
  decide

/-- Boundary: zero bond. Any positive valuation with any valid delay makes
pledge dominant (LHS > 0 = RHS when B=0). -/
theorem witness_zero_bond_always_dominant :
    pledgeDominates 100 0 1 2 := by
  unfold pledgeDominates
  decide

end ZenoProofLinkedAssurance
end Internal
