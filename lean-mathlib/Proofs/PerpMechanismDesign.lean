import Mathlib.Tactic

/-!
# Mechanism Design Foundations

Minimal game-theory definitions for perpetual protocol verification.
Since no Mathlib game theory library exists, we build custom definitions
following the `SettlementAlgebra.lean` pattern.

## Definitions

- `Game n m`: n-player, m-strategy normal-form game with integer payoffs
- `NashEq`: no player can improve by unilateral deviation
- `DominantStrategy`: strategy is best regardless of opponents' choices
- `IncentiveCompatible`: honest behavior ≥ deviant behavior
- `IndividuallyRational`: participation payoff ≥ reservation value
- `BudgetBalanced`: sum of mechanism payments ≥ 0

## Key Results

- `dominant_implies_nash`: dominant strategy profile ⇒ Nash equilibrium
- `ic_iff_dominant`: DSIC ↔ dominant strategy (definitional biconditional)
- `ic_from_dominant`: dominant strategy → incentive compatibility (forward direction)
- `witness_two_player_game`: non-vacuity via concrete 2×2 game (`native_decide`)
-/

namespace Proofs

namespace PerpMechanismDesign

/-! ## Core Definitions -/

/-- An n-player, m-strategy normal-form game with integer payoffs. -/
structure Game (n m : Nat) where
  payoff : (Fin n → Fin m) → Fin n → ℤ

/-- Replace player i's strategy in profile σ with s (alias for `Function.update`). -/
@[reducible]
def deviate {n m : Nat} (σ : Fin n → Fin m) (i : Fin n) (s : Fin m) : Fin n → Fin m :=
  Function.update σ i s

/-- Deviating to one's own strategy is a no-op. -/
theorem deviate_self {n m : Nat} (σ : Fin n → Fin m) (i : Fin n) :
    deviate σ i (σ i) = σ :=
  Function.update_eq_self i σ

/-- A profile σ is a Nash equilibrium: no player can improve by unilateral deviation. -/
@[reducible]
def NashEq {n m : Nat} (g : Game n m) (σ : Fin n → Fin m) : Prop :=
  ∀ i : Fin n, ∀ s : Fin m, g.payoff (deviate σ i s) i ≤ g.payoff σ i

/-- Strategy s is dominant for player i: it weakly dominates all alternatives
    regardless of opponents' strategies. -/
@[reducible]
def DominantStrategy {n m : Nat} (g : Game n m) (i : Fin n) (s : Fin m) : Prop :=
  ∀ σ : Fin n → Fin m, ∀ s' : Fin m,
    g.payoff (deviate σ i s') i ≤ g.payoff (deviate σ i s) i

/-- A profile σ is a dominant-strategy profile: each player plays a dominant strategy. -/
@[reducible]
def DominantProfile {n m : Nat} (g : Game n m) (σ : Fin n → Fin m) : Prop :=
  ∀ i : Fin n, DominantStrategy g i (σ i)

/-- A mechanism is incentive-compatible for player i with honest strategy h:
    reporting honestly is weakly best regardless of opponents. -/
@[reducible]
def IncentiveCompatible {n m : Nat} (g : Game n m) (i : Fin n) (h : Fin m) : Prop :=
  ∀ σ : Fin n → Fin m, ∀ s : Fin m,
    g.payoff (deviate σ i s) i ≤ g.payoff (deviate σ i h) i

/-- Participation by player i is individually rational: payoff ≥ reservation value r. -/
@[reducible]
def IndividuallyRational {n m : Nat} (g : Game n m) (σ : Fin n → Fin m)
    (i : Fin n) (r : ℤ) : Prop :=
  r ≤ g.payoff σ i

/-- A mechanism is (weakly) budget-balanced at profile σ: total payoffs are non-negative.
    Specialized to 2-player games to avoid BigOperators import. -/
@[reducible]
def BudgetBalanced₂ {m : Nat} (g : Game 2 m) (σ : Fin 2 → Fin m) : Prop :=
  (0 : ℤ) ≤ g.payoff σ 0 + g.payoff σ 1

/-! ## Core Theorems -/

/-- A dominant-strategy profile is a Nash equilibrium.
    Proof: DominantStrategy gives `payoff(deviate σ i s) i ≤ payoff(deviate σ i (σ i)) i`
    for all profiles. Since `deviate σ i (σ i) = σ`, this is the Nash condition. -/
theorem dominant_implies_nash {n m : Nat} (g : Game n m) (σ : Fin n → Fin m)
    (hdom : DominantProfile g σ) : NashEq g σ := by
  intro i s
  have h := hdom i σ s
  rw [deviate_self] at h
  exact h

/-- `IncentiveCompatible g i h` and `DominantStrategy g i h` are definitionally equal:
    both state that `h` maximizes player `i`'s payoff under any opponent profile.
    This biconditional records the equivalence. -/
theorem ic_iff_dominant {n m : Nat} (g : Game n m) (i : Fin n) (h : Fin m) :
    IncentiveCompatible g i h ↔ DominantStrategy g i h := Iff.rfl

/-- Forward direction of `ic_iff_dominant`: dominant strategy implies
    incentive compatibility. Convenience wrapper for downstream use. -/
theorem ic_from_dominant {n m : Nat} (g : Game n m) (i : Fin n) (h : Fin m)
    (hdom : DominantStrategy g i h) : IncentiveCompatible g i h :=
  hdom

/-! ## Non-Vacuity Witness

Concrete 2-player, 2-strategy Prisoner's Dilemma where strategy 1 (defect) is
dominant for both players, making (1,1) a dominant-strategy Nash equilibrium.

Payoff matrix (row = player 0, col = player 1):
```
         C(0)    D(1)
  C(0):  (3,3)   (0,5)
  D(1):  (5,0)   (1,1)
```
-/

/-- Prisoner's Dilemma: a concrete 2×2 game. -/
def pdGame : Game 2 2 where
  payoff σ i :=
    if σ 0 = 0 then
      if σ 1 = 0 then 3
      else if i = 0 then 0 else 5
    else
      if σ 1 = 0 then
        if i = 0 then 5 else 0
      else 1

/-- Non-vacuity: (Defect, Defect) is a dominant-strategy Nash equilibrium
    in the Prisoner's Dilemma, both players have non-negative payoff,
    and the game is budget-balanced. -/
theorem witness_two_player_game :
    let σ : Fin 2 → Fin 2 := fun _ => 1
    NashEq pdGame σ ∧
    DominantProfile pdGame σ ∧
    IndividuallyRational pdGame σ (0 : Fin 2) (0 : ℤ) ∧
    IndividuallyRational pdGame σ (1 : Fin 2) (0 : ℤ) ∧
    BudgetBalanced₂ pdGame σ := by
  native_decide

end PerpMechanismDesign

end Proofs
