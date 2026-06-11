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

/-! ## Strict Dominance and Equilibrium Uniqueness

Weak dominance certifies an equilibrium but says nothing about other
equilibria, so a mechanism analyzed with `DominantProfile` alone has a
*supported* outcome, not a *predicted* one.  Strict dominance closes that
gap: a strictly-dominant profile is the **unique** Nash equilibrium
(`strict_dominant_unique_nash`), pinning the mechanism's predicted outcome.
-/

/-- Strategy s is strictly dominant for player i: strictly better than every
    alternative `s' ≠ s`, regardless of opponents' strategies. -/
@[reducible]
def StrictlyDominantStrategy {n m : Nat} (g : Game n m) (i : Fin n) (s : Fin m) : Prop :=
  ∀ σ : Fin n → Fin m, ∀ s' : Fin m, s' ≠ s →
    g.payoff (deviate σ i s') i < g.payoff (deviate σ i s) i

/-- A strictly-dominant profile: every player's strategy is strictly dominant. -/
@[reducible]
def StrictDominantProfile {n m : Nat} (g : Game n m) (σ : Fin n → Fin m) : Prop :=
  ∀ i : Fin n, StrictlyDominantStrategy g i (σ i)

/-- Strict dominance implies weak dominance. -/
theorem strict_dominant_implies_dominant {n m : Nat} (g : Game n m) (i : Fin n)
    (s : Fin m) (h : StrictlyDominantStrategy g i s) : DominantStrategy g i s := by
  intro σ s'
  by_cases hs : s' = s
  · subst hs
    exact le_rfl
  · exact le_of_lt (h σ s' hs)

/-- A strictly-dominant profile is a Nash equilibrium (existence half). -/
theorem strict_dominant_profile_nash {n m : Nat} (g : Game n m) (σ : Fin n → Fin m)
    (hdom : StrictDominantProfile g σ) : NashEq g σ :=
  dominant_implies_nash g σ fun i => strict_dominant_implies_dominant g i (σ i) (hdom i)

/-- **Uniqueness**: every Nash equilibrium coincides with a strictly-dominant
    profile.  Proof: if `τ i ≠ σ i`, strict dominance at profile `τ` gives
    `payoff τ i < payoff (deviate τ i (σ i)) i`, contradicting the Nash
    condition for `τ` at deviation `σ i`. -/
theorem strict_dominant_unique_nash {n m : Nat} (g : Game n m)
    (σ τ : Fin n → Fin m) (hdom : StrictDominantProfile g σ) (hτ : NashEq g τ) :
    τ = σ := by
  funext i
  by_contra hne
  have hstrict := hdom i τ (τ i) hne
  rw [deviate_self] at hstrict
  have hnash := hτ i (σ i)
  exact absurd (lt_of_lt_of_le hstrict hnash) (lt_irrefl _)

/-- Full characterization: under a strictly-dominant profile `σ`, a profile is
    a Nash equilibrium iff it equals `σ`.  The mechanism's predicted outcome
    is unique. -/
theorem nash_iff_eq_of_strict_dominant {n m : Nat} (g : Game n m)
    (σ : Fin n → Fin m) (hdom : StrictDominantProfile g σ) (τ : Fin n → Fin m) :
    NashEq g τ ↔ τ = σ := by
  constructor
  · exact strict_dominant_unique_nash g σ τ hdom
  · rintro rfl
    exact strict_dominant_profile_nash _ _ hdom

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

/-- Non-vacuity for strict dominance: in the Prisoner's Dilemma,
    (Defect, Defect) is a strictly-dominant profile.  By
    `nash_iff_eq_of_strict_dominant` it is therefore the UNIQUE Nash
    equilibrium of `pdGame` — a strictly stronger conclusion than
    `witness_two_player_game`, which only certifies it as *a* Nash
    equilibrium. -/
theorem witness_pd_strict_dominance :
    StrictDominantProfile pdGame (fun _ => 1) := by
  native_decide

end PerpMechanismDesign

end Proofs
