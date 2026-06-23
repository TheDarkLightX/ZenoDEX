import Mathlib.Tactic

/-!
# Pokayoke Impact Gate

This file formalizes only the impact-only subdomain of the exact-in Pokayoke
advisory gate. It does **not** claim anything about the full mixed decision
surface with MEV or slippage-trigger reasons.

The promoted claim is narrow:

- if impact `< 1%`, the impact-only action is `allow`
- if impact is in `[1%, 5%)`, the impact-only action is `confirm`
- if impact is `>= 5%`, the impact-only action is `typedConfirm`
- the induced severity order is monotone in `price_impact_bps`

This matches the explicit threshold posture in
`src/core/pokayoke_swap_guardrails.py` once all non-impact triggers are absent.
-/

namespace Proofs
namespace PokayokeImpactGate

inductive ImpactAction where
  | allow
  | confirm
  | typedConfirm
deriving DecidableEq, Repr

def severity : ImpactAction → Nat
  | .allow => 0
  | .confirm => 1
  | .typedConfirm => 2

def impactOnlyAction (impactBps : Nat) : ImpactAction :=
  if 500 ≤ impactBps then
    .typedConfirm
  else if 100 ≤ impactBps then
    .confirm
  else
    .allow

theorem impactOnlyAction_of_lt_100 (impactBps : Nat) (h : impactBps < 100) :
    impactOnlyAction impactBps = .allow := by
  have h500 : ¬ 500 ≤ impactBps := by omega
  have h100 : ¬ 100 ≤ impactBps := by omega
  simp [impactOnlyAction, h500, h100]

theorem impactOnlyAction_of_band (impactBps : Nat)
    (h100 : 100 ≤ impactBps) (h500 : impactBps < 500) :
    impactOnlyAction impactBps = .confirm := by
  have h500' : ¬ 500 ≤ impactBps := by omega
  simp [impactOnlyAction, h500', h100]

theorem impactOnlyAction_of_ge_500 (impactBps : Nat) (h : 500 ≤ impactBps) :
    impactOnlyAction impactBps = .typedConfirm := by
  simp [impactOnlyAction, h]

theorem severity_impactOnlyAction_monotone (a b : Nat) (hab : a ≤ b) :
    severity (impactOnlyAction a) ≤ severity (impactOnlyAction b) := by
  by_cases hb100 : b < 100
  · have ha100 : a < 100 := by omega
    simp [impactOnlyAction_of_lt_100, ha100, hb100, severity]
  · have hb100' : 100 ≤ b := by omega
    by_cases hb500 : b < 500
    · by_cases ha100 : a < 100
      · simp [impactOnlyAction_of_lt_100, impactOnlyAction_of_band, ha100, hb100', hb500, severity]
      · have ha100' : 100 ≤ a := by omega
        have ha500 : a < 500 := by omega
        simp [impactOnlyAction_of_band, ha100', ha500, hb100', hb500, severity]
    · have hb500' : 500 ≤ b := by omega
      by_cases ha100 : a < 100
      · simp [impactOnlyAction_of_lt_100, impactOnlyAction_of_ge_500, ha100, hb500', severity]
      · have ha100' : 100 ≤ a := by omega
        by_cases ha500 : a < 500
        · simp [impactOnlyAction_of_band, impactOnlyAction_of_ge_500, ha100', ha500, hb500', severity]
        · have ha500' : 500 ≤ a := by omega
          simp [impactOnlyAction_of_ge_500, ha500', hb500', severity]

theorem impactOnlyAction_eq_allow_iff (impactBps : Nat) :
    impactOnlyAction impactBps = .allow ↔ impactBps < 100 := by
  constructor
  · intro h
    by_cases h100 : impactBps < 100
    · exact h100
    · have h100' : 100 ≤ impactBps := by omega
      by_cases h500 : impactBps < 500
      · rw [impactOnlyAction_of_band impactBps h100' h500] at h
        cases h
      · have h500' : 500 ≤ impactBps := by omega
        rw [impactOnlyAction_of_ge_500 impactBps h500'] at h
        cases h
  · intro h
    exact impactOnlyAction_of_lt_100 impactBps h

theorem impactOnlyAction_eq_confirm_iff (impactBps : Nat) :
    impactOnlyAction impactBps = .confirm ↔ 100 ≤ impactBps ∧ impactBps < 500 := by
  constructor
  · intro h
    constructor
    · by_cases h100 : 100 ≤ impactBps
      · exact h100
      · have hlt100 : impactBps < 100 := by omega
        rw [impactOnlyAction_of_lt_100 impactBps hlt100] at h
        cases h
    · by_cases h500 : impactBps < 500
      · exact h500
      · have h500' : 500 ≤ impactBps := by omega
        rw [impactOnlyAction_of_ge_500 impactBps h500'] at h
        cases h
  · rintro ⟨h100, h500⟩
    exact impactOnlyAction_of_band impactBps h100 h500

theorem impactOnlyAction_eq_typedConfirm_iff (impactBps : Nat) :
    impactOnlyAction impactBps = .typedConfirm ↔ 500 ≤ impactBps := by
  constructor
  · intro h
    by_cases h500 : 500 ≤ impactBps
    · exact h500
    · have hlt500 : impactBps < 500 := by omega
      by_cases h100 : 100 ≤ impactBps
      · rw [impactOnlyAction_of_band impactBps h100 hlt500] at h
        cases h
      · have hlt100 : impactBps < 100 := by omega
        rw [impactOnlyAction_of_lt_100 impactBps hlt100] at h
        cases h
  · intro h
    exact impactOnlyAction_of_ge_500 impactBps h

theorem witness_impactOnlyAction_boundaries :
    impactOnlyAction 99 = .allow ∧
    impactOnlyAction 100 = .confirm ∧
    impactOnlyAction 499 = .confirm ∧
    impactOnlyAction 500 = .typedConfirm := by
  native_decide

end PokayokeImpactGate
end Proofs
