import Mathlib.Tactic

/-!
# Commit-Reveal Incentive-Compatibility Boundary

A binding commitment proves that the value revealed after the deadline equals
the value committed before the deadline.  It does not prove that the committed
value equals the user's private type or truthful preference.

This distinction matters for ZenoDEX.  A theorem with the hypothesis

`reported = trueValue`

already assumes away the strategic deviation that strategyproofness is supposed
to compare.  Such a theorem can still certify post-commit non-adaptivity, but it
must not be promoted as truthful incentive compatibility over the pre-commit
report space.

This file formalizes the boundary and gives a constructive counterexample:
binding commit-reveal can hold while a pre-commit misreport is strictly more
profitable than the truthful report.
-/

namespace TauSwap
namespace MechanismDesign
namespace CommitRevealBoundary

/-- A reveal is binding when it must equal the previously committed report. -/
def RevealConsistent {Report : Type}
    (committed revealed : Report) : Prop :=
  revealed = committed

/-- Truthful strategyproofness at one private type: no report has greater
utility than the truthful report. -/
def TruthfulAt {Report : Type}
    (utility : Report → ℤ)
    (truthfulReport : Report) : Prop :=
  ∀ report, utility report ≤ utility truthfulReport

/-- Binding gives post-commit non-adaptivity: two accepted reveals for the same
commitment are identical and therefore induce the same deterministic outcome. -/
theorem binding_implies_post_commit_nonadaptivity
    {Report Outcome : Type}
    (outcome : Report → Outcome)
    {committed reveal₁ reveal₂ : Report}
    (hReveal₁ : RevealConsistent committed reveal₁)
    (hReveal₂ : RevealConsistent committed reveal₂) :
    outcome reveal₁ = outcome reveal₂ := by
  unfold RevealConsistent at hReveal₁ hReveal₂
  rw [hReveal₁, hReveal₂]

/-- Assuming the contested report equals the truthful report makes the
no-profitable-deviation inequality reflexive.  This is a valid equality fact,
but not a proof that users optimally choose the truthful report before commit. -/
theorem report_eq_truth_makes_deviation_reflexive
    {Report : Type}
    (utility : Report → ℤ)
    {truthfulReport reported : Report}
    (hEq : reported = truthfulReport) :
    ¬ utility reported > utility truthfulReport := by
  subst reported
  omega

/-- A tiny utility model with a profitable pre-commit report `2` when the
designated truthful report is `1`. -/
def counterexampleUtility (report : ℤ) : ℤ :=
  if report = 2 then 1 else 0

theorem counterexample_profitable_precommit_misreport :
    counterexampleUtility 1 < counterexampleUtility 2 := by
  norm_num [counterexampleUtility]

/-- Binding and truthful strategyproofness are logically distinct.

The user commits to `2` and reveals `2`, so binding is satisfied.  Nevertheless,
report `2` gives strictly greater utility than the designated truthful report
`1`, so truthful strategyproofness fails. -/
theorem binding_does_not_imply_truthful_strategyproofness :
    RevealConsistent (2 : ℤ) 2 ∧
      ¬ TruthfulAt counterexampleUtility (1 : ℤ) := by
  constructor
  · rfl
  · intro hTruthful
    have hReportTwo :
        counterexampleUtility 2 ≤ counterexampleUtility 1 :=
      hTruthful 2
    norm_num [counterexampleUtility] at hReportTwo

end CommitRevealBoundary
end MechanismDesign
end TauSwap
