import Proofs.AMMLocalJetFrontier

/-!
# AMM Functional-Analysis Frontier

This file recasts the AMM local-frontier impossibility theorem as a theorem
about functions over a global price/state domain.

The key object is the positive function cone with the pointwise frontier
operator

`F(S)(q) = (1/8) / S(q)`.

The global no-free-lunch theorem is then an order-theoretic fact: `F` is
strictly antitone on the positive cone.  Therefore a candidate slippage function
that is pointwise no worse and strictly better somewhere cannot also have an
impermanent-loss curvature function that is pointwise no worse, provided both
profiles lie on the same frontier graph.

This does not derive the frontier graph from arbitrary CFMM code.  It isolates
the functional-analysis bridge a future full theorem must discharge: prove that
the admissible AMM function space maps into `FunctionalFrontierProfile`.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-! ## Positive function cone and frontier operator -/

/-- Pointwise positivity for a real-valued function on a global price/state
domain. -/
def PositiveFunction {ι : Type*} (f : ι → ℝ) : Prop :=
  ∀ q, 0 < f q

/-- The pointwise frontier operator attached to the local AMM uncertainty law. -/
def frontierOperator {ι : Type*} (slippage : ι → ℝ) : ι → ℝ :=
  fun q => (1 / 8 : ℝ) / slippage q

/-- Profiles that lie on the global frontier graph `C = F(S)`. -/
structure FunctionalFrontierProfile (ι : Type*) where
  slippage : ι → ℝ
  ilCoeff : ι → ℝ
  slippage_pos : PositiveFunction slippage
  il_eq_frontier : ilCoeff = frontierOperator slippage

/-- A frontier-operator profile is also a `GlobalFrontierProfile`, so all of
the existing no-dominance theorems apply. -/
def FunctionalFrontierProfile.toGlobalFrontierProfile {ι : Type*}
    (P : FunctionalFrontierProfile ι) : GlobalFrontierProfile ι where
  slippage := P.slippage
  ilCoeff := P.ilCoeff
  frontier q := by
    unfold FrontierInvariant
    rw [P.il_eq_frontier]
    simp [frontierOperator]
    field_simp [ne_of_gt (P.slippage_pos q)]
  slippage_pos := P.slippage_pos

/-- Conversely, a positive pointwise frontier profile is a functional frontier
profile.  This proves that the operator-graph view is equivalent to the older
product-invariant view, not an extra mathematical assumption. -/
def GlobalFrontierProfile.toFunctionalFrontierProfile {ι : Type*}
    (P : GlobalFrontierProfile ι) : FunctionalFrontierProfile ι where
  slippage := P.slippage
  ilCoeff := P.ilCoeff
  slippage_pos := P.slippage_pos
  il_eq_frontier := by
    funext q
    exact frontier_ilCoeff_eq (P.frontier q) (P.slippage_pos q)

/-- Strict Pareto dominance for the two extracted AMM observables, with lower
values better in both coordinates. -/
def StrictParetoDominates {ι : Type*}
    (candidateSlippage baselineSlippage candidateILCoeff baselineILCoeff : ι → ℝ) :
    Prop :=
  GloballyNoWorse candidateSlippage baselineSlippage ∧
    GloballyNoWorse candidateILCoeff baselineILCoeff ∧
    (StrictlyBetterSomewhere candidateSlippage baselineSlippage ∨
      StrictlyBetterSomewhere candidateILCoeff baselineILCoeff)

/-- The frontier operator is strictly antitone on the positive cone. -/
theorem frontierOperator_strict_antitone_at {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_candidate : PositiveFunction candidate)
    {q : ι}
    (hbetter : candidate q < baseline q) :
    frontierOperator baseline q < frontierOperator candidate q := by
  unfold frontierOperator
  exact div_lt_div_of_pos_left
    (by positivity : (0 : ℝ) < 1 / 8)
    (hpos_candidate q)
    hbetter

/-- Weak antitonicity of the frontier operator: pointwise lower slippage maps to
pointwise higher frontier-implied IL curvature. -/
theorem frontierOperator_antitone {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_candidate : PositiveFunction candidate)
    (hslippage_no_worse : GloballyNoWorse candidate baseline) :
    GloballyNoWorse (frontierOperator baseline) (frontierOperator candidate) := by
  intro q
  unfold frontierOperator
  exact div_le_div_of_nonneg_left
    (by positivity : (0 : ℝ) ≤ 1 / 8)
    (hpos_candidate q)
    (hslippage_no_worse q)

/-- Strict improvement somewhere in slippage maps to strict worsening somewhere
in frontier-implied IL curvature. -/
theorem frontierOperator_strictly_worse_somewhere {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_candidate : PositiveFunction candidate)
    (hslippage_strict : StrictlyBetterSomewhere candidate baseline) :
    StrictlyBetterSomewhere (frontierOperator baseline) (frontierOperator candidate) := by
  rcases hslippage_strict with ⟨q, hq⟩
  exact ⟨q, frontierOperator_strict_antitone_at hpos_candidate hq⟩

/-- Pointwise reflection of strict antitonicity: if frontier-implied curvature
is strictly worse at `q`, then the original slippage was strictly better at
`q`. -/
theorem frontierOperator_reflects_strict_antitone_at {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_baseline : PositiveFunction baseline)
    {q : ι}
    (hbetter_frontier :
      frontierOperator baseline q < frontierOperator candidate q) :
    candidate q < baseline q := by
  by_contra hnot
  have hle : baseline q ≤ candidate q := le_of_not_gt hnot
  have hfrontier_le :
      frontierOperator candidate q ≤ frontierOperator baseline q := by
    unfold frontierOperator
    exact div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ 1 / 8)
      (hpos_baseline q)
      hle
  exact not_lt_of_ge hfrontier_le hbetter_frontier

/-- Weak reflection of antitonicity: an order comparison after applying the
frontier operator reflects back to the reversed slippage order. -/
theorem frontierOperator_reflects_antitone {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_baseline : PositiveFunction baseline)
    (hfrontier_no_worse :
      GloballyNoWorse (frontierOperator baseline) (frontierOperator candidate)) :
    GloballyNoWorse candidate baseline := by
  intro q
  by_contra hnot
  have hlt : baseline q < candidate q := lt_of_not_ge hnot
  have hfrontier_worse :
      frontierOperator candidate q < frontierOperator baseline q :=
    frontierOperator_strict_antitone_at
      (baseline := candidate)
      (candidate := baseline)
      hpos_baseline
      hlt
  exact not_lt_of_ge (hfrontier_no_worse q) hfrontier_worse

/-- Strict reflection of antitonicity at the function level. -/
theorem frontierOperator_reflects_strictly_worse_somewhere {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_baseline : PositiveFunction baseline)
    (hfrontier_strict :
      StrictlyBetterSomewhere (frontierOperator baseline) (frontierOperator candidate)) :
    StrictlyBetterSomewhere candidate baseline := by
  rcases hfrontier_strict with ⟨q, hq⟩
  exact ⟨q, frontierOperator_reflects_strict_antitone_at hpos_baseline hq⟩

/-- Weak order equivalence induced by the frontier operator on positive
functions. -/
theorem frontierOperator_antitone_iff {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_baseline : PositiveFunction baseline)
    (hpos_candidate : PositiveFunction candidate) :
    GloballyNoWorse candidate baseline ↔
      GloballyNoWorse (frontierOperator baseline) (frontierOperator candidate) := by
  constructor
  · exact frontierOperator_antitone hpos_candidate
  · exact frontierOperator_reflects_antitone hpos_baseline

/-- Strict order equivalence induced by the frontier operator on positive
functions. -/
theorem frontierOperator_strictly_worse_somewhere_iff {ι : Type*}
    {baseline candidate : ι → ℝ}
    (hpos_baseline : PositiveFunction baseline)
    (hpos_candidate : PositiveFunction candidate) :
    StrictlyBetterSomewhere candidate baseline ↔
      StrictlyBetterSomewhere (frontierOperator baseline) (frontierOperator candidate) := by
  constructor
  · exact frontierOperator_strictly_worse_somewhere hpos_candidate
  · exact frontierOperator_reflects_strictly_worse_somewhere hpos_baseline

/-- The frontier operator is injective on positive functions. -/
theorem frontierOperator_injective_of_positive {ι : Type*}
    {left right : ι → ℝ}
    (hleft_pos : PositiveFunction left)
    (hright_pos : PositiveFunction right)
    (heq : frontierOperator left = frontierOperator right) :
    left = right := by
  funext q
  have hq := congrFun heq q
  unfold frontierOperator at hq
  field_simp [ne_of_gt (hleft_pos q), ne_of_gt (hright_pos q)] at hq
  linarith

/-- Functional-analysis form of the global no-free-lunch theorem.

If two global profiles lie on the frontier graph `C = F(S)`, a candidate cannot
be pointwise no worse in slippage, strictly better somewhere, and also pointwise
no worse in IL curvature. -/
theorem functional_frontier_no_simultaneous_dominance {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    (hslippage_no_worse :
      GloballyNoWorse candidate.slippage baseline.slippage)
    (hslippage_strict :
      StrictlyBetterSomewhere candidate.slippage baseline.slippage) :
    ¬ GloballyNoWorse candidate.ilCoeff baseline.ilCoeff :=
  global_frontier_no_simultaneous_dominance
    baseline.toGlobalFrontierProfile
    candidate.toGlobalFrontierProfile
    hslippage_no_worse
    hslippage_strict

/-- Direct witness form: a strict slippage gain at `q` forces strictly worse
frontier-implied IL curvature at the same `q`. -/
theorem functional_frontier_curvature_worse_at {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    {q : ι}
    (hbetter : candidate.slippage q < baseline.slippage q) :
    baseline.ilCoeff q < candidate.ilCoeff q := by
  rw [baseline.il_eq_frontier, candidate.il_eq_frontier]
  exact frontierOperator_strict_antitone_at
    candidate.slippage_pos hbetter

/-- A strict slippage gain somewhere gives a concrete point where the candidate
has worse frontier-implied IL curvature. -/
theorem functional_frontier_curvature_strictly_worse_somewhere {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    (hslippage_strict :
      StrictlyBetterSomewhere candidate.slippage baseline.slippage) :
    StrictlyBetterSomewhere baseline.ilCoeff candidate.ilCoeff := by
  rcases hslippage_strict with ⟨q, hq⟩
  exact ⟨q, functional_frontier_curvature_worse_at baseline candidate hq⟩

/-- Dual pointwise witness: a strict IL-curvature gain at `q` forces worse
slippage at the same point. -/
theorem functional_frontier_slippage_worse_at_strict_curvature_gain {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    {q : ι}
    (hbetter : candidate.ilCoeff q < baseline.ilCoeff q) :
    baseline.slippage q < candidate.slippage q :=
  global_frontier_slippage_worse_at_strict_il_gain
    baseline.toGlobalFrontierProfile
    candidate.toGlobalFrontierProfile
    hbetter

/-- A strict IL-curvature gain somewhere gives a concrete point where the
candidate has worse frontier-implied slippage. -/
theorem functional_frontier_slippage_strictly_worse_somewhere {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    (hcurvature_strict :
      StrictlyBetterSomewhere candidate.ilCoeff baseline.ilCoeff) :
    StrictlyBetterSomewhere baseline.slippage candidate.slippage := by
  rcases hcurvature_strict with ⟨q, hq⟩
  exact ⟨q, functional_frontier_slippage_worse_at_strict_curvature_gain
    baseline candidate hq⟩

/-- Dual functional-analysis no-dominance theorem.

If two global profiles lie on the frontier graph `C = F(S)`, a candidate cannot
be pointwise no worse in IL curvature, strictly better somewhere, and also
pointwise no worse in slippage. -/
theorem functional_frontier_no_simultaneous_dominance_from_curvature_gain {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    (hcurvature_no_worse :
      GloballyNoWorse candidate.ilCoeff baseline.ilCoeff)
    (hcurvature_strict :
      StrictlyBetterSomewhere candidate.ilCoeff baseline.ilCoeff) :
    ¬ GloballyNoWorse candidate.slippage baseline.slippage :=
  global_frontier_no_simultaneous_dominance_from_il_gain
    baseline.toGlobalFrontierProfile
    candidate.toGlobalFrontierProfile
    hcurvature_no_worse
    hcurvature_strict

/-- Frontier profiles form an antichain for the product order where lower
slippage and lower IL curvature are both considered better.  If a candidate is
no worse in both coordinates, then the two observable functions are equal. -/
theorem functional_frontier_antichain_eq {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι)
    (hslippage_no_worse :
      GloballyNoWorse candidate.slippage baseline.slippage)
    (hcurvature_no_worse :
      GloballyNoWorse candidate.ilCoeff baseline.ilCoeff) :
    candidate.slippage = baseline.slippage ∧
      candidate.ilCoeff = baseline.ilCoeff := by
  have hslippage_eq : candidate.slippage = baseline.slippage := by
    funext q
    rcases lt_or_eq_of_le (hslippage_no_worse q) with hlt | heq
    · have hcurvature_worse :
          baseline.ilCoeff q < candidate.ilCoeff q :=
        functional_frontier_curvature_worse_at baseline candidate hlt
      exact False.elim
        (not_lt_of_ge (hcurvature_no_worse q) hcurvature_worse)
    · exact heq
  have hcurvature_eq : candidate.ilCoeff = baseline.ilCoeff := by
    rw [candidate.il_eq_frontier, baseline.il_eq_frontier, hslippage_eq]
  exact ⟨hslippage_eq, hcurvature_eq⟩

/-- Functional frontier profiles allow no strict Pareto dominance: no distinct
candidate can be weakly better in both slippage and IL curvature while strictly
better in at least one. -/
theorem functional_frontier_no_strict_pareto_dominance {ι : Type*}
    (baseline candidate : FunctionalFrontierProfile ι) :
    ¬ StrictParetoDominates
      candidate.slippage baseline.slippage
      candidate.ilCoeff baseline.ilCoeff := by
  intro h
  rcases h with ⟨hslippage_no_worse, hcurvature_no_worse, hstrict⟩
  have heq := functional_frontier_antichain_eq
    baseline candidate hslippage_no_worse hcurvature_no_worse
  rcases hstrict with hslippage_strict | hcurvature_strict
  · rcases hslippage_strict with ⟨q, hq⟩
    rw [heq.1] at hq
    exact lt_irrefl _ hq
  · rcases hcurvature_strict with ⟨q, hq⟩
    rw [heq.2] at hq
    exact lt_irrefl _ hq

/-! ## Smooth normal-form families as functional-frontier profiles -/

/-- An indexed smooth normal-form AMM family induces a functional frontier
profile.  This is the functional-analysis packaging of the existing smooth
normal-form bridge. -/
def smoothLocalNormalFormFunctionalProfile {ι : Type*}
    (S : ι → SmoothLocalNormalForm) : FunctionalFrontierProfile ι where
  slippage q := cfmmWitnessSlippage (smoothLocalNormalFormWitness (S q))
  ilCoeff q := cfmmWitnessILCoeff (smoothLocalNormalFormWitness (S q))
  slippage_pos q := by
    change 0 < cfmmWitnessSlippage (smoothLocalNormalFormWitness (S q))
    rw [cfmmWitnessSlippage_eq_jet]
    exact jetSlippage_pos (S q).jet
  il_eq_frontier := by
    funext q
    exact frontier_ilCoeff_eq
      (smoothLocalNormalForm_frontier_invariant (S q))
      (by
        change 0 < cfmmWitnessSlippage (smoothLocalNormalFormWitness (S q))
        rw [cfmmWitnessSlippage_eq_jet]
        exact jetSlippage_pos (S q).jet)

/-- Functional-analysis no-dominance theorem for indexed smooth local
normal-form families. -/
theorem smoothLocalNormalForm_functional_no_simultaneous_dominance {ι : Type*}
    (baseline candidate : ι → SmoothLocalNormalForm)
    (hslippage_no_worse :
      GloballyNoWorse
        (smoothLocalNormalFormFunctionalProfile candidate).slippage
        (smoothLocalNormalFormFunctionalProfile baseline).slippage)
    (hslippage_strict :
      StrictlyBetterSomewhere
        (smoothLocalNormalFormFunctionalProfile candidate).slippage
        (smoothLocalNormalFormFunctionalProfile baseline).slippage) :
    ¬ GloballyNoWorse
      (smoothLocalNormalFormFunctionalProfile candidate).ilCoeff
      (smoothLocalNormalFormFunctionalProfile baseline).ilCoeff :=
  functional_frontier_no_simultaneous_dominance
    (smoothLocalNormalFormFunctionalProfile baseline)
    (smoothLocalNormalFormFunctionalProfile candidate)
    hslippage_no_worse
    hslippage_strict

/-! ## Raw AMM semantic boundary -/

/-- Minimal semantic interface for the remaining global theorem.

The hard AMM-specific work is exactly the construction of the two frontier
fields for every admissible raw AMM: positive extracted slippage and extracted
IL curvature equal to `F(slippage)`.  Once a concrete semantics layer supplies
this interface, the functional-analysis theorems in this file apply without
additional proof search. -/
structure RawFunctionalFrontierSemantics (RawAMM ι : Type*) where
  Admissible : RawAMM → Prop
  slippage : RawAMM → ι → ℝ
  ilCoeff : RawAMM → ι → ℝ
  slippage_pos : ∀ {A : RawAMM}, Admissible A → PositiveFunction (slippage A)
  il_eq_frontier :
    ∀ {A : RawAMM}, Admissible A → ilCoeff A = frontierOperator (slippage A)

/-- Every admissible raw AMM maps to a functional frontier profile.  This is the
formal target that a future concrete AMM calculus/semantics proof must build. -/
def RawFunctionalFrontierSemantics.profile {RawAMM ι : Type*}
    (M : RawFunctionalFrontierSemantics RawAMM ι)
    {A : RawAMM} (hA : M.Admissible A) : FunctionalFrontierProfile ι where
  slippage := M.slippage A
  ilCoeff := M.ilCoeff A
  slippage_pos := M.slippage_pos hA
  il_eq_frontier := M.il_eq_frontier hA

/-- Raw-semantics consequence: for admissible raw AMMs whose extracted
observables lie on the functional frontier, strict global slippage improvement
rules out global IL-curvature no-worse. -/
theorem RawFunctionalFrontierSemantics.not_simultaneous_global_no_worse
    {RawAMM ι : Type*} (M : RawFunctionalFrontierSemantics RawAMM ι)
    {baseline candidate : RawAMM}
    (hbaseline : M.Admissible baseline)
    (hcandidate : M.Admissible candidate)
    (hslippage_no_worse :
      GloballyNoWorse (M.slippage candidate) (M.slippage baseline))
    (hslippage_strict :
      StrictlyBetterSomewhere (M.slippage candidate) (M.slippage baseline)) :
    ¬ GloballyNoWorse (M.ilCoeff candidate) (M.ilCoeff baseline) := by
  simpa [RawFunctionalFrontierSemantics.profile] using
    functional_frontier_no_simultaneous_dominance
      (M.profile hbaseline)
      (M.profile hcandidate)
      hslippage_no_worse
      hslippage_strict

/-- Raw-semantics witness consequence: a strict global slippage gain for an
admissible candidate gives a concrete state where the candidate has worse
frontier-implied IL curvature. -/
theorem RawFunctionalFrontierSemantics.curvature_strictly_worse_somewhere
    {RawAMM ι : Type*} (M : RawFunctionalFrontierSemantics RawAMM ι)
    {baseline candidate : RawAMM}
    (hbaseline : M.Admissible baseline)
    (hcandidate : M.Admissible candidate)
    (hslippage_strict :
      StrictlyBetterSomewhere (M.slippage candidate) (M.slippage baseline)) :
    StrictlyBetterSomewhere (M.ilCoeff baseline) (M.ilCoeff candidate) := by
  simpa [RawFunctionalFrontierSemantics.profile] using
    functional_frontier_curvature_strictly_worse_somewhere
      (M.profile hbaseline)
      (M.profile hcandidate)
      hslippage_strict

/-- Raw-semantics antichain consequence: if an admissible candidate is no worse
in both extracted observables, then it has exactly the same extracted slippage
and IL-curvature functions as the baseline. -/
theorem RawFunctionalFrontierSemantics.antichain_eq
    {RawAMM ι : Type*} (M : RawFunctionalFrontierSemantics RawAMM ι)
    {baseline candidate : RawAMM}
    (hbaseline : M.Admissible baseline)
    (hcandidate : M.Admissible candidate)
    (hslippage_no_worse :
      GloballyNoWorse (M.slippage candidate) (M.slippage baseline))
    (hcurvature_no_worse :
      GloballyNoWorse (M.ilCoeff candidate) (M.ilCoeff baseline)) :
    M.slippage candidate = M.slippage baseline ∧
      M.ilCoeff candidate = M.ilCoeff baseline := by
  simpa [RawFunctionalFrontierSemantics.profile] using
    functional_frontier_antichain_eq
      (M.profile hbaseline)
      (M.profile hcandidate)
      hslippage_no_worse
      hcurvature_no_worse

/-- Raw-semantics Pareto-frontier consequence: no admissible candidate can
strictly Pareto-dominate an admissible baseline in the extracted slippage and
IL-curvature observables. -/
theorem RawFunctionalFrontierSemantics.no_strict_pareto_dominance
    {RawAMM ι : Type*} (M : RawFunctionalFrontierSemantics RawAMM ι)
    {baseline candidate : RawAMM}
    (hbaseline : M.Admissible baseline)
    (hcandidate : M.Admissible candidate) :
    ¬ StrictParetoDominates
      (M.slippage candidate) (M.slippage baseline)
      (M.ilCoeff candidate) (M.ilCoeff baseline) := by
  simpa [RawFunctionalFrontierSemantics.profile] using
    functional_frontier_no_strict_pareto_dominance
      (M.profile hbaseline)
      (M.profile hcandidate)

/-! ## Necessity of the frontier graph assumption -/

/-- The functional frontier graph assumption is necessary.  Without requiring
`C = F(S)`, simultaneous pointwise improvement remains consistent even on a
one-point global domain. -/
theorem simultaneous_functional_dominance_possible_without_frontier :
    ∃ (baselineSlippage candidateSlippage baselineILCoeff candidateILCoeff : PUnit → ℝ),
      PositiveFunction baselineSlippage ∧
        PositiveFunction candidateSlippage ∧
        GloballyNoWorse candidateSlippage baselineSlippage ∧
        StrictlyBetterSomewhere candidateSlippage baselineSlippage ∧
        GloballyNoWorse candidateILCoeff baselineILCoeff ∧
        StrictlyBetterSomewhere candidateILCoeff baselineILCoeff ∧
        candidateILCoeff ≠ frontierOperator candidateSlippage := by
  exact ⟨fun _ => (1 : ℝ), fun _ => (1 / 2 : ℝ),
    fun _ => (1 : ℝ), fun _ => (1 / 2 : ℝ), by
      constructor
      · intro q
        cases q
        norm_num
      constructor
      · intro q
        cases q
        norm_num
      constructor
      · intro q
        cases q
        norm_num
      constructor
      · exact ⟨PUnit.unit, by norm_num⟩
      constructor
      · intro q
        cases q
        norm_num
      constructor
      · exact ⟨PUnit.unit, by norm_num⟩
      · intro h
        have hunit := congrFun h PUnit.unit
        norm_num [frontierOperator] at hunit⟩

end

end LocalJetFrontier
end Impossibility
end TauSwap
