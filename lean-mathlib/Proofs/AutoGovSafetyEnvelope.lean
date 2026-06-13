import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# AutoGov Safety Envelope

This file formalizes the narrow safety envelope used by the autonomous
governance surface runner.

The theorem is intentionally abstract. It proves that once the deterministic
governance gates accept a proposed surface state, applying that decision
preserves the bounded parameter envelope across any finite trace. Runtime tests
bind this abstract apply rule to `admit_autonomous_governance_surface_request_v1`
and the Python/Tau governance gates.

It does not prove policy optimality, oracle truth, learned-model quality, or that
the Python implementation is equivalent to this model by itself.
-/

namespace Proofs
namespace AutoGovSafetyEnvelope

abbrev FeeMaxBps : Nat := 1000
abbrev FeeStepBps : Nat := 50
abbrev SplitShareMax : Nat := 10000
abbrev SplitSum : Nat := 10000
abbrev SplitStepBps : Nat := 500
abbrev RatioMinBps : Nat := 10000
abbrev RatioMaxBps : Nat := 30000
abbrev RatioStepBps : Nat := 1000
abbrev FundingCapMaxBps : Nat := 200
abbrev FundingStepBps : Nat := 25
abbrev WhaleStakerBpsMax : Nat := 7000
abbrev WhaleStepBps : Nat := 500

/-- The governance-surface state tracked by the autonomous policy runner. -/
structure SurfaceState where
  feeBps : Nat
  buyburnBps : Nat
  stakersBps : Nat
  reserveBps : Nat
  hostsBps : Nat
  mcrBps : Nat
  ccrBps : Nat
  stakerBps : Nat
  fundingCapBps : Nat
deriving Repr

def routerTotal (s : SurfaceState) : Nat :=
  s.buyburnBps + s.stakersBps + s.reserveBps + s.hostsBps

/-- Symmetric natural-number distance, used for bounded per-step drift. -/
def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- The state-level safety envelope that must hold after every admitted step. -/
def Envelope (s : SurfaceState) : Prop :=
  s.feeBps ≤ FeeMaxBps ∧
    routerTotal s = SplitSum ∧
    s.buyburnBps ≤ SplitShareMax ∧
    s.stakersBps ≤ SplitShareMax ∧
    s.reserveBps ≤ SplitShareMax ∧
    s.hostsBps ≤ SplitShareMax ∧
    RatioMinBps ≤ s.mcrBps ∧
    s.mcrBps ≤ s.ccrBps ∧
    s.ccrBps ≤ RatioMaxBps ∧
    s.stakerBps ≤ WhaleStakerBpsMax ∧
    s.fundingCapBps ≤ FundingCapMaxBps

def FeeGate (current proposed : SurfaceState) : Prop :=
  proposed.feeBps ≤ FeeMaxBps ∧
    absDiff current.feeBps proposed.feeBps ≤ FeeStepBps

def RouterGate (current proposed : SurfaceState) : Prop :=
  routerTotal proposed = SplitSum ∧
    proposed.buyburnBps ≤ SplitShareMax ∧
    proposed.stakersBps ≤ SplitShareMax ∧
    proposed.reserveBps ≤ SplitShareMax ∧
    proposed.hostsBps ≤ SplitShareMax ∧
    absDiff current.buyburnBps proposed.buyburnBps ≤ SplitStepBps ∧
    absDiff current.stakersBps proposed.stakersBps ≤ SplitStepBps ∧
    absDiff current.reserveBps proposed.reserveBps ≤ SplitStepBps ∧
    absDiff current.hostsBps proposed.hostsBps ≤ SplitStepBps

def CollateralGate (current proposed : SurfaceState) : Prop :=
  RatioMinBps ≤ proposed.mcrBps ∧
    proposed.mcrBps ≤ proposed.ccrBps ∧
    proposed.ccrBps ≤ RatioMaxBps ∧
    absDiff current.mcrBps proposed.mcrBps ≤ RatioStepBps ∧
    absDiff current.ccrBps proposed.ccrBps ≤ RatioStepBps

def WhaleGate (current proposed : SurfaceState) : Prop :=
  proposed.stakerBps ≤ WhaleStakerBpsMax ∧
    absDiff current.stakerBps proposed.stakerBps ≤ WhaleStepBps

def FundingGate (current proposed : SurfaceState) : Prop :=
  proposed.fundingCapBps ≤ FundingCapMaxBps ∧
    absDiff current.fundingCapBps proposed.fundingCapBps ≤ FundingStepBps

/--
Abstract acceptance predicate for one governance-surface proposal. This mirrors
the composition shape of the Python/Tau fee, router, collateral, whale, and
funding gates.
-/
def GateAccepted (current proposed : SurfaceState) : Prop :=
  FeeGate current proposed ∧
    RouterGate current proposed ∧
    CollateralGate current proposed ∧
    WhaleGate current proposed ∧
    FundingGate current proposed

/-- Gate acceptance implies the proposed state is inside the state envelope. -/
theorem gateAccepted_implies_envelope
    {current proposed : SurfaceState}
    (hGate : GateAccepted current proposed) :
    Envelope proposed := by
  rcases hGate with ⟨hFee, hRouter, hCollateral, hWhale, hFunding⟩
  rcases hFee with ⟨hFeeMax, _hFeeStep⟩
  rcases hRouter with
    ⟨hRouterSum, hBuyburnMax, hStakersMax, hReserveMax, hHostsMax,
      _hBuyburnStep, _hStakersStep, _hReserveStep, _hHostsStep⟩
  rcases hCollateral with
    ⟨hMcrMin, hMcrLeCcr, hCcrMax, _hMcrStep, _hCcrStep⟩
  rcases hWhale with ⟨hStakerMax, _hStakerStep⟩
  rcases hFunding with ⟨hFundingMax, _hFundingStep⟩
  exact
    ⟨hFeeMax, hRouterSum, hBuyburnMax, hStakersMax, hReserveMax, hHostsMax,
      hMcrMin, hMcrLeCcr, hCcrMax, hStakerMax, hFundingMax⟩

/-- One live admission decision. Rejections are deterministic no-ops. -/
structure SurfaceStep where
  proposed : SurfaceState
  admitted : Bool
deriving Repr

def applyStep (current : SurfaceState) (step : SurfaceStep) : SurfaceState :=
  if step.admitted then step.proposed else current

/--
Decision safety is decision-to-safety: when a step is admitted, the gate
acceptance fact is required as a hypothesis. Rejected steps need no proposed
state safety fact because the runner applies the committed state.
-/
def DecisionOK (current : SurfaceState) (step : SurfaceStep) : Prop :=
  step.admitted = true -> GateAccepted current step.proposed

theorem applyStep_preserves_envelope
    {current : SurfaceState} {step : SurfaceStep}
    (hCurrent : Envelope current)
    (hDecision : DecisionOK current step) :
    Envelope (applyStep current step) := by
  unfold applyStep
  cases hAdmitted : step.admitted
  · simpa [hAdmitted] using hCurrent
  · have hGate : GateAccepted current step.proposed := hDecision hAdmitted
    have hProposed : Envelope step.proposed := gateAccepted_implies_envelope hGate
    simpa [hAdmitted] using hProposed

def runSteps : SurfaceState -> List SurfaceStep -> SurfaceState
  | current, [] => current
  | current, step :: rest => runSteps (applyStep current step) rest

/-- Every admitted step in the trace is checked against the state where it runs. -/
def TraceOK : SurfaceState -> List SurfaceStep -> Prop
  | _current, [] => True
  | current, step :: rest =>
      DecisionOK current step ∧ TraceOK (applyStep current step) rest

/-- A finite trace of accepted/no-op decisions preserves the safety envelope. -/
theorem runSteps_preserves_envelope
    {initial : SurfaceState} {steps : List SurfaceStep}
    (hInitial : Envelope initial)
    (hTrace : TraceOK initial steps) :
    Envelope (runSteps initial steps) := by
  induction steps generalizing initial with
  | nil =>
      simpa [runSteps]
  | cons step rest ih =>
      simp [TraceOK] at hTrace
      have hHead : Envelope (applyStep initial step) :=
        applyStep_preserves_envelope hInitial hTrace.1
      exact ih hHead hTrace.2

/-- A single trajectory-budget counter for one governed parameter. -/
structure BudgetState where
  used : Nat
  limit : Nat
deriving Repr

structure BudgetStep where
  deltaAbs : Nat
  admitted : Bool
deriving Repr

def BudgetOK (b : BudgetState) : Prop :=
  b.used ≤ b.limit

def BudgetGate (b : BudgetState) (step : BudgetStep) : Prop :=
  b.used + step.deltaAbs ≤ b.limit

def applyBudgetStep (b : BudgetState) (step : BudgetStep) : BudgetState :=
  if step.admitted then { b with used := b.used + step.deltaAbs } else b

def BudgetDecisionOK (b : BudgetState) (step : BudgetStep) : Prop :=
  step.admitted = true -> BudgetGate b step

theorem applyBudgetStep_preserves_limit
    {b : BudgetState} {step : BudgetStep}
    (hBudget : BudgetOK b)
    (hDecision : BudgetDecisionOK b step) :
    BudgetOK (applyBudgetStep b step) := by
  unfold applyBudgetStep BudgetOK BudgetDecisionOK BudgetGate at *
  cases hAdmitted : step.admitted
  · simpa [hAdmitted] using hBudget
  · simpa [hAdmitted] using hDecision hAdmitted

theorem applyBudgetStep_used_monotone
  (b : BudgetState) (step : BudgetStep) :
    b.used ≤ (applyBudgetStep b step).used := by
  unfold applyBudgetStep
  cases step.admitted <;> simp

def runBudgetSteps : BudgetState -> List BudgetStep -> BudgetState
  | b, [] => b
  | b, step :: rest => runBudgetSteps (applyBudgetStep b step) rest

def BudgetTraceOK : BudgetState -> List BudgetStep -> Prop
  | _b, [] => True
  | b, step :: rest =>
      BudgetDecisionOK b step ∧ BudgetTraceOK (applyBudgetStep b step) rest

theorem runBudgetSteps_preserves_limit
    {initial : BudgetState} {steps : List BudgetStep}
    (hInitial : BudgetOK initial)
    (hTrace : BudgetTraceOK initial steps) :
    BudgetOK (runBudgetSteps initial steps) := by
  induction steps generalizing initial with
  | nil =>
      simpa [runBudgetSteps]
  | cons step rest ih =>
      simp [BudgetTraceOK] at hTrace
      have hHead : BudgetOK (applyBudgetStep initial step) :=
        applyBudgetStep_preserves_limit hInitial hTrace.1
      exact ih hHead hTrace.2

theorem runBudgetSteps_used_monotone
    (initial : BudgetState) (steps : List BudgetStep) :
    initial.used ≤ (runBudgetSteps initial steps).used := by
  induction steps generalizing initial with
  | nil =>
      simp [runBudgetSteps]
  | cons step rest ih =>
      exact (applyBudgetStep_used_monotone initial step).trans
        (ih (applyBudgetStep initial step))

end AutoGovSafetyEnvelope
end Proofs
