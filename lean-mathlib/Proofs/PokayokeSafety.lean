/-!
# Poka-yoke Safety Contract

This file formalizes the mistake-proofing contract used by the UI and audit
tools: a dangerous user action may be submitted only when an explicit interlock
has been satisfied by typed confirmation or an advanced override log.

The theorem is abstract by design.  Concrete UI or API surfaces instantiate it
by proving that their submit decision is computed by `submitAllowed` or an
equivalent fail-closed predicate.
-/

namespace TauSwap
namespace PokayokeSafety

/-- Risk states currently tracked by the mistake-proofing audit catalog. -/
inductive RiskStatus where
  | safe
  | mevConflict
  | inconclusiveMev
  | noRevertSafeOption
  | highPriceImpact
  | imbalancedLiquidity
  | nearTotalRemoval
  deriving DecidableEq, Repr

/-- Which statuses require an interlock before submission. -/
def dangerous : RiskStatus → Bool
  | .safe => false
  | .mevConflict => true
  | .inconclusiveMev => true
  | .noRevertSafeOption => true
  | .highPriceImpact => true
  | .imbalancedLiquidity => true
  | .nearTotalRemoval => true

/-- Runtime evidence that the user-facing interlock was actually satisfied. -/
structure InterlockState where
  interlockPresent : Bool
  typedConfirmAccepted : Bool
  advancedOverrideLogged : Bool
  deriving DecidableEq, Repr

/-- Positive evidence that it is acceptable to pass a dangerous action through
the submit path. -/
def interlockSatisfied (i : InterlockState) : Bool :=
  i.interlockPresent && (i.typedConfirmAccepted || i.advancedOverrideLogged)

/-- Fail-closed submit decision. -/
def submitAllowed (status : RiskStatus) (i : InterlockState) : Bool :=
  !dangerous status || interlockSatisfied i

/-- Semantic contract: a status is shielded if it is not dangerous, or if the
interlock exists and has been explicitly satisfied. -/
def Shielded (status : RiskStatus) (i : InterlockState) : Prop :=
  dangerous status = false ∨
    i.interlockPresent = true ∧
      (i.typedConfirmAccepted = true ∨ i.advancedOverrideLogged = true)

theorem interlockSatisfied_true_iff (i : InterlockState) :
    interlockSatisfied i = true ↔
      i.interlockPresent = true ∧
        (i.typedConfirmAccepted = true ∨ i.advancedOverrideLogged = true) := by
  unfold interlockSatisfied
  rw [Bool.and_eq_true, Bool.or_eq_true]

/-- If submission is allowed, then the status is shielded. -/
theorem submitAllowed_implies_shielded
    (status : RiskStatus)
    (i : InterlockState)
    (h : submitAllowed status i = true) :
    Shielded status i := by
  unfold submitAllowed at h
  unfold Shielded
  rw [Bool.or_eq_true] at h
  rcases h with hsafe | hinterlock
  · left
    cases hdanger : dangerous status
    · rfl
    · rw [hdanger] at hsafe
      contradiction
  · right
    exact (interlockSatisfied_true_iff i).1 hinterlock

/-- A dangerous action without a satisfied interlock cannot pass the submit
predicate. -/
theorem dangerous_without_interlock_blocks
    (status : RiskStatus)
    (i : InterlockState)
    (hdanger : dangerous status = true)
    (hinterlock : interlockSatisfied i = false) :
    submitAllowed status i = false := by
  simp [submitAllowed, hdanger, hinterlock]

/-- Dangerous actions that do pass must have a satisfied interlock. -/
theorem allowed_dangerous_requires_interlock
    (status : RiskStatus)
    (i : InterlockState)
    (hdanger : dangerous status = true)
    (hallowed : submitAllowed status i = true) :
    interlockSatisfied i = true := by
  unfold submitAllowed at hallowed
  rw [hdanger] at hallowed
  exact hallowed

/-- A concrete typed confirmation is sufficient for a dangerous submit path. -/
theorem typed_confirmation_allows
    (status : RiskStatus)
    (i : InterlockState)
    (hpresent : i.interlockPresent = true)
    (htyped : i.typedConfirmAccepted = true) :
    submitAllowed status i = true := by
  simp [submitAllowed, interlockSatisfied, hpresent, htyped]

/-- A logged advanced override is sufficient for a dangerous submit path. -/
theorem advanced_override_allows
    (status : RiskStatus)
    (i : InterlockState)
    (hpresent : i.interlockPresent = true)
    (hoverride : i.advancedOverrideLogged = true) :
    submitAllowed status i = true := by
  simp [submitAllowed, interlockSatisfied, hpresent, hoverride]

end PokayokeSafety
end TauSwap
