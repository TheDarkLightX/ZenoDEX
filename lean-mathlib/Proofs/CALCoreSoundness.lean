import Proofs.CertifiedFinancialMathObjects
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# CAL Core Soundness

This file turns the CAL/FIRE skeleton theorem into a checked theorem over the
existing `CertifiedFinancialObject` core.

The public CAL draft has many artifact and governance gates.  Those gates are
modeled here as concrete fields/projections, while the funds-moving financial
gates are defined against the certified object:

* accepted witnesses replay through the object's transition system,
* accepted collateral posts at least the certified holder/writer collateral,
* accepted deltas are bound to the replayed payoff,
* conservation and replay determinism are explicit fields,
* settlement safety is derived from the certified payoff bounds.

This is not a full runtime verifier.  It is the first machine-checked
admission-logic soundness theorem for the CAL shape.
-/

namespace Proofs
namespace CALCoreSoundness

open CertifiedFinancialMathObjects

variable {State Witness : Type _}

/-! ## Evidence floor -/

/-- Evidence classes ordered from strongest to weakest. -/
inductive Evidence where
  | proved
  | contract
  | implemented
  | testedDiscovery
  | hypothesis
  deriving DecidableEq, Repr

/-- Numeric strength rank; higher is stronger. -/
def Evidence.rank : Evidence -> Nat
  | .proved => 4
  | .contract => 3
  | .implemented => 2
  | .testedDiscovery => 1
  | .hypothesis => 0

/-- Evidence meet returns the weaker dependency. -/
def Evidence.meet (left right : Evidence) : Evidence :=
  if left.rank ≤ right.rank then left else right

@[simp] theorem evidence_meet_proved_left (e : Evidence) :
    Evidence.meet Evidence.proved e = e := by
  cases e <;> rfl

@[simp] theorem evidence_meet_proved_right (e : Evidence) :
    Evidence.meet e Evidence.proved = e := by
  cases e <;> rfl

@[simp] theorem evidence_meet_hypothesis_left (e : Evidence) :
    Evidence.meet Evidence.hypothesis e = Evidence.hypothesis := by
  cases e <;> rfl

@[simp] theorem evidence_meet_hypothesis_right (e : Evidence) :
    Evidence.meet e Evidence.hypothesis = Evidence.hypothesis := by
  cases e <;> rfl

theorem evidence_meet_comm (left right : Evidence) :
    Evidence.meet left right = Evidence.meet right left := by
  cases left <;> cases right <;> rfl

theorem evidence_meet_idem (e : Evidence) :
    Evidence.meet e e = e := by
  cases e <;> rfl

/-! ## Integer interval helper lemmas from the skeleton -/

structure IntInterval where
  lower : Int
  upper : Int
  valid : lower ≤ upper

def InInterval (x : Int) (I : IntInterval) : Prop :=
  I.lower ≤ x ∧ x ≤ I.upper

/-- Generic collateral theorem for a two-party scalar integer payoff. -/
theorem collateral_two_party_no_default
    (f L U CA CB : Int)
    (hL : L ≤ f)
    (hU : f ≤ U)
    (hCA : CA ≥ max 0 (-L))
    (hCB : CB ≥ max 0 U) :
    CA + f ≥ 0 ∧ CB - f ≥ 0 := by
  constructor <;> omega

/-- Integer capped positive-part bound. -/
theorem cap_bound (x C : Int) (hC : C ≥ 0) :
    0 ≤ min (max x 0) C ∧ min (max x 0) C ≤ C := by
  exact ⟨le_min (le_max_right x 0) hC, min_le_right _ _⟩

/-- Integer clamp bound. -/
theorem clamp_bound (x A B : Int) (hAB : A ≤ B) :
    A ≤ min (max x A) B ∧ min (max x A) B ≤ B := by
  exact ⟨le_min (le_max_right x A) hAB, min_le_right _ _⟩

/-! ## Concrete CAL verifier surface -/

structure ObjectTemplate (State Witness : Type _) where
  objectHash : String
  cfo : CertifiedFinancialObject State Witness
  schemaOk : Prop
  dependencyClosed : Prop
  unitOk : Prop
  domainOk : Prop

structure ObjectInstance (State : Type _) where
  instanceHash : String
  objectHash : String
  initialState : State
  paramOk : Prop
  authorizationOk : Prop
  nonceOk : Prop

structure Certificate where
  objectHash : String
  instanceHash? : Option String
  evidenceFloor : Evidence
  certOk : Prop
  evidenceOk : Prop

structure WitnessBundle (Witness : Type _) where
  witnessHash : String
  instanceHash : String
  trace : List Witness
  maturityOk : Prop
  windowOk : Prop

structure CollateralTable where
  holderPosted : ℝ
  writerPosted : ℝ

structure DeltaTable (State : Type _) where
  finalState : State
  payoff : ℝ
  conserved : Prop
  replayDeterministic : Prop

def SchemaOK
    (O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (_Γ : Certificate) : Prop :=
  O.schemaOk

def HashBindOK
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (Γ : Certificate) : Prop :=
  I.objectHash = O.objectHash ∧
    Γ.objectHash = O.objectHash ∧
    (Γ.instanceHash? = none ∨ Γ.instanceHash? = some I.instanceHash)

def DependencyClosed (O : ObjectTemplate State Witness) : Prop :=
  O.dependencyClosed

def UnitOK (O : ObjectTemplate State Witness) : Prop :=
  O.unitOk

def DomainOK (O : ObjectTemplate State Witness) : Prop :=
  O.domainOk

def ParamOK
    (I : ObjectInstance State)
    (O : ObjectTemplate State Witness) : Prop :=
  I.paramOk ∧ I.objectHash = O.objectHash ∧ O.cfo.invariant I.initialState

def AuthorizationOK (I : ObjectInstance State) : Prop :=
  I.authorizationOk

def NonceOK (I : ObjectInstance State) : Prop :=
  I.nonceOk

def MaturityOK (_I : ObjectInstance State) (w : WitnessBundle Witness) : Prop :=
  w.maturityOk

def WindowOK (_I : ObjectInstance State) (w : WitnessBundle Witness) : Prop :=
  w.windowOk

def CertOK
    (_O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (Γ : Certificate) : Prop :=
  Γ.certOk

def EvidenceOK (Γ : Certificate) : Prop :=
  Γ.evidenceOk ∧ Γ.evidenceFloor ≠ Evidence.hypothesis

def WitnessOK
    (O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (w : WitnessBundle Witness) : Prop :=
  List.Forall O.cfo.witnessOk w.trace

def CollateralOK
    (O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (C : CollateralTable) : Prop :=
  writerCollateral O.cfo.upper ≤ C.writerPosted ∧
    holderCollateral O.cfo.lower ≤ C.holderPosted

def IntegerEvalOK
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (w : WitnessBundle Witness)
    (Δ : DeltaTable State) : Prop :=
  Δ.finalState = O.cfo.run I.initialState w.trace ∧
    Δ.payoff = O.cfo.payoff Δ.finalState

def DeltaConservationOK
    (_O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (Δ : DeltaTable State) : Prop :=
  Δ.conserved

def ReplayOK
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (w : WitnessBundle Witness)
    (Δ : DeltaTable State) : Prop :=
  Δ.finalState = O.cfo.run I.initialState w.trace ∧ Δ.replayDeterministic

def CollateralSafe
    (_I : ObjectInstance State)
    (C : CollateralTable)
    (Δ : DeltaTable State) : Prop :=
  0 ≤ C.holderPosted + Δ.payoff ∧ 0 ≤ C.writerPosted - Δ.payoff

def DeltaConserved
    (_O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (Δ : DeltaTable State) : Prop :=
  Δ.conserved

def ReplayDeterministic
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (w : WitnessBundle Witness)
    (Δ : DeltaTable State) : Prop :=
  Δ.finalState = O.cfo.run I.initialState w.trace ∧ Δ.replayDeterministic

def IntegerEvalWithinBounds
    (O : ObjectTemplate State Witness)
    (_I : ObjectInstance State)
    (_w : WitnessBundle Witness)
    (Δ : DeltaTable State) : Prop :=
  O.cfo.lower ≤ Δ.payoff ∧ Δ.payoff ≤ O.cfo.upper

def SettlementSafe
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (w : WitnessBundle Witness)
    (C : CollateralTable)
    (Δ : DeltaTable State) : Prop :=
  CollateralSafe I C Δ ∧
    DeltaConserved O I Δ ∧
    ReplayDeterministic O I w Δ ∧
    IntegerEvalWithinBounds O I w Δ

def FIREVAccept
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (Γ : Certificate)
    (w : WitnessBundle Witness)
    (C : CollateralTable)
    (Δ : DeltaTable State) : Prop :=
  SchemaOK O I Γ ∧
    HashBindOK O I Γ ∧
    DependencyClosed O ∧
    UnitOK O ∧
    DomainOK O ∧
    ParamOK I O ∧
    AuthorizationOK I ∧
    NonceOK I ∧
    MaturityOK I w ∧
    WindowOK I w ∧
    CertOK O I Γ ∧
    EvidenceOK Γ ∧
    WitnessOK O I w ∧
    CollateralOK O I C ∧
    IntegerEvalOK O I w Δ ∧
    DeltaConservationOK O I Δ ∧
    ReplayOK O I w Δ

/-- The replayed final state satisfies the certified object invariant, given
parameter, witness, and evaluation acceptance.  Shared by all settlement-safety
conclusions. -/
private theorem finalState_invariant
    {O : ObjectTemplate State Witness}
    {I : ObjectInstance State}
    {w : WitnessBundle Witness}
    {Δ : DeltaTable State}
    (hparam : ParamOK I O)
    (hwitness : WitnessOK O I w)
    (heval : IntegerEvalOK O I w Δ) :
    O.cfo.invariant Δ.finalState := by
  rw [heval.1]
  exact O.cfo.invariant_run hparam.2.2 hwitness

/-- The evaluated payoff at the replayed final state lies within the certified
bounds.  Shared by collateral and within-bounds conclusions. -/
private theorem payoff_within_bounds
    {O : ObjectTemplate State Witness}
    {I : ObjectInstance State}
    {w : WitnessBundle Witness}
    {Δ : DeltaTable State}
    (hparam : ParamOK I O)
    (hwitness : WitnessOK O I w)
    (heval : IntegerEvalOK O I w Δ) :
    O.cfo.lower ≤ Δ.payoff ∧ Δ.payoff ≤ O.cfo.upper := by
  rw [heval.2]
  exact O.cfo.payoffBounded (finalState_invariant hparam hwitness heval)

/-- Accepted collateral plus a certified payoff bound implies bilateral
collateral safety. -/
theorem collateralOK_implies_collateralSafe
    {O : ObjectTemplate State Witness}
    {I : ObjectInstance State}
    {w : WitnessBundle Witness}
    {C : CollateralTable}
    {Δ : DeltaTable State}
    (hparam : ParamOK I O)
    (hwitness : WitnessOK O I w)
    (hcollateral : CollateralOK O I C)
    (heval : IntegerEvalOK O I w Δ) :
    CollateralSafe I C Δ := by
  have hBase := bilateral_no_default_of_bounds (payoff_within_bounds hparam hwitness heval)
  exact ⟨by linarith [hBase.1, hcollateral.2], by linarith [hBase.2, hcollateral.1]⟩

/-- Accepted integer evaluation is within the certified payoff bounds. -/
theorem integerEvalOK_within_bounds
    {O : ObjectTemplate State Witness}
    {I : ObjectInstance State}
    {w : WitnessBundle Witness}
    {Δ : DeltaTable State}
    (hparam : ParamOK I O)
    (hwitness : WitnessOK O I w)
    (heval : IntegerEvalOK O I w Δ) :
    IntegerEvalWithinBounds O I w Δ :=
  payoff_within_bounds hparam hwitness heval

/-- Concrete CAL/FIRE-V acceptance soundness theorem. -/
theorem fireV_accept_soundness
    (O : ObjectTemplate State Witness)
    (I : ObjectInstance State)
    (Γ : Certificate)
    (w : WitnessBundle Witness)
    (C : CollateralTable)
    (Δ : DeltaTable State)
    (h : FIREVAccept O I Γ w C Δ) :
    SettlementSafe O I w C Δ := by
  rcases h with
    ⟨_hSchema, _hHash, _hDep, _hUnit, _hDomain, hParam,
      _hAuth, _hNonce, _hMaturity, _hWindow, _hCert, _hEvidence,
      hWitness, hCollateral, hEval, hDelta, hReplay⟩
  exact ⟨
    collateralOK_implies_collateralSafe hParam hWitness hCollateral hEval,
    hDelta,
    hReplay,
    integerEvalOK_within_bounds hParam hWitness hEval
  ⟩

end CALCoreSoundness
end Proofs
