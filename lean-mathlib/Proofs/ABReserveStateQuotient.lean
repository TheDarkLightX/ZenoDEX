import Proofs.ABStrictZeroMinMonotone

/-!
# AB Reserve-State Quotient Bridge

This file isolates the Lean proof component behind the reserve-state quotient
certificate checker.

The host checker groups full order histories by the pair
`(processedReserveIn, reserveOut)`.  This file proves the abstract contract for
that grouping: future strict exact-in suffix behavior depends only on that pair,
and a selected state with minimum output reserve dominates the finite quotient
family for the strict zero-min economic key at fixed executed input.

Scope: this is a research proof component.  It does not prove Python-to-Lean
refinement, JSON canonicalization, packet hashing, nonzero `min_amount_out`,
canonical tie order, settlement, state-root, production, or governance
authority.
-/

namespace ABReserveStateQuotient

open ABStrictZeroMinMonotone

/-- Reserve-state quotient key for the strict zero-min research surface.

Two full order histories with the same value here expose the same state to any
future fixed exact-in suffix in the abstract model. -/
structure ReserveState where
  processedReserveIn : Nat
  reserveOut : Nat
  deriving Repr, DecidableEq

/-- Interpret a reserve-state quotient row as the existing processed-record
model from the AB strict zero-min proof ladder. -/
def ReserveState.toRecord (state : ReserveState) : ProcessedRecord :=
  ⟨state.processedReserveIn, state.reserveOut⟩

/-- Apply one common exact-in step to a reserve-state quotient row.

This is the local transition used by the quotient induction surface.  It does
not assert that the host actually emits this child; it only states the abstract
state update once a fixed step is chosen. -/
def ReserveState.afterStep (state : ReserveState) (step : ExactInStep) : ReserveState :=
  ⟨state.processedReserveIn + step.grossIn,
    postReserveOut state.processedReserveIn state.reserveOut step.netIn⟩

/-- Final output reserve after running a fixed suffix from a reserve state. -/
def finalReserveOutAfterState (state : ReserveState) (suffix : List ExactInStep) : Nat :=
  finalReserveOutAfterRecord state.toRecord suffix

/-- Total zero-min suffix output extracted from a reserve state. -/
def stateSuffixOutput
    (initialReserveOut : Nat)
    (state : ReserveState)
    (suffix : List ExactInStep) : Nat :=
  suffixTotalOutput initialReserveOut state.toRecord suffix

/-- Reserve-state equivalence is equality of the two fields kept by the
quotient. -/
def reserveStateEquivalent (left right : ReserveState) : Prop :=
  left.processedReserveIn = right.processedReserveIn ∧
    left.reserveOut = right.reserveOut

/-- Equivalent reserve states have the same final output reserve for any fixed
suffix. -/
theorem reserveStateEquivalent_same_finalReserveOut
    {left right : ReserveState}
    {suffix : List ExactInStep}
    (heq : reserveStateEquivalent left right) :
    finalReserveOutAfterState left suffix =
      finalReserveOutAfterState right suffix := by
  rcases heq with ⟨hin, hout⟩
  cases left
  cases right
  simp at hin hout
  subst hin
  subst hout
  rfl

/-- Equivalent reserve states have the same zero-min suffix output for any fixed
suffix. -/
theorem reserveStateEquivalent_same_suffixOutput
    {initialReserveOut : Nat}
    {left right : ReserveState}
    {suffix : List ExactInStep}
    (heq : reserveStateEquivalent left right) :
    stateSuffixOutput initialReserveOut left suffix =
      stateSuffixOutput initialReserveOut right suffix := by
  rcases heq with ⟨hin, hout⟩
  cases left
  cases right
  simp at hin hout
  subst hin
  subst hout
  rfl

/-- A selected reserve state dominates another state with the same processed
input reserve and no lower output reserve. -/
theorem reserveState_minReserve_dominates_suffixOutput
    {initialReserveOut : Nat}
    {selected candidate : ReserveState}
    {suffix : List ExactInStep}
    (hsame :
      selected.processedReserveIn = candidate.processedReserveIn)
    (hmin :
      selected.reserveOut ≤ candidate.reserveOut) :
    stateSuffixOutput initialReserveOut candidate suffix ≤
      stateSuffixOutput initialReserveOut selected suffix := by
  unfold stateSuffixOutput ReserveState.toRecord
  exact minReserveRecord_dominates_suffixTotalOutput
    (initialReserveOut := initialReserveOut)
    (lower := selected.toRecord)
    (upper := candidate.toRecord)
    (suffix := suffix)
    hsame
    hmin

/-- Best suffix output from all states in a finite quotient family. -/
def quotientFullBestSuffixOutput
    (initialReserveOut : Nat)
    (states : List ReserveState)
    (suffix : List ExactInStep) : Nat :=
  (states.map (fun state => stateSuffixOutput initialReserveOut state suffix)).foldl Nat.max 0

/-- Local validity for a selected reserve state over a finite quotient family.

The selected state must be present in the family, have the same processed input
reserve as every family member, and have no greater output reserve than any
family member. -/
def reserveStateQuotientInvariant
    (selected : ReserveState)
    (states : List ReserveState) : Prop :=
  selected ∈ states ∧
    (∀ state, state ∈ states ->
      selected.processedReserveIn = state.processedReserveIn) ∧
    (∀ state, state ∈ states ->
      selected.reserveOut ≤ state.reserveOut)

/-- Applying the same step to two rows with the same processed input keeps their
processed input equal. -/
theorem reserveState_afterStep_same_processed
    {selected candidate : ReserveState}
    {step : ExactInStep}
    (hsame :
      selected.processedReserveIn = candidate.processedReserveIn) :
    (ReserveState.afterStep selected step).processedReserveIn =
      (ReserveState.afterStep candidate step).processedReserveIn := by
  simp [ReserveState.afterStep, hsame]

/-- Applying the same step to a lower-output-reserve row preserves the
lower-output-reserve ordering. -/
theorem reserveState_afterStep_minReserve
    {selected candidate : ReserveState}
    {step : ExactInStep}
    (hsame :
      selected.processedReserveIn = candidate.processedReserveIn)
    (hmin :
      selected.reserveOut ≤ candidate.reserveOut) :
    (ReserveState.afterStep selected step).reserveOut ≤
      (ReserveState.afterStep candidate step).reserveOut := by
  simp [ReserveState.afterStep]
  rw [hsame]
  exact postReserveOut_mono_reserveOut
    (reserveIn := candidate.processedReserveIn)
    (netIn := step.netIn)
    hmin

/-- One-step quotient-invariant preservation.

If `selected` is the minimum-output-reserve representative of a finite quotient
family, applying one common exact-in step to every family member keeps the
selected child as a valid minimum-output-reserve representative. -/
theorem reserveStateQuotientInvariant_afterStep
    {selected : ReserveState}
    {states : List ReserveState}
    {step : ExactInStep}
    (hinvariant : reserveStateQuotientInvariant selected states) :
    reserveStateQuotientInvariant
      (ReserveState.afterStep selected step)
      (states.map (fun state => ReserveState.afterStep state step)) := by
  rcases hinvariant with ⟨hselectedMem, hsame, hmin⟩
  unfold reserveStateQuotientInvariant
  constructor
  · exact List.mem_map.mpr ⟨selected, hselectedMem, rfl⟩
  · constructor
    · intro state hstate
      rw [List.mem_map] at hstate
      rcases hstate with ⟨candidate, hcandidate, rfl⟩
      exact reserveState_afterStep_same_processed
        (selected := selected)
        (candidate := candidate)
        (step := step)
        (hsame candidate hcandidate)
    · intro state hstate
      rw [List.mem_map] at hstate
      rcases hstate with ⟨candidate, hcandidate, rfl⟩
      exact reserveState_afterStep_minReserve
        (selected := selected)
        (candidate := candidate)
        (step := step)
        (hsame candidate hcandidate)
        (hmin candidate hcandidate)

/-- A finite reserve-state quotient family is bounded by its selected minimum
output-reserve state. -/
theorem quotientFullBestSuffixOutput_le_selected
    {initialReserveOut : Nat}
    {selected : ReserveState}
    {states : List ReserveState}
    {suffix : List ExactInStep}
    (hinvariant : reserveStateQuotientInvariant selected states) :
    quotientFullBestSuffixOutput initialReserveOut states suffix ≤
      stateSuffixOutput initialReserveOut selected suffix := by
  rcases hinvariant with ⟨_hselectedMem, hsame, hmin⟩
  unfold quotientFullBestSuffixOutput
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨state, hstate, rfl⟩
    exact reserveState_minReserve_dominates_suffixOutput
      (initialReserveOut := initialReserveOut)
      (selected := selected)
      (candidate := state)
      (suffix := suffix)
      (hsame state hstate)
      (hmin state hstate)

/-- Economic key for the full finite quotient family at fixed executed input. -/
def quotientFullFrontierZeroMinEconomicKey
    (executedInput initialReserveOut : Nat)
    (states : List ReserveState)
    (suffix : List ExactInStep) : ZeroMinEconomicKey :=
  ⟨executedInput, quotientFullBestSuffixOutput initialReserveOut states suffix⟩

/-- Economic key for the selected reserve state at fixed executed input. -/
def quotientSelectedZeroMinEconomicKey
    (executedInput initialReserveOut : Nat)
    (selected : ReserveState)
    (suffix : List ExactInStep) : ZeroMinEconomicKey :=
  ⟨executedInput, stateSuffixOutput initialReserveOut selected suffix⟩

/-- A valid finite reserve-state quotient family is economically dominated by
the selected state at fixed executed input. -/
theorem reserveStateQuotientInvariant_bounds_zeroMinEconomicKey
    {executedInput initialReserveOut : Nat}
    {selected : ReserveState}
    {states : List ReserveState}
    {suffix : List ExactInStep}
    (hinvariant : reserveStateQuotientInvariant selected states) :
    zeroMinEconomicKeyDominated
      (quotientFullFrontierZeroMinEconomicKey executedInput initialReserveOut states suffix)
      (quotientSelectedZeroMinEconomicKey executedInput initialReserveOut selected suffix) := by
  unfold zeroMinEconomicKeyDominated
    quotientFullFrontierZeroMinEconomicKey
    quotientSelectedZeroMinEconomicKey
  exact ⟨Nat.le_refl executedInput,
    quotientFullBestSuffixOutput_le_selected
      (initialReserveOut := initialReserveOut)
      (selected := selected)
      (states := states)
      (suffix := suffix)
      hinvariant⟩

/-- Data-only shell for a host-emitted reserve-state quotient table.

The Boolean fields mirror the host-side packet rails. They are modeled as
validity inputs; this file does not prove hash computation or host refinement. -/
structure ReserveStateQuotientHostTable where
  states : List ReserveState
  selected : ReserveState
  initialReserveOut : Nat
  executedInput : Nat
  suffix : List ExactInStep
  packetHashBound : Bool
  noAuthorityEffect : Bool
  quotientFamilyBound : Bool
  selectedStateBound : Bool
  deriving Repr

/-- Validity predicate for the reserve-state quotient host table. -/
def reserveStateQuotientHostTableValid
    (table : ReserveStateQuotientHostTable) : Prop :=
  table.packetHashBound = true ∧
    table.noAuthorityEffect = true ∧
    table.quotientFamilyBound = true ∧
    table.selectedStateBound = true ∧
    reserveStateQuotientInvariant table.selected table.states ∧
    suffixExecutable table.selected.processedReserveIn table.selected.reserveOut table.suffix

/-- Full quotient-family key named through the host table. -/
def reserveStateQuotientHostTableFullKey
    (table : ReserveStateQuotientHostTable) : ZeroMinEconomicKey :=
  quotientFullFrontierZeroMinEconomicKey table.executedInput
    table.initialReserveOut table.states table.suffix

/-- Selected quotient-state key named through the host table. -/
def reserveStateQuotientHostTableSelectedKey
    (table : ReserveStateQuotientHostTable) : ZeroMinEconomicKey :=
  quotientSelectedZeroMinEconomicKey table.executedInput
    table.initialReserveOut table.selected table.suffix

/-- Host-table endpoint for the reserve-state quotient bridge.

A valid table gives the host rails, proves selected-state membership in the
quotient family, proves economic-key dominance at fixed executed input, and
carries suffix executability for the selected state. -/
theorem reserveStateQuotientHostTable_validates
    (table : ReserveStateQuotientHostTable)
    (hvalid : reserveStateQuotientHostTableValid table) :
    table.packetHashBound = true ∧
      table.noAuthorityEffect = true ∧
      table.quotientFamilyBound = true ∧
      table.selectedStateBound = true ∧
      table.selected ∈ table.states ∧
      zeroMinEconomicKeyDominated
        (reserveStateQuotientHostTableFullKey table)
        (reserveStateQuotientHostTableSelectedKey table) ∧
      suffixExecutable table.selected.processedReserveIn table.selected.reserveOut table.suffix := by
  rcases hvalid with
    ⟨hhash, hnoAuthority, hfamily, hselectedBound, hinvariant, hexec⟩
  exact ⟨hhash, hnoAuthority, hfamily, hselectedBound,
    hinvariant.1,
    reserveStateQuotientInvariant_bounds_zeroMinEconomicKey
      (executedInput := table.executedInput)
      (initialReserveOut := table.initialReserveOut)
      (selected := table.selected)
      (states := table.states)
      (suffix := table.suffix)
      hinvariant,
    hexec⟩

/-- Host-visible summary shell for a reserve-state quotient table.

The summary binds count and selected-state metadata to the validated Lean table.
It is a checker boundary only: host construction, JSON canonicalization, and
packet hashing remain outside this proof component. -/
structure ReserveStateQuotientObservedSummary where
  table : ReserveStateQuotientHostTable
  observedStateCount : Nat
  observedSelectedReserveIn : Nat
  observedSelectedReserveOut : Nat
  observedExecutedInput : Nat
  observedInitialReserveOut : Nat
  deriving Repr

/-- Validity predicate for the observed reserve-state quotient summary. -/
def reserveStateQuotientObservedSummaryValid
    (summary : ReserveStateQuotientObservedSummary) : Prop :=
  reserveStateQuotientHostTableValid summary.table ∧
    summary.observedStateCount = summary.table.states.length ∧
    summary.observedSelectedReserveIn = summary.table.selected.processedReserveIn ∧
    summary.observedSelectedReserveOut = summary.table.selected.reserveOut ∧
    summary.observedExecutedInput = summary.table.executedInput ∧
    summary.observedInitialReserveOut = summary.table.initialReserveOut

/-- Full quotient-family key named through observed summary metadata. -/
def reserveStateQuotientObservedSummaryFullKey
    (summary : ReserveStateQuotientObservedSummary) : ZeroMinEconomicKey :=
  quotientFullFrontierZeroMinEconomicKey summary.observedExecutedInput
    summary.observedInitialReserveOut summary.table.states summary.table.suffix

/-- Selected quotient-state key named through observed summary metadata. -/
def reserveStateQuotientObservedSummarySelectedKey
    (summary : ReserveStateQuotientObservedSummary) : ZeroMinEconomicKey :=
  quotientSelectedZeroMinEconomicKey summary.observedExecutedInput
    summary.observedInitialReserveOut summary.table.selected summary.table.suffix

/-- The observed summary predicate carries the original host-table predicate. -/
theorem reserveStateQuotientObservedSummary_to_hostTableValid
    (summary : ReserveStateQuotientObservedSummary)
    (hvalid : reserveStateQuotientObservedSummaryValid summary) :
    reserveStateQuotientHostTableValid summary.table := by
  exact hvalid.1

/-- Observed-summary validation endpoint.

A valid summary recovers the host-visible count and selected-state bindings,
then inherits the reserve-state quotient economic endpoint using the observed
executed-input and initial-reserve metadata. -/
theorem reserveStateQuotientObservedSummary_validates
    (summary : ReserveStateQuotientObservedSummary)
    (hvalid : reserveStateQuotientObservedSummaryValid summary) :
    summary.observedStateCount = summary.table.states.length ∧
      summary.observedSelectedReserveIn = summary.table.selected.processedReserveIn ∧
      summary.observedSelectedReserveOut = summary.table.selected.reserveOut ∧
      summary.table.packetHashBound = true ∧
      summary.table.noAuthorityEffect = true ∧
      summary.table.quotientFamilyBound = true ∧
      summary.table.selectedStateBound = true ∧
      summary.table.selected ∈ summary.table.states ∧
      zeroMinEconomicKeyDominated
        (reserveStateQuotientObservedSummaryFullKey summary)
        (reserveStateQuotientObservedSummarySelectedKey summary) ∧
      suffixExecutable summary.table.selected.processedReserveIn
        summary.table.selected.reserveOut summary.table.suffix := by
  rcases hvalid with
    ⟨htableValid, hcount, hselectedIn, hselectedOut, hexecutedInput,
      hinitialReserveOut⟩
  have hendpoint := reserveStateQuotientHostTable_validates summary.table htableValid
  rcases hendpoint with
    ⟨hhash, hnoAuthority, hfamily, hselectedBound, hselectedMem,
      hdominance, hexec⟩
  have hdominanceObserved :
      zeroMinEconomicKeyDominated
        (reserveStateQuotientObservedSummaryFullKey summary)
        (reserveStateQuotientObservedSummarySelectedKey summary) := by
    unfold reserveStateQuotientObservedSummaryFullKey
      reserveStateQuotientObservedSummarySelectedKey
    rw [hexecutedInput, hinitialReserveOut]
    exact hdominance
  exact ⟨hcount, hselectedIn, hselectedOut, hhash, hnoAuthority, hfamily,
    hselectedBound, hselectedMem, hdominanceObserved, hexec⟩

/-- Concrete non-vacuity witness for reserve-state equivalence. -/
theorem witness_reserveStateEquivalent_same_suffixOutput :
    let left : ReserveState := ⟨1000, 900⟩
    let right : ReserveState := ⟨1000, 900⟩
    let suffix : List ExactInStep := [⟨100, 99⟩]
    reserveStateEquivalent left right ∧
      finalReserveOutAfterState left suffix = finalReserveOutAfterState right suffix ∧
      stateSuffixOutput 1200 left suffix = stateSuffixOutput 1200 right suffix := by
  simp [reserveStateEquivalent, finalReserveOutAfterState, stateSuffixOutput,
    ReserveState.toRecord]

/-- Concrete non-vacuity witness for reserve-state quotient validation. -/
theorem witness_reserveStateQuotientHostTable_validates :
    let selected : ReserveState := ⟨1000, 800⟩
    let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
    let table : ReserveStateQuotientHostTable := {
      states := states
      selected := selected
      initialReserveOut := 1200
      executedInput := 100
      suffix := []
      packetHashBound := true
      noAuthorityEffect := true
      quotientFamilyBound := true
      selectedStateBound := true
    }
    reserveStateQuotientHostTableValid table ∧
      table.packetHashBound = true ∧
        table.noAuthorityEffect = true ∧
        table.quotientFamilyBound = true ∧
        table.selectedStateBound = true ∧
        table.selected ∈ table.states ∧
        zeroMinEconomicKeyDominated
          (reserveStateQuotientHostTableFullKey table)
          (reserveStateQuotientHostTableSelectedKey table) ∧
        suffixExecutable table.selected.processedReserveIn table.selected.reserveOut table.suffix := by
  let selected : ReserveState := ⟨1000, 800⟩
  let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
  let table : ReserveStateQuotientHostTable := {
    states := states
    selected := selected
    initialReserveOut := 1200
    executedInput := 100
    suffix := []
    packetHashBound := true
    noAuthorityEffect := true
    quotientFamilyBound := true
    selectedStateBound := true
  }
  have hinvariant : reserveStateQuotientInvariant selected states := by
    unfold reserveStateQuotientInvariant
    constructor
    · simp [states]
    · constructor
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          rfl
        · subst state
          rfl
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          simp [selected]
        · subst state
          simp [selected]
  have hexec :
      suffixExecutable selected.processedReserveIn selected.reserveOut [] := by
    simp [suffixExecutable]
  have hvalid : reserveStateQuotientHostTableValid table := by
    unfold reserveStateQuotientHostTableValid
    exact ⟨rfl, rfl, rfl, rfl, by simpa [table] using hinvariant,
      by simpa [table] using hexec⟩
  exact ⟨hvalid, reserveStateQuotientHostTable_validates table hvalid⟩

/-- Concrete non-vacuity witness for one-step quotient-invariant preservation. -/
theorem witness_reserveStateQuotientInvariant_afterStep :
    let selected : ReserveState := ⟨1000, 800⟩
    let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
    let step : ExactInStep := ⟨100, 99⟩
    reserveStateQuotientInvariant selected states ∧
      reserveStateQuotientInvariant
        (ReserveState.afterStep selected step)
        (states.map (fun state => ReserveState.afterStep state step)) := by
  let selected : ReserveState := ⟨1000, 800⟩
  let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
  let step : ExactInStep := ⟨100, 99⟩
  have hinvariant : reserveStateQuotientInvariant selected states := by
    unfold reserveStateQuotientInvariant
    constructor
    · simp [states]
    · constructor
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          rfl
        · subst state
          rfl
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          simp [selected]
        · subst state
          simp [selected]
  exact ⟨hinvariant,
    reserveStateQuotientInvariant_afterStep
      (selected := selected)
      (states := states)
      (step := step)
      hinvariant⟩

/-- Concrete non-vacuity witness for reserve-state observed-summary validation. -/
theorem witness_reserveStateQuotientObservedSummary_validates :
    let selected : ReserveState := ⟨1000, 800⟩
    let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
    let table : ReserveStateQuotientHostTable := {
      states := states
      selected := selected
      initialReserveOut := 1200
      executedInput := 100
      suffix := []
      packetHashBound := true
      noAuthorityEffect := true
      quotientFamilyBound := true
      selectedStateBound := true
    }
    let summary : ReserveStateQuotientObservedSummary := {
      table := table
      observedStateCount := 3
      observedSelectedReserveIn := 1000
      observedSelectedReserveOut := 800
      observedExecutedInput := 100
      observedInitialReserveOut := 1200
    }
    reserveStateQuotientObservedSummaryValid summary ∧
      summary.observedStateCount = summary.table.states.length ∧
        summary.observedSelectedReserveIn =
          summary.table.selected.processedReserveIn ∧
        summary.observedSelectedReserveOut =
          summary.table.selected.reserveOut ∧
        summary.table.packetHashBound = true ∧
        summary.table.noAuthorityEffect = true ∧
        summary.table.quotientFamilyBound = true ∧
        summary.table.selectedStateBound = true ∧
        summary.table.selected ∈ summary.table.states ∧
        zeroMinEconomicKeyDominated
          (reserveStateQuotientObservedSummaryFullKey summary)
          (reserveStateQuotientObservedSummarySelectedKey summary) ∧
        suffixExecutable summary.table.selected.processedReserveIn
          summary.table.selected.reserveOut summary.table.suffix := by
  let selected : ReserveState := ⟨1000, 800⟩
  let states : List ReserveState := [selected, ⟨1000, 900⟩, ⟨1000, 1100⟩]
  let table : ReserveStateQuotientHostTable := {
    states := states
    selected := selected
    initialReserveOut := 1200
    executedInput := 100
    suffix := []
    packetHashBound := true
    noAuthorityEffect := true
    quotientFamilyBound := true
    selectedStateBound := true
  }
  let summary : ReserveStateQuotientObservedSummary := {
    table := table
    observedStateCount := 3
    observedSelectedReserveIn := 1000
    observedSelectedReserveOut := 800
    observedExecutedInput := 100
    observedInitialReserveOut := 1200
  }
  have hinvariant : reserveStateQuotientInvariant selected states := by
    unfold reserveStateQuotientInvariant
    constructor
    · simp [states]
    · constructor
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          rfl
        · subst state
          rfl
      · intro state hstate
        simp [states] at hstate
        rcases hstate with hstate | hstate | hstate
        · subst state
          rfl
        · subst state
          simp [selected]
        · subst state
          simp [selected]
  have hexec :
      suffixExecutable selected.processedReserveIn selected.reserveOut [] := by
    simp [suffixExecutable]
  have htableValid : reserveStateQuotientHostTableValid table := by
    unfold reserveStateQuotientHostTableValid
    exact ⟨rfl, rfl, rfl, rfl, by simpa [table] using hinvariant,
      by simpa [table] using hexec⟩
  have hsummaryValid : reserveStateQuotientObservedSummaryValid summary := by
    unfold reserveStateQuotientObservedSummaryValid
    exact ⟨htableValid, by simp [summary, table, states],
      by simp [summary, table, selected], by simp [summary, table, selected],
      by simp [summary, table], by simp [summary, table]⟩
  exact ⟨hsummaryValid,
    reserveStateQuotientObservedSummary_validates summary hsummaryValid⟩

end ABReserveStateQuotient
