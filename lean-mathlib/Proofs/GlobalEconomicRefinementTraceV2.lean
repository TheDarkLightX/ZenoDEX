import Proofs.GlobalEconomicStateRefinementV2

/-!
# GlobalSettlementABI V2 finite trace composition

This file lifts the existing single-step outcome relation of
`Proofs.GlobalEconomicStateRefinementV2` to a finite history.  A `Run` is a
list of steps in which each step is exactly one `Outcome` of the existing
model and the next step starts from that outcome's `postState`.  Nothing about
the single-step relation is redefined here: accepted steps carry the same
`Verified` structure with all nineteen fields, and rejected steps use the same
`Outcome.postState`, `Outcome.effectPlan`, `Outcome.terminalPlan`,
`Outcome.oraclePlan` and `Outcome.occurrences` projections.

## What the trace theorems add

`every_run_refines` bundles the composition results:

* every committed step still carries the complete one-step `Verified` witness,
  so no conjunct of the single-step relation is dropped or weakened;
* the committed steps form one contiguous chain from the first state to the
  last, which is where the rejection no-op is used: a rejected step is
  invisible in the state chain;
* the final height equals the initial height plus the number of committed
  steps that consumed at least one occurrence;
* the replay registry only grows, so a recorded replay identifier keeps its
  recorded occurrence identifier for the rest of the history;
* no replay identifier and no occurrence identifier is consumed twice anywhere
  in the history, which is the trace form of exact-retry refusal;
* the pre-O-009 outbox stays closed on every step, accepted or rejected;
* a run with no committed step reproduces all five rejection dimensions of
  `rejected_is_no_op_bundle` at the trace level.

## Atomicity assumptions, stated explicitly

These are assumptions of the model, not results proved about any runtime.

1. **Sequential composition.**  `Run.step` forces the next step's pre-state to
   be the previous step's `Outcome.postState`.  Nothing here shows that a
   deployed writer observes that discipline, and no concurrent or interleaved
   writer is modelled.
2. **All-or-nothing steps.**  A step is one `Outcome`.  Partially applied
   state, torn writes, and crash-interrupted application are not modelled.
3. **No out-of-band mutation.**  State changes only through the steps of the
   run.  External edits between steps are outside the model.
4. **The outcome is given, not decided.**  A `Run` is built from outcome
   values.  This file does not decide which outcome an executable checker
   returns for a candidate, and it does not model checker exception classes,
   reject-code precedence, or message text.

## Claim boundary

Roots, identifiers, and registries stay abstract `String`-indexed values.  No
theorem assumes digest injectivity or collision resistance.  These theorems
establish no Python or Rust runtime refinement, no verifier, publisher,
settlement, or value-moving authority, no migration result, no release status,
and no production readiness.  They make no durability, persistence, storage
engine, or crash-recovery claim of any kind, and in particular no SQLite
claim.  They do not model what a client knows or does not know, and no
indeterminate client knowledge is represented as a rejection: rejection here
is only the existing `Outcome.rejected` constructor with its exact no-op
projections.  They do not mount a runtime route.
-/

namespace Proofs
namespace GlobalEconomicRefinementTraceV2

open GlobalSettlementCoreV2
open GlobalEconomicStateRefinementV2

/-! ## Finite histories over the existing one-step outcome -/

/-- One recovered step endpoint.  The fields are exactly the arguments of the
single-step `Verified` relation, in the same order. -/
structure Transition where
  pre : GlobalState
  effects : EffectPlan
  terminalPlan : TerminalPlan
  oraclePlan : OraclePlan
  occurrences : List CommandOccurrence
  post : GlobalState

/-- The complete single-step relation, unweakened, for a recovered step. -/
def Transition.IsVerified (transition : Transition) : Prop :=
  Verified transition.pre transition.effects transition.terminalPlan
    transition.oraclePlan transition.occurrences transition.post

/-- A finite history.  Each step is one existing `Outcome` and the next step
starts from that outcome's `postState`. -/
inductive Run : GlobalState → GlobalState → Type where
  | halt (state : GlobalState) : Run state state
  | step {pre final : GlobalState} (outcome : Outcome pre)
      (rest : Run outcome.postState final) : Run pre final

/-- The committed steps, in order.  Rejected steps contribute nothing. -/
def Run.committed : {pre final : GlobalState} → Run pre final → List Transition
  | _, _, .halt _ => []
  | pre, _, .step (.accepted accepted) rest =>
      { pre := pre
        effects := accepted.effects
        terminalPlan := accepted.terminalPlan
        oraclePlan := accepted.oraclePlan
        occurrences := accepted.occurrences
        post := accepted.post } :: rest.committed
  | _, _, .step (.rejected _) rest => rest.committed

/-- Every step's effect plan, accepted and rejected alike. -/
def Run.stepEffectPlans : {pre final : GlobalState} → Run pre final → List EffectPlan
  | _, _, .halt _ => []
  | _, _, .step outcome rest => outcome.effectPlan :: rest.stepEffectPlans

/-- Every step's terminal deltas, accepted and rejected alike. -/
def Run.stepTerminalDeltas :
    {pre final : GlobalState} → Run pre final → List TerminalDelta
  | _, _, .halt _ => []
  | _, _, .step outcome rest => outcome.terminalPlan.deltas ++ rest.stepTerminalDeltas

/-- Every step's Oracle deltas, accepted and rejected alike. -/
def Run.stepOracleDeltas :
    {pre final : GlobalState} → Run pre final → List OracleDelta
  | _, _, .halt _ => []
  | _, _, .step outcome rest => outcome.oraclePlan.deltas ++ rest.stepOracleDeltas

/-- Every occurrence consumed anywhere in the history. -/
def Run.stepOccurrences :
    {pre final : GlobalState} → Run pre final → List CommandOccurrence
  | _, _, .halt _ => []
  | _, _, .step outcome rest => outcome.occurrences ++ rest.stepOccurrences

def Run.consumedReplayIds {pre final : GlobalState} (run : Run pre final) :
    List Identifier :=
  run.committed.flatMap fun transition =>
    transition.occurrences.map (fun occurrence => occurrence.replayId)

def Run.consumedOccurrenceIds {pre final : GlobalState} (run : Run pre final) :
    List RootId :=
  run.committed.flatMap fun transition =>
    transition.occurrences.map (fun occurrence => occurrence.occurrenceId)

/-- The committed steps compose end to end, with no gap between them. -/
def Chained : GlobalState → List Transition → GlobalState → Prop
  | start, [], final => start = final
  | start, transition :: rest, final =>
      transition.pre = start ∧ Chained transition.post rest final

def Transition.advancesHeight (transition : Transition) : Bool :=
  !transition.occurrences.isEmpty

def committedHeightSteps (transitions : List Transition) : Nat :=
  (transitions.filter Transition.advancesHeight).length

theorem committedHeightSteps_cons (transition : Transition) (rest : List Transition) :
    committedHeightSteps (transition :: rest) =
      (if transition.occurrences.isEmpty then 0 else 1) + committedHeightSteps rest := by
  unfold committedHeightSteps Transition.advancesHeight
  rw [List.filter_cons]
  cases transition.occurrences.isEmpty <;> simp <;> omega

/-- Pure arithmetic of one height step against the tail count. -/
theorem height_step_arithmetic {preHeight postHeight finalHeight tailSteps : Nat}
    {noOccurrences : Bool}
    (step : postHeight = if noOccurrences then preHeight else preHeight + 1)
    (tail : finalHeight = postHeight + tailSteps) :
    finalHeight = preHeight + ((if noOccurrences then 0 else 1) + tailSteps) := by
  cases noOccurrences <;> simp only [if_true, if_false, Bool.false_eq_true] at step ⊢ <;> omega

/-! ## Single-step lemmas extracted from the existing relation -/

theorem verified_replay_registry_is_monotone
    {pre : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    {oraclePlan : OraclePlan} {occurrences : List CommandOccurrence}
    {post : GlobalState}
    (verified : Verified pre effects terminalPlan oraclePlan occurrences post)
    (replayId : Identifier) (occurrenceId : RootId)
    (recorded : pre.replayState replayId = some occurrenceId) :
    post.replayState replayId = some occurrenceId := by
  have refines := verified.replay.2.2.2.1
  by_cases untouched : ∀ occurrence ∈ occurrences, occurrence.replayId ≠ replayId
  · rw [refines.2.2 replayId untouched]
    exact recorded
  · have collided : ∃ occurrence, occurrence ∈ occurrences ∧ occurrence.replayId = replayId :=
      Classical.byContradiction fun missing =>
        untouched fun occurrence member same => missing ⟨occurrence, member, same⟩
    obtain ⟨occurrence, member, sameId⟩ := collided
    have absent := (refines.2.1 occurrence member).1
    rw [sameId] at absent
    exact absurd (absent.symm.trans recorded) (by simp)

theorem verified_records_consumed_occurrence
    {pre : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    {oraclePlan : OraclePlan} {occurrences : List CommandOccurrence}
    {post : GlobalState}
    (verified : Verified pre effects terminalPlan oraclePlan occurrences post)
    (occurrence : CommandOccurrence) (member : occurrence ∈ occurrences) :
    post.replayState occurrence.replayId = some occurrence.occurrenceId :=
  (verified.replay.2.2.2.1.2.1 occurrence member).2.1

theorem verified_consumed_replay_id_was_unset
    {pre : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    {oraclePlan : OraclePlan} {occurrences : List CommandOccurrence}
    {post : GlobalState}
    (verified : Verified pre effects terminalPlan oraclePlan occurrences post)
    (occurrence : CommandOccurrence) (member : occurrence ∈ occurrences) :
    pre.replayState occurrence.replayId = none :=
  (verified.replay.2.2.2.1.2.1 occurrence member).1

theorem verified_consumed_occurrence_id_is_fresh
    {pre : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    {oraclePlan : OraclePlan} {occurrences : List CommandOccurrence}
    {post : GlobalState}
    (verified : Verified pre effects terminalPlan oraclePlan occurrences post)
    (occurrence : CommandOccurrence) (member : occurrence ∈ occurrences)
    (replayId : Identifier) (priorOccurrenceId : RootId)
    (recorded : pre.replayState replayId = some priorOccurrenceId) :
    priorOccurrenceId ≠ occurrence.occurrenceId :=
  (verified.replay.2.2.2.1.2.1 occurrence member).2.2 replayId priorOccurrenceId recorded

theorem string_lt_implies_ne {left right : String} (ordered : left < right) :
    left ≠ right := by
  intro collision
  rw [collision] at ordered
  exact String.lt_irrefl right ordered

theorem fixedContext_refl (state : GlobalState) : FixedContext state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fixedContext_trans {first middle last : GlobalState}
    (left : FixedContext first middle) (right : FixedContext middle last) :
    FixedContext first last :=
  ⟨left.1.trans right.1, left.2.1.trans right.2.1,
    left.2.2.1.trans right.2.2.1, left.2.2.2.1.trans right.2.2.2.1,
    left.2.2.2.2.1.trans right.2.2.2.2.1,
    left.2.2.2.2.2.1.trans right.2.2.2.2.2.1,
    left.2.2.2.2.2.2.1.trans right.2.2.2.2.2.2.1,
    left.2.2.2.2.2.2.2.trans right.2.2.2.2.2.2.2⟩

/-! ## Trace composition -/

/-- Every committed step still carries the complete single-step witness. -/
theorem run_committed_transitions_are_verified :
    ∀ {pre final : GlobalState} (run : Run pre final),
      ∀ transition ∈ run.committed, transition.IsVerified
  | _, _, .halt _ => by intro transition member; cases member
  | _, _, .step (.accepted accepted) rest => by
      intro transition member
      rcases List.mem_cons.mp member with head | tail
      · subst head; exact accepted.verified
      · exact run_committed_transitions_are_verified rest transition tail
  | _, _, .step (.rejected _) rest => run_committed_transitions_are_verified rest

/-- The committed steps form one contiguous chain from the first state to the
last.  Rejected steps leave no gap because their post-state is their
pre-state. -/
theorem run_committed_transitions_chain :
    ∀ {pre final : GlobalState} (run : Run pre final),
      Chained pre run.committed final
  | _, _, .halt _ => rfl
  | _, _, .step (.accepted _) rest =>
      ⟨rfl, run_committed_transitions_chain rest⟩
  | _, _, .step (.rejected _) rest => run_committed_transitions_chain rest

theorem run_preserves_fixed_context :
    ∀ {pre final : GlobalState}, Run pre final → FixedContext pre final
  | state, _, .halt _ => fixedContext_refl state
  | _, _, .step (.accepted accepted) rest =>
      fixedContext_trans accepted.verified.fixedContext
        (run_preserves_fixed_context rest)
  | _, _, .step (.rejected _) rest => run_preserves_fixed_context rest

/-- The final height is the initial height plus the number of committed steps
that consumed at least one occurrence. -/
theorem run_height_counts_committed_advancing_steps :
    ∀ {pre final : GlobalState} (run : Run pre final),
      final.height = pre.height + committedHeightSteps run.committed
  | _, _, .halt _ => by simp [committedHeightSteps, Run.committed]
  | pre, _, .step (.accepted accepted) rest => by
      have stepHeight := accepted.verified.replay.2.2.2.2.1
      have tail := run_height_counts_committed_advancing_steps rest
      have unfoldCommitted :
          (Run.step (Outcome.accepted accepted) rest).committed =
            { pre := pre
              effects := accepted.effects
              terminalPlan := accepted.terminalPlan
              oraclePlan := accepted.oraclePlan
              occurrences := accepted.occurrences
              post := accepted.post } :: rest.committed := rfl
      rw [unfoldCommitted, committedHeightSteps_cons]
      exact height_step_arithmetic stepHeight tail
  | _, _, .step (.rejected _) rest =>
      run_height_counts_committed_advancing_steps rest

/-- A recorded replay identifier keeps its recorded occurrence identifier for
the rest of the history. -/
theorem run_replay_registry_is_monotone :
    ∀ {pre final : GlobalState}, Run pre final →
      ∀ (replayId : Identifier) (occurrenceId : RootId),
        pre.replayState replayId = some occurrenceId →
          final.replayState replayId = some occurrenceId
  | _, _, .halt _ => fun _ _ recorded => recorded
  | _, _, .step (.accepted accepted) rest => fun replayId occurrenceId recorded =>
      run_replay_registry_is_monotone rest replayId occurrenceId
        (verified_replay_registry_is_monotone accepted.verified replayId
          occurrenceId recorded)
  | _, _, .step (.rejected _) rest => run_replay_registry_is_monotone rest

/-- Every replay identifier consumed anywhere in the history was unset at the
first state of the history. -/
theorem run_consumed_replay_ids_start_unset :
    ∀ {pre final : GlobalState} (run : Run pre final),
      ∀ transition ∈ run.committed, ∀ occurrence ∈ transition.occurrences,
        pre.replayState occurrence.replayId = none
  | _, _, .halt _ => by intro transition member; cases member
  | pre, _, .step (.accepted accepted) rest => by
      intro transition member occurrence occurrenceMember
      rcases List.mem_cons.mp member with head | tail
      · subst head
        exact verified_consumed_replay_id_was_unset accepted.verified occurrence
          occurrenceMember
      · have tailUnset :=
          run_consumed_replay_ids_start_unset rest transition tail occurrence
            occurrenceMember
        cases before : pre.replayState occurrence.replayId with
        | none => rfl
        | some priorOccurrenceId =>
            have carried :=
              verified_replay_registry_is_monotone accepted.verified
                occurrence.replayId priorOccurrenceId before
            exact absurd (carried.symm.trans tailUnset) (by simp)
  | _, _, .step (.rejected _) rest => run_consumed_replay_ids_start_unset rest

/-- No occurrence identifier consumed anywhere in the history was already
recorded in the first state of the history. -/
theorem run_consumed_occurrence_ids_are_fresh_at_start :
    ∀ {pre final : GlobalState} (run : Run pre final),
      ∀ transition ∈ run.committed, ∀ occurrence ∈ transition.occurrences,
        ∀ (replayId : Identifier) (priorOccurrenceId : RootId),
          pre.replayState replayId = some priorOccurrenceId →
            priorOccurrenceId ≠ occurrence.occurrenceId
  | _, _, .halt _ => by intro transition member; cases member
  | _, _, .step (.accepted accepted) rest => by
      intro transition member occurrence occurrenceMember replayId
        priorOccurrenceId recorded
      rcases List.mem_cons.mp member with head | tail
      · subst head
        exact verified_consumed_occurrence_id_is_fresh accepted.verified occurrence
          occurrenceMember replayId priorOccurrenceId recorded
      · exact run_consumed_occurrence_ids_are_fresh_at_start rest transition tail
          occurrence occurrenceMember replayId priorOccurrenceId
          (verified_replay_registry_is_monotone accepted.verified replayId
            priorOccurrenceId recorded)
  | _, _, .step (.rejected _) rest =>
      run_consumed_occurrence_ids_are_fresh_at_start rest

/-- Exact-retry refusal at trace level: no replay identifier is consumed twice
anywhere in the history. -/
theorem run_consumes_each_replay_id_at_most_once :
    ∀ {pre final : GlobalState} (run : Run pre final),
      run.consumedReplayIds.Nodup
  | _, _, .halt _ => by simp [Run.consumedReplayIds, Run.committed]
  | _, _, .step (.accepted accepted) rest => by
      simp only [Run.consumedReplayIds, Run.committed, List.flatMap_cons] at *
      refine List.nodup_append.mpr ⟨accepted.verified.replay.2.2.2.1.1, ?_, ?_⟩
      · exact run_consumes_each_replay_id_at_most_once rest
      · intro left leftMember right rightMember
        obtain ⟨occurrence, occurrenceMember, leftValue⟩ := List.mem_map.mp leftMember
        obtain ⟨transition, transitionMember, rightSource⟩ :=
          List.mem_flatMap.mp rightMember
        obtain ⟨laterOccurrence, laterMember, rightValue⟩ := List.mem_map.mp rightSource
        subst leftValue
        subst rightValue
        intro collision
        have recorded :=
          verified_records_consumed_occurrence accepted.verified occurrence
            occurrenceMember
        have unset : accepted.post.replayState laterOccurrence.replayId = none :=
          run_consumed_replay_ids_start_unset rest transition transitionMember
            laterOccurrence laterMember
        rw [collision] at recorded
        exact absurd (recorded.symm.trans unset) (by simp)
  | _, _, .step (.rejected _) rest => run_consumes_each_replay_id_at_most_once rest

/-- No occurrence identifier is consumed twice anywhere in the history. -/
theorem run_consumes_each_occurrence_id_at_most_once :
    ∀ {pre final : GlobalState} (run : Run pre final),
      run.consumedOccurrenceIds.Nodup
  | _, _, .halt _ => by simp [Run.consumedOccurrenceIds, Run.committed]
  | _, _, .step (.accepted accepted) rest => by
      simp only [Run.consumedOccurrenceIds, Run.committed, List.flatMap_cons] at *
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · exact List.Pairwise.imp string_lt_implies_ne accepted.verified.replay.1
      · exact run_consumes_each_occurrence_id_at_most_once rest
      · intro left leftMember right rightMember
        obtain ⟨occurrence, occurrenceMember, leftValue⟩ := List.mem_map.mp leftMember
        obtain ⟨transition, transitionMember, rightSource⟩ :=
          List.mem_flatMap.mp rightMember
        obtain ⟨laterOccurrence, laterMember, rightValue⟩ := List.mem_map.mp rightSource
        subst leftValue
        subst rightValue
        exact run_consumed_occurrence_ids_are_fresh_at_start rest transition
          transitionMember laterOccurrence laterMember occurrence.replayId
          occurrence.occurrenceId
          (verified_records_consumed_occurrence accepted.verified occurrence
            occurrenceMember)
  | _, _, .step (.rejected _) rest =>
      run_consumes_each_occurrence_id_at_most_once rest

/-- The pre-O-009 outbox stays closed on every step of the history. -/
theorem run_keeps_outbox_closed_before_o009 :
    ∀ {pre final : GlobalState} (run : Run pre final),
      ∀ plan ∈ run.stepEffectPlans, plan.externalOutboxEnqueue = []
  | _, _, .halt _ => by intro plan member; cases member
  | _, _, .step (.accepted accepted) rest => by
      intro plan member
      rcases List.mem_cons.mp member with head | tail
      · subst head; exact accepted.verified.outboxClosed
      · exact run_keeps_outbox_closed_before_o009 rest plan tail
  | _, _, .step (.rejected _) rest => by
      intro plan member
      rcases List.mem_cons.mp member with head | tail
      · subst head; rfl
      · exact run_keeps_outbox_closed_before_o009 rest plan tail

/-- A committed step that consumed no occurrence is completely static, exactly
as in the single-step statement. -/
theorem run_committed_step_without_occurrences_is_static
    {pre final : GlobalState} (run : Run pre final) :
    ∀ transition ∈ run.committed, transition.occurrences = [] →
      transition.effects.IsEmpty ∧
      transition.terminalPlan.deltas = [] ∧
      transition.oraclePlan.deltas = [] ∧
      transition.pre = transition.post := by
  intro transition member zero
  exact (run_committed_transitions_are_verified run transition member).zeroOccurrence zero

/-- Trace form of `rejected_is_no_op_bundle`, keeping all five dimensions: a
history with no committed step changes no state, plans nothing, and consumes
nothing. -/
theorem run_without_committed_steps_is_complete_no_op :
    ∀ {pre final : GlobalState} (run : Run pre final), run.committed = [] →
      final = pre ∧
      (∀ plan ∈ run.stepEffectPlans, plan.IsEmpty) ∧
      run.stepTerminalDeltas = [] ∧
      run.stepOracleDeltas = [] ∧
      run.stepOccurrences = []
  | _, _, .halt _ => by
      intro _
      refine ⟨rfl, ?_, rfl, rfl, rfl⟩
      intro plan member
      cases member
  | _, _, .step (.accepted _) _ => by
      intro empty
      simp [Run.committed] at empty
  | _, _, .step (.rejected code) rest => by
      intro empty
      obtain ⟨state, plans, terminal, oracle, occurrences⟩ :=
        run_without_committed_steps_is_complete_no_op rest empty
      have unfoldTerminal :
          (Run.step (Outcome.rejected code) rest).stepTerminalDeltas =
            rest.stepTerminalDeltas := rfl
      have unfoldOracle :
          (Run.step (Outcome.rejected code) rest).stepOracleDeltas =
            rest.stepOracleDeltas := rfl
      have unfoldOccurrences :
          (Run.step (Outcome.rejected code) rest).stepOccurrences =
            rest.stepOccurrences := rfl
      refine ⟨state, ?_, ?_, ?_, ?_⟩
      · intro plan member
        rcases List.mem_cons.mp member with head | tail
        · subst head; exact effectPlan_empty_has_six_empty_fields
        · exact plans plan tail
      · rw [unfoldTerminal, terminal]
      · rw [unfoldOracle, oracle]
      · rw [unfoldOccurrences, occurrences]

/-! ## State invariants carried across the history -/

theorem run_preserves_state_quantities :
    ∀ {pre final : GlobalState}, Run pre final →
      StateQuantitiesAdmitted pre → StateQuantitiesAdmitted final
  | _, _, .halt _ => fun admitted => admitted
  | _, _, .step (.accepted accepted) rest => fun _ =>
      run_preserves_state_quantities rest accepted.verified.postQuantities
  | _, _, .step (.rejected _) rest => run_preserves_state_quantities rest

theorem run_preserves_owned_supply :
    ∀ {pre final : GlobalState}, Run pre final →
      OwnedMatchesSupply pre → OwnedMatchesSupply final
  | _, _, .halt _ => fun matched => matched
  | _, _, .step (.accepted accepted) rest => fun _ =>
      run_preserves_owned_supply rest accepted.verified.ownedSupplyPost
  | _, _, .step (.rejected _) rest => run_preserves_owned_supply rest

theorem run_preserves_liability_backing :
    ∀ {pre final : GlobalState}, Run pre final →
      ClaimantLiabilitiesBacked pre → ClaimantLiabilitiesBacked final
  | _, _, .halt _ => fun backed => backed
  | _, _, .step (.accepted accepted) rest => fun _ =>
      run_preserves_liability_backing rest accepted.verified.liabilitiesPost
  | _, _, .step (.rejected _) rest => run_preserves_liability_backing rest

theorem run_keeps_oracles_within_global_height
    {pre final : GlobalState} (run : Run pre final)
    (admitted : StateQuantitiesAdmitted pre) :
    OracleRegistryWithinGlobalHeight final := by
  rcases run_preserves_state_quantities run admitted with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, oracleAdmitted⟩
  exact oracleAdmitted.1

/-! ## Bundled trace refinement -/

structure TraceRefines {pre final : GlobalState} (run : Run pre final) : Prop where
  committedVerified : ∀ transition ∈ run.committed, transition.IsVerified
  committedChain : Chained pre run.committed final
  fixedContext : FixedContext pre final
  heightAccounting : final.height = pre.height + committedHeightSteps run.committed
  replayMonotone : ∀ (replayId : Identifier) (occurrenceId : RootId),
    pre.replayState replayId = some occurrenceId →
      final.replayState replayId = some occurrenceId
  replayIdsConsumedOnce : run.consumedReplayIds.Nodup
  occurrenceIdsConsumedOnce : run.consumedOccurrenceIds.Nodup
  outboxClosed : ∀ plan ∈ run.stepEffectPlans, plan.externalOutboxEnqueue = []
  zeroOccurrenceStatic : ∀ transition ∈ run.committed, transition.occurrences = [] →
    transition.effects.IsEmpty ∧
    transition.terminalPlan.deltas = [] ∧
    transition.oraclePlan.deltas = [] ∧
    transition.pre = transition.post
  uncommittedIsCompleteNoOp : run.committed = [] →
    final = pre ∧
    (∀ plan ∈ run.stepEffectPlans, plan.IsEmpty) ∧
    run.stepTerminalDeltas = [] ∧
    run.stepOracleDeltas = [] ∧
    run.stepOccurrences = []

theorem every_run_refines {pre final : GlobalState} (run : Run pre final) :
    TraceRefines run where
  committedVerified := run_committed_transitions_are_verified run
  committedChain := run_committed_transitions_chain run
  fixedContext := run_preserves_fixed_context run
  heightAccounting := run_height_counts_committed_advancing_steps run
  replayMonotone := run_replay_registry_is_monotone run
  replayIdsConsumedOnce := run_consumes_each_replay_id_at_most_once run
  occurrenceIdsConsumedOnce := run_consumes_each_occurrence_id_at_most_once run
  outboxClosed := run_keeps_outbox_closed_before_o009 run
  zeroOccurrenceStatic := run_committed_step_without_occurrences_is_static run
  uncommittedIsCompleteNoOp := run_without_committed_steps_is_complete_no_op run

/-! ## Concrete non-vacuity witnesses

`staticAccepted` of the single-step file consumes no occurrence, so it alone
cannot show that the height, replay, and uniqueness results say anything.  The
witness below is an accepted step that actually consumes one occurrence and
advances the height. -/

def committingOccurrence : CommandOccurrence where
  occurrenceId := "occurrence-1"
  replayId := "replay-1"
  chainId := "chain"
  deploymentRoot := "deployment-root"
  profileRoot := "profile-root"
  preStateRoot := "state-root"
  height := 1

def committingEffects : EffectPlan :=
  { EffectPlan.empty with occurrenceConsumptions := ["occurrence-1"] }

def committingPostState : GlobalState :=
  { staticGlobalState with
    stateRoot := "state-root-1"
    height := 1
    replayState := fun replayId =>
      if replayId = "replay-1" then some "occurrence-1" else none }

theorem committing_post_state_quantities_admitted :
    StateQuantitiesAdmitted committingPostState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zero_fits_u64
  · have oneFits : FitsU64 1 := by unfold FitsU64 maxU64; omega
    exact oneFits
  all_goals
    first
      | (intro replayIdLeft replayIdRight occurrenceId leftLookup rightLookup
         simp only [committingPostState] at leftLookup rightLookup
         by_cases leftKey : replayIdLeft = "replay-1"
         · by_cases rightKey : replayIdRight = "replay-1"
           · rw [leftKey, rightKey]
           · simp [rightKey] at rightLookup)
      | (simp [committingPostState, staticGlobalState, SparseAmountRowsAdmitted,
          SparseSupplyRowsAdmitted, ownedFor, liabilityFor, amountForAsset, supplyFor,
          TerminalObligationAdmitted, OracleRegistryAdmitted,
          OracleRegistryWithinGlobalHeight, OracleRegistryKeysMatch, zero_fits_u128])
  · simp [leftKey] at leftLookup

theorem committing_step_verified :
    Verified staticGlobalState committingEffects staticTerminalPlan staticOraclePlan
      [committingOccurrence] committingPostState := by
  refine {
    fixedContext := ?_,
    preQuantities := static_global_state_quantities_admitted,
    postQuantities := committing_post_state_quantities_admitted,
    effectPlan := ?_,
    laneWrites := ?_,
    economicTables := ?_,
    supplyEffects := ?_,
    conservationCoverage := ?_,
    conservationRows := ?_,
    annotations := ?_,
    ownedSupplyPre := ?_,
    ownedSupplyPost := ?_,
    liabilitiesPre := ?_,
    liabilitiesPost := ?_,
    terminal := ?_,
    oracle := ?_,
    replay := ?_,
    outboxClosed := ?_,
    zeroOccurrence := ?_ }
  · simp [FixedContext, committingPostState, staticGlobalState]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [committingEffects, EffectPlan.empty]
    · simp [committingEffects, EffectPlan.empty]
    · simp [committingEffects, EffectPlan.empty]
    · intro asset
      simp [committingEffects, EffectPlan.empty, declaredIssueFor, declaredBurnFor,
        issuedFor, burnedFor]
    · intro asset
      simp [committingEffects, EffectPlan.empty, declaredCurrentAllocationsFor,
        allocatedFeeFor]
    · simp [PlanWithinItemBounds, committingEffects, EffectPlan.empty]
    · simp [PlanKeysUnique, committingEffects, EffectPlan.empty]
  · simp [ExactLaneWrites, LaneWrittenBy, committingEffects, EffectPlan.empty,
      committingPostState, staticGlobalState]
  · simp [ExactEconomicTables, ExactTableEffect, amountAt, effectFor,
      committingPostState, staticGlobalState, committingEffects, EffectPlan.empty]
  · simp [ExactSupplyEffects, supplyFor, issueDeltaFor, burnDeltaFor, issuedFor,
      burnedFor, committingPostState, staticGlobalState, committingEffects,
      EffectPlan.empty]
  · simp [ExactConservationCoverage, EconomicAssetTouched, amountAt, supplyFor,
      committingPostState, staticGlobalState, committingEffects, EffectPlan.empty]
  · simp [ConservationRowsMatchState, committingEffects, EffectPlan.empty]
  · simp [AnnotationMirrors, StateBearingAggregatesFitI128, RunningTotalsFitI128,
      FeeAllocationCreditsMirrored, RewardSlashMirrored, FeeRowsCanonical,
      FeeResidueExact, positiveDesignatedResidueFor, positiveCarriedResidueFor,
      committingEffects, EffectPlan.empty]
  · simp [OwnedMatchesSupply, ownedFor, amountForAsset, supplyFor, staticGlobalState]
  · simp [OwnedMatchesSupply, ownedFor, amountForAsset, supplyFor, committingPostState,
      staticGlobalState]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      amountForAssetDomain, openTerminalAmountFor, amountAt, staticGlobalState]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      amountForAssetDomain, openTerminalAmountFor, amountAt, committingPostState,
      staticGlobalState]
  · simp [ExactTerminalRefinement, TerminalRegistryRefines, terminalLookup,
      TerminalOwningLaneWrites, TerminalLiabilityEffects,
      TerminalLiabilityAggregatesFitI128, RunningTotalsFitI128,
      terminalLiabilityDeltaFor, effectFor, committingPostState, staticGlobalState,
      staticTerminalPlan, committingEffects, EffectPlan.empty]
  · simp [ExactOracleRefinement, OracleRegistryRefines, OracleLaneWrite,
      committingPostState, staticGlobalState, staticOraclePlan, committingEffects,
      EffectPlan.empty]
  · refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [OrderedOccurrenceIds]
    · simp [OccurrenceContextMatches, committingOccurrence, staticGlobalState]
    · simp [committingOccurrence]
    · intro occurrence member
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨rfl, by simp [committingPostState, committingOccurrence],
        by intro replayId priorOccurrenceId recorded; simp [staticGlobalState] at recorded⟩
    · intro replayId untouched
      have distinct : ¬ replayId = "replay-1" := by
        intro collision
        exact untouched committingOccurrence (by simp) (by simp [committingOccurrence, collision])
      simp [committingPostState, staticGlobalState, distinct]
    · simp [committingPostState, staticGlobalState]
    · have oneFits : FitsU64 1 := by unfold FitsU64 maxU64; omega
      exact oneFits
    · simp [committingOccurrence, committingPostState]
  · rfl
  · intro zero
    simp at zero

def committingAccepted : Accepted staticGlobalState where
  effects := committingEffects
  terminalPlan := staticTerminalPlan
  oraclePlan := staticOraclePlan
  occurrences := [committingOccurrence]
  post := committingPostState
  verified := committing_step_verified

/-- A three-step history: one rejection, one accepted static step, and one
accepted step that consumes an occurrence and advances the height. -/
def witnessRun : Run staticGlobalState committingPostState :=
  .step (.rejected .replayMismatch)
    (.step (.accepted staticAccepted)
      (.step (.accepted committingAccepted) (.halt committingPostState)))

theorem witness_run_has_three_steps_and_two_committed :
    witnessRun.committed.length = 2 := rfl

theorem witness_run_advances_height_exactly_once :
    committedHeightSteps witnessRun.committed = 1 := rfl

theorem witness_run_consumes_one_replay_id :
    witnessRun.consumedReplayIds = ["replay-1"] := rfl

theorem witness_run_consumes_one_occurrence_id :
    witnessRun.consumedOccurrenceIds = ["occurrence-1"] := rfl

theorem witness_run_height_accounting_is_nonvacuous :
    committingPostState.height =
      staticGlobalState.height + committedHeightSteps witnessRun.committed :=
  run_height_counts_committed_advancing_steps witnessRun

/-! ## Observable projection of a history

A deployed writer cannot hand Lean a `Verified` witness, but it can report,
for each step, the pre and post state root, the pre and post height, whether
the step committed, and which replay and occurrence identifiers it consumed.
`observedTraceOk` is a decision procedure over exactly that record, and
`run_observation_is_ok` proves that the observation of every model run passes
it.  A recorded history that fails `observedTraceOk` therefore cannot be the
observation of any run of this model.  The converse does not hold: passing is
a necessary condition, not a refinement proof. -/

structure ObservedStep where
  preStateRoot : RootId
  postStateRoot : RootId
  preHeight : Nat
  postHeight : Nat
  committed : Bool
  replayIds : List Identifier
  occurrenceIds : List RootId
  deriving DecidableEq, Repr

def Run.observe : {pre final : GlobalState} → Run pre final → List ObservedStep
  | _, _, .halt _ => []
  | pre, _, .step (.accepted accepted) rest =>
      { preStateRoot := pre.stateRoot
        postStateRoot := accepted.post.stateRoot
        preHeight := pre.height
        postHeight := accepted.post.height
        committed := true
        replayIds := accepted.occurrences.map (fun occurrence => occurrence.replayId)
        occurrenceIds :=
          accepted.occurrences.map (fun occurrence => occurrence.occurrenceId) } ::
        rest.observe
  | pre, _, .step (.rejected _) rest =>
      { preStateRoot := pre.stateRoot
        postStateRoot := pre.stateRoot
        preHeight := pre.height
        postHeight := pre.height
        committed := false
        replayIds := []
        occurrenceIds := [] } :: rest.observe

theorem observe_accepted {pre final : GlobalState} (accepted : Accepted pre)
    (rest : Run (Outcome.accepted accepted).postState final) :
    (Run.step (Outcome.accepted accepted) rest).observe =
      { preStateRoot := pre.stateRoot
        postStateRoot := accepted.post.stateRoot
        preHeight := pre.height
        postHeight := accepted.post.height
        committed := true
        replayIds := accepted.occurrences.map (fun occurrence => occurrence.replayId)
        occurrenceIds :=
          accepted.occurrences.map (fun occurrence => occurrence.occurrenceId) } ::
        rest.observe := rfl

theorem observe_rejected {pre final : GlobalState} (code : RejectCode)
    (rest : Run (Outcome.rejected code : Outcome pre).postState final) :
    (Run.step (Outcome.rejected code) rest).observe =
      { preStateRoot := pre.stateRoot
        postStateRoot := pre.stateRoot
        preHeight := pre.height
        postHeight := pre.height
        committed := false
        replayIds := []
        occurrenceIds := [] } :: rest.observe := rfl

theorem committed_accepted {pre final : GlobalState} (accepted : Accepted pre)
    (rest : Run (Outcome.accepted accepted).postState final) :
    (Run.step (Outcome.accepted accepted) rest).committed =
      { pre := pre
        effects := accepted.effects
        terminalPlan := accepted.terminalPlan
        oraclePlan := accepted.oraclePlan
        occurrences := accepted.occurrences
        post := accepted.post } :: rest.committed := rfl

theorem committed_rejected {pre final : GlobalState} (code : RejectCode)
    (rest : Run (Outcome.rejected code : Outcome pre).postState final) :
    (Run.step (Outcome.rejected code) rest).committed = rest.committed := rfl

def observedStepOk (step : ObservedStep) : Bool :=
  (step.replayIds.length == step.occurrenceIds.length) &&
  (if step.committed then
      (if step.replayIds.isEmpty then
          (step.postStateRoot == step.preStateRoot) && (step.postHeight == step.preHeight)
        else step.postHeight == step.preHeight + 1)
    else
      (step.postStateRoot == step.preStateRoot) && (step.postHeight == step.preHeight) &&
        step.replayIds.isEmpty && step.occurrenceIds.isEmpty)

def observedChained :
    RootId → Nat → List ObservedStep → RootId → Nat → Bool
  | root, height, [], finalRoot, finalHeight =>
      (root == finalRoot) && (height == finalHeight)
  | root, height, step :: rest, finalRoot, finalHeight =>
      (step.preStateRoot == root) && (step.preHeight == height) &&
        observedChained step.postStateRoot step.postHeight rest finalRoot finalHeight

def observedAdvancingSteps (steps : List ObservedStep) : Nat :=
  (steps.filter fun step => !step.replayIds.isEmpty).length

def observedTraceOk (root : RootId) (height : Nat) (steps : List ObservedStep)
    (finalRoot : RootId) (finalHeight : Nat) : Bool :=
  steps.all observedStepOk &&
  observedChained root height steps finalRoot finalHeight &&
  decide (steps.flatMap (fun step => step.replayIds)).Nodup &&
  decide (steps.flatMap (fun step => step.occurrenceIds)).Nodup &&
  (finalHeight == height + observedAdvancingSteps steps)

theorem verified_observed_step_ok
    {pre : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    {oraclePlan : OraclePlan} {occurrences : List CommandOccurrence}
    {post : GlobalState}
    (verified : Verified pre effects terminalPlan oraclePlan occurrences post) :
    observedStepOk
      { preStateRoot := pre.stateRoot
        postStateRoot := post.stateRoot
        preHeight := pre.height
        postHeight := post.height
        committed := true
        replayIds := occurrences.map (fun occurrence => occurrence.replayId)
        occurrenceIds :=
          occurrences.map (fun occurrence => occurrence.occurrenceId) } = true := by
  have stepHeight := verified.replay.2.2.2.2.1
  cases occurrences with
  | nil =>
      obtain ⟨_, _, _, same⟩ := verified.zeroOccurrence rfl
      simp [observedStepOk, same]
  | cons head tail =>
      simp only [List.isEmpty_cons, List.map_cons] at stepHeight ⊢
      simp [observedStepOk, stepHeight]

theorem run_observation_step_lists_agree :
    ∀ {pre final : GlobalState} (run : Run pre final),
      run.observe.flatMap (fun step => step.replayIds) = run.consumedReplayIds ∧
      run.observe.flatMap (fun step => step.occurrenceIds) = run.consumedOccurrenceIds ∧
      observedAdvancingSteps run.observe = committedHeightSteps run.committed
  | _, _, .halt _ => ⟨rfl, rfl, rfl⟩
  | _, _, .step (.accepted accepted) rest => by
      obtain ⟨replayIds, occurrenceIds, advancing⟩ := run_observation_step_lists_agree rest
      refine ⟨?_, ?_, ?_⟩
      · rw [Run.consumedReplayIds, observe_accepted, committed_accepted,
          List.flatMap_cons, List.flatMap_cons]
        rw [← Run.consumedReplayIds, replayIds]
      · rw [Run.consumedOccurrenceIds, observe_accepted, committed_accepted,
          List.flatMap_cons, List.flatMap_cons]
        rw [← Run.consumedOccurrenceIds, occurrenceIds]
      · simp only [observedAdvancingSteps] at advancing ⊢
        rw [observe_accepted, committed_accepted, List.filter_cons,
          committedHeightSteps_cons]
        cases accepted.occurrences <;> simp [advancing] <;> omega
  | _, _, .step (.rejected code) rest => by
      obtain ⟨replayIds, occurrenceIds, advancing⟩ := run_observation_step_lists_agree rest
      refine ⟨?_, ?_, ?_⟩
      · rw [Run.consumedReplayIds, observe_rejected, committed_rejected,
          List.flatMap_cons]
        rw [← Run.consumedReplayIds, replayIds, List.nil_append]
      · rw [Run.consumedOccurrenceIds, observe_rejected, committed_rejected,
          List.flatMap_cons]
        rw [← Run.consumedOccurrenceIds, occurrenceIds, List.nil_append]
      · simp only [observedAdvancingSteps] at advancing ⊢
        rw [observe_rejected, committed_rejected, List.filter_cons]
        simpa using advancing

theorem run_observation_steps_are_ok :
    ∀ {pre final : GlobalState} (run : Run pre final),
      run.observe.all observedStepOk = true
  | _, _, .halt _ => rfl
  | _, _, .step (.accepted accepted) rest => by
      rw [observe_accepted, List.all_cons, run_observation_steps_are_ok rest,
        verified_observed_step_ok accepted.verified]
      rfl
  | _, _, .step (.rejected code) rest => by
      rw [observe_rejected, List.all_cons, run_observation_steps_are_ok rest]
      simp [observedStepOk]

theorem run_observation_is_chained :
    ∀ {pre final : GlobalState} (run : Run pre final),
      observedChained pre.stateRoot pre.height run.observe final.stateRoot
        final.height = true
  | _, _, .halt _ => by simp [Run.observe, observedChained]
  | _, _, .step (.accepted accepted) rest => by
      rw [observe_accepted, observedChained]
      simpa using run_observation_is_chained rest
  | _, _, .step (.rejected code) rest => by
      rw [observe_rejected, observedChained]
      simpa using run_observation_is_chained rest

/-- The observation of every run of this model passes `observedTraceOk`. -/
theorem run_observation_is_ok {pre final : GlobalState} (run : Run pre final) :
    observedTraceOk pre.stateRoot pre.height run.observe final.stateRoot
      final.height = true := by
  obtain ⟨replayIds, occurrenceIds, advancing⟩ := run_observation_step_lists_agree run
  unfold observedTraceOk
  rw [run_observation_steps_are_ok run, run_observation_is_chained run, replayIds,
    occurrenceIds, advancing]
  rw [decide_eq_true (run_consumes_each_replay_id_at_most_once run),
    decide_eq_true (run_consumes_each_occurrence_id_at_most_once run),
    run_height_counts_committed_advancing_steps run]
  simp

theorem witness_run_observation_is_ok :
    observedTraceOk staticGlobalState.stateRoot staticGlobalState.height
      witnessRun.observe committingPostState.stateRoot committingPostState.height = true :=
  run_observation_is_ok witnessRun

end GlobalEconomicRefinementTraceV2
end Proofs
