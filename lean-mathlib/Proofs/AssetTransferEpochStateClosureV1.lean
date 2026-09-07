import Proofs.AssetTransferGlobalStateClosureV1

/-!
# Shared-height epoch continuation of the restricted custody transfer

`AssetTransferGlobalSuccessorV1` advances the global height once per standalone
transfer and `AssetTransferGlobalStateClosureV1` composes those standalone
transfers.  The actual epoch allocation admission
(`_epoch_allocation_binding_reject_v1`) instead binds every command and every
successor of one epoch to the single target height `H + 1` of the certified
source `H`: the first predecessor is the source itself at height `H`, every later
predecessor is the previous prospective disclosure at height `H + 1`.

This file builds that continuation explicitly.  `epochSuccessor` carries the
actual custody-complete post economic tables (`AssetTransferCustodyEffectPlanV1.complete`)
with exactly four metadata changes: the opaque post state root, the occurrence
height (the shared target), the changed asset lane root and one replay
insertion.  `epochStep` and `epochContinuedState` branch only on the actual leaf
verdict.  `EpochRequirements` is a predicate on the inputs alone: the certified
carried state, the source/position binding, the same context, the bounded index,
the u64 target, the predecessor height by index, the occurrence at the target,
replay-key and occurrence-identity freshness, the private pre root, the distinct
post commitment, command bounds and the existing fee eligibility.  No desired
post row, no `StateInvariant` of the output, no `Verified` and no per-step
preservation oracle is a premise.

## What is proved

- an accepted attempt yields the actual completed economic tables with only the
  four metadata changes, the shared target height, the exact replay insertion
  and the other-key frame, and the nine inherited state obligations of
  `AssetTransferGlobalStateClosureV1.StateInvariant`;
- `SharedHeightVerified` restates the eighteen clauses of the existing
  `Verified` record other than `ExactReplayRefinement` verbatim on the
  shared-height successor (its `postQuantities` clause reads the successor
  height through the u64 bound and the Oracle height bound and is discharged
  from the u64 target and height monotonicity), and replaces
  `ExactReplayRefinement` by its order, consumption, context and registry
  clauses together with the shared target height, its u64 bound and the
  occurrence height binding.  It is deliberately not `Verified`:
  `ExactReplayRefinement` forces `post.height = pre.height + 1`, which is the
  standalone one-step law and is false at every later epoch position.  Neither
  `Verified` nor the standalone theorem is weakened here;
- at the first position the constructed successor is exactly the standalone
  successor, so the existing `Verified` record follows by reuse;
- a rejected leaf retains the exact carried state, the empty plan and no
  occurrence;
- `EpochPrefix` chains admitted accepted attempts from a certified source with
  index equal to the number of earlier accepted attempts.  Invariant
  preservation, the shared height, the fixed context, the static module frame,
  the exact replay fold and the prefix length bound `0..64` are derived by
  induction.  A nonempty prefix has `1..64` accepted attempts and carries the
  shared target height (`epochPrefix_nonempty`); the runtime requires that
  nonempty range for a published epoch, while the empty prefix is the source
  itself.

## What is not proved

A rejected attempt extends no chain; the runtime fold aborts the whole epoch on
its first rejected pair.  The carried-state relation grants no authority to
publish any intermediate or final state: whether an epoch is published is
decided by the runtime checker, certificate and publisher, none of which is
modelled here.  Whole-epoch publication, the certificate, receipts,
authenticated snapshots, aggregate authorization, atomicity of the runtime fold,
`CheckedEpochEconomicTablesV1` table telescoping, an epoch-level `Verified`
record and any Python/Rust refinement remain external.  Roots and identities
are opaque strings and authenticity is external.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferEpochStateClosureV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace X
export AssetTransferGlobalSuccessorV1
  (Input Admitted Result pre fields result result_verdict result_post result_post_frame
   result_reserves result_terminal result_liabilities result_height result_accepted_plan_fields
   successor successorRoots successorRoots_self successorRoots_other insertReplay
   insertReplay_self insertReplay_other insertReplay_injective quantities_transport
   successor_verified successor_fixed_context successor_oracle SingleEnabledLane FeeEligible)
end X

namespace Z
export AssetTransferGlobalStateClosureV1
  (StateInvariant ContinuationRequirements continuedState_static_frame invariant_of_admitted
   admitted_of_invariant)
end Z

namespace K
export AssetTransferPolicySelectionV1
  (State StateAdmitted step rejected_step_noop step_preserves_state_admitted
   step_preserves_state_quantities_admitted
   step_preserves_owned_supply_and_claimant_liabilities_backed accepted_selected_step)
end K

namespace C
export AssetTransferCustodyEffectPlanV1
  (complete complete_rejected_exact complete_effect_plan_admitted
   complete_accepted_exact_relations complete_accepted_conservation
   complete_accepted_preserves_owned_supply complete_annotation_mirrors_iff)
end C

namespace G
export GlobalEconomicStateRefinementV2
  (GlobalState CommandOccurrence StateQuantitiesAdmitted OwnedMatchesSupply
   ClaimantLiabilitiesBacked OccurrenceContextMatches FixedContext ExactLaneWrites
   ExactEconomicTables ExactSupplyEffects ExactConservationCoverage ConservationRowsMatchState
   ExactTerminalRefinement ExactOracleRefinement ReplayRegistryRefines OrderedOccurrenceIds
   PreO009OutboxClosed ZeroOccurrenceStatic Verified)
end G

namespace T
export AssetTransferRefinementV1 (RejectCode CommandWellFormed)
end T

/-! ## Position and admission -/

/-- The runtime command ceiling of one epoch (`MAX_EPOCH_COMMANDS_V1`). -/
def maxEpochCommands : Nat := 64

/-- The certified epoch source economic state and the occurrence index of one attempt. -/
structure Position where
  source : G.GlobalState
  index : Nat

/-- The predecessor height the epoch relation expects: the source height at the first position
and the shared target height afterwards. -/
def expectedPriorHeight (position : Position) : Nat :=
  if position.index = 0 then position.source.height else position.source.height + 1

/-- The same chain, deployment, profile and writer epoch as the certified source. -/
def SameContext (source state : G.GlobalState) : Prop :=
  state.chainId = source.chainId ∧ state.deploymentRoot = source.deploymentRoot ∧
    state.profileRoot = source.profileRoot ∧ state.writerEpoch = source.writerEpoch

/-- Input facts for one attempt at a position against the carried state.  Every clause is a
premise on the inputs; none mentions the output.  `firstSource` and `sourceContext` mirror the
runtime source/position binding guards (the first predecessor is the source itself; every
carried state shares the source's chain, deployment, profile and writer epoch).  They are
provenance and position conditions beyond what the local accounting proofs consume, which
read only the carried state; authenticity of the certified source remains external. -/
structure EpochRequirements (position : Position) (carried : K.State) (next : X.Input) : Prop where
  pre : next.transfer.pre = carried
  indexBound : position.index < maxEpochCommands
  targetFits : FitsU64 (position.source.height + 1)
  priorHeight : carried.economic.height = expectedPriorHeight position
  firstSource : position.index = 0 → carried.economic = position.source
  sourceContext : SameContext position.source carried.economic
  context : G.OccurrenceContextMatches carried.economic next.occurrence
  height : next.occurrence.height = position.source.height + 1
  freshReplay : carried.economic.replayState next.occurrence.replayId = none
  freshOccurrence : ∀ replayId prior,
    carried.economic.replayState replayId = some prior → prior ≠ next.occurrence.occurrenceId
  preLaneRoot : next.privatePortPreRoot = carried.economic.laneRoots .assetTransfer
  laneRootChanged : next.postLaneRoot ≠ carried.economic.laneRoots .assetTransfer
  commandWellFormed : T.CommandWellFormed next.transfer.command
  feeEligible : X.FeeEligible next

/-! ## Construction -/

/-- The shared-height successor: the actual completed post economic tables with the opaque post
root, the occurrence height, the changed asset lane root and one replay insertion.  It differs
from the standalone successor only in the height field. -/
def epochSuccessor (input : X.Input) : G.GlobalState :=
  { (X.result input).post.economic with
    stateRoot := input.postStateRoot
    height := input.occurrence.height
    laneRoots := X.successorRoots (X.pre input) input.postLaneRoot
    replayState := X.insertReplay (X.pre input).replayState input.occurrence }

/-- Executable shared-height step: an accepted leaf yields the shared-height successor and one
occurrence; a rejected leaf yields the initial state, the leaf plan (proved empty below) and no
occurrence.  This branches on the actual verdict only and performs no admission check. -/
def epochStep (input : X.Input) : X.Result :=
  match (X.result input).verdict with
  | .accepted => ⟨.accepted, epochSuccessor input, (X.result input).plan, [input.occurrence]⟩
  | .rejected code => ⟨.rejected code, X.pre input, (X.result input).plan, []⟩

/-- Carry the actual module result and the shared-height step in one existing state value. -/
def epochContinuedState (input : X.Input) : K.State :=
  { (X.result input).post with economic := (epochStep input).post }

/-! ## Metadata and frame -/

/-- The four constructed metadata fields, stated as observable equations. -/
theorem epochSuccessor_metadata (input : X.Input) :
    (epochSuccessor input).stateRoot = input.postStateRoot ∧
      (epochSuccessor input).height = input.occurrence.height ∧
      (epochSuccessor input).laneRoots .assetTransfer = input.postLaneRoot ∧
      (∀ lane, lane ≠ .assetTransfer →
        (epochSuccessor input).laneRoots lane = (X.pre input).laneRoots lane) ∧
      (epochSuccessor input).replayState input.occurrence.replayId =
        some input.occurrence.occurrenceId ∧
      ∀ replayId, replayId ≠ input.occurrence.replayId →
        (epochSuccessor input).replayState replayId = (X.pre input).replayState replayId := by
  refine ⟨rfl, rfl, X.successorRoots_self (X.pre input) input.postLaneRoot, ?_,
    X.insertReplay_self (X.pre input).replayState input.occurrence, ?_⟩
  · intro lane other
    exact X.successorRoots_other (X.pre input) input.postLaneRoot other
  · intro replayId other
    exact X.insertReplay_other (X.pre input).replayState input.occurrence other

/-- Accepted or rejected, the successor is the initial state with the actual leaf balance table
and exactly the four constructed metadata fields; every other table and field is framed. -/
theorem epochSuccessor_frame (input : X.Input) :
    epochSuccessor input =
      { X.pre input with
        balances := (X.result input).post.economic.balances
        stateRoot := input.postStateRoot
        height := input.occurrence.height
        laneRoots := X.successorRoots (X.pre input) input.postLaneRoot
        replayState := X.insertReplay (X.pre input).replayState input.occurrence } := by
  unfold epochSuccessor
  rw [X.result_post_frame input]

theorem epochSuccessor_fixed_context (input : X.Input) :
    G.FixedContext (X.pre input) (epochSuccessor input) :=
  X.successor_fixed_context input

/-- An accepted leaf makes `epochStep` return the shared-height successor with one occurrence. -/
theorem epochStep_accepted {input : X.Input}
    (accepted : (K.step input.transfer).verdict = .accepted) :
    epochStep input =
      ⟨.accepted, epochSuccessor input, (X.result input).plan, [input.occurrence]⟩ := by
  have verdict : (X.result input).verdict = .accepted := by
    rw [X.result_verdict]
    exact accepted
  simp [epochStep, verdict]

/-- A rejected leaf makes `epochStep` the exact no-op: initial state, empty plan, no occurrence. -/
theorem epochStep_rejected_exact {input : X.Input} {code : T.RejectCode}
    (rejected : (K.step input.transfer).verdict = .rejected code) :
    epochStep input = ⟨.rejected code, X.pre input, EffectPlan.empty, []⟩ := by
  have leaf := C.complete_rejected_exact (fields := X.fields input) rejected
  unfold epochStep X.result
  rw [leaf]

/-- Module release and policy rows come from the actual module transition. -/
theorem epochContinuedState_static_frame (input : X.Input) :
    (epochContinuedState input).moduleReleaseId = input.transfer.pre.moduleReleaseId ∧
      (epochContinuedState input).policies = input.transfer.pre.policies :=
  Z.continuedState_static_frame input

theorem epochContinuedState_accepted {input : X.Input}
    (accepted : (K.step input.transfer).verdict = .accepted) :
    epochContinuedState input =
      { (X.result input).post with economic := epochSuccessor input } := by
  simp only [epochContinuedState, epochStep_accepted accepted]

/-- A rejected attempt leaves the exact carried state. -/
theorem epochContinuedState_rejected {input : X.Input} {code : T.RejectCode}
    (rejected : (K.step input.transfer).verdict = .rejected code) :
    epochContinuedState input = input.transfer.pre := by
  unfold epochContinuedState
  rw [epochStep_rejected_exact rejected, X.result_post, (K.rejected_step_noop rejected).1]
  rfl

/-! ## Shared-height obligations of an accepted attempt -/

/-- Quantity admission of the shared-height successor: the leaf preservation lemma, the u64
target height, monotone height from the predecessor-height clause and both replay freshness
premises. -/
theorem epochSuccessor_quantities {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input) :
    G.StateQuantitiesAdmitted (epochSuccessor input) := by
  have preserved :=
    K.step_preserves_state_quantities_admitted invariant.state invariant.quantities
  rw [← X.result_post input] at preserved
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, injective, _⟩ := invariant.quantities
  have inserted := X.insertReplay_injective injective requirements.freshOccurrence
  have heightFits : FitsU64 input.occurrence.height := by
    rw [requirements.height]
    exact requirements.targetFits
  have heightMono : (X.result input).post.economic.height ≤ input.occurrence.height := by
    rw [X.result_height, requirements.height]
    have prior := requirements.priorHeight
    unfold expectedPriorHeight at prior
    change input.transfer.pre.economic.height ≤ position.source.height + 1
    rw [prior]
    split <;> omega
  exact X.quantities_transport preserved input.postStateRoot
    (X.successorRoots (X.pre input) input.postLaneRoot) heightFits heightMono inserted

/-- Owned supply and claimant backing follow from the leaf preservation lemma; the successor
tables are the actual completed tables. -/
theorem epochSuccessor_owned_backed {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre) :
    G.OwnedMatchesSupply (epochSuccessor input) ∧
      G.ClaimantLiabilitiesBacked (epochSuccessor input) := by
  have preserved := K.step_preserves_owned_supply_and_claimant_liabilities_backed
    invariant.state invariant.owned invariant.backed
  rw [← X.result_post input] at preserved
  exact preserved

/-- Lane writes are exact: the single write names the enabled asset lane, its pre root is the
carried global lane root, its post root is the changed successor root, and no other lane root
changes. -/
theorem epochSuccessor_lane_writes {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.ExactLaneWrites (X.pre input) (epochSuccessor input) (X.result input).plan := by
  obtain ⟨writes, _, _⟩ := X.result_accepted_plan_fields accepted
  have postRoots : (epochSuccessor input).laneRoots =
      X.successorRoots (X.pre input) input.postLaneRoot := rfl
  have singleLane : X.SingleEnabledLane (X.pre input) := invariant.singleLane
  have preLaneRoot : input.privatePortPreRoot = (X.pre input).laneRoots .assetTransfer :=
    requirements.preLaneRoot
  have laneRootChanged : input.postLaneRoot ≠ (X.pre input).laneRoots .assetTransfer :=
    requirements.laneRootChanged
  refine ⟨?_, ?_, ?_⟩
  · intro lane
    rw [postRoots]
    by_cases asset : lane = .assetTransfer
    · subst asset
      rw [X.successorRoots_self]
      constructor
      · intro _
        exact laneRootChanged.symm
      · intro _
        refine ⟨⟨.assetTransfer, input.privatePortPreRoot, input.postLaneRoot⟩, ?_, rfl⟩
        rw [writes]
        exact List.mem_singleton.mpr rfl
    · rw [X.successorRoots_other _ _ asset]
      constructor
      · rintro ⟨write, member, laneEq⟩
        rw [writes, List.mem_singleton] at member
        subst member
        exact absurd laneEq.symm asset
      · intro changed
        exact absurd rfl changed
  · intro lane changed
    rw [postRoots] at changed
    by_cases asset : lane = .assetTransfer
    · subst asset
      exact (singleLane _).mpr rfl
    · rw [X.successorRoots_other _ _ asset] at changed
      exact absurd rfl changed
  · intro write member
    rw [writes, List.mem_singleton] at member
    subst member
    refine ⟨(singleLane _).mpr rfl, preLaneRoot, ?_⟩
    rw [postRoots]
    exact (X.successorRoots_self (X.pre input) input.postLaneRoot).symm

theorem epochSuccessor_annotations {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    AnnotationMirrors (X.result input).plan := by
  obtain ⟨policy, selection, _, _, _, _⟩ := K.accepted_selected_step accepted
  exact (C.complete_annotation_mirrors_iff (X.fields input) invariant.state
    requirements.commandWellFormed accepted).mpr
    ⟨policy, selection, requirements.feeEligible policy selection⟩

/-- The empty terminal plan refines the framed terminal registry; the accepted plan has no
liability effect because the leaf frames the liability table. -/
theorem epochSuccessor_terminal {input : X.Input} (state : K.StateAdmitted input.transfer.pre)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.ExactTerminalRefinement (X.pre input) (epochSuccessor input) (X.result input).plan ⟨[]⟩ := by
  have terminal := X.result_terminal input
  have liabilityZero : ∀ owner asset domain,
      effectFor .liability (X.result input).plan owner asset domain = 0 := by
    intro owner asset domain
    have tables := (C.complete_accepted_exact_relations (fields := X.fields input) state
      accepted).1.2.2.1 owner asset domain
    have liabilities : (C.complete (X.fields input) input.transfer).post.economic.liabilities =
        input.transfer.pre.economic.liabilities := X.result_liabilities input
    rw [liabilities, Int.sub_self] at tables
    exact tables.symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · intro delta member
    simp at member
  · intro obligationId _
    show terminalLookup (epochSuccessor input).terminalObligations obligationId = _
    rw [show (epochSuccessor input).terminalObligations = (X.pre input).terminalObligations
      from terminal]
  · intro delta member
    simp at member
  · intro owner asset domain
    simp [RunningTotalsFitI128]
  · intro owner asset domain
    rw [liabilityZero]
    rfl

/-- Exactly one replay insertion keyed by the admitted occurrence, fresh on both identities, with
every other key framed.  This is the replay clause of `ExactReplayRefinement` without its
standalone one-step height equation. -/
theorem epochSuccessor_replay_registry {position : Position} {input : X.Input}
    (requirements : EpochRequirements position input.transfer.pre input) :
    G.ReplayRegistryRefines (X.pre input).replayState (epochSuccessor input).replayState
      [input.occurrence] := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro occurrence member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨requirements.freshReplay,
      X.insertReplay_self (X.pre input).replayState input.occurrence, requirements.freshOccurrence⟩
  · intro replayId untouched
    have other : replayId ≠ input.occurrence.replayId := fun same =>
      untouched input.occurrence (List.mem_singleton.mpr rfl) same.symm
    exact X.insertReplay_other (X.pre input).replayState input.occurrence other

/-- The eighteen clauses of the existing `Verified` record other than `ExactReplayRefinement`,
stated verbatim on the shared-height successor, together with the shared-height replay
clauses.  `postQuantities` does read the successor height (u64 bound, Oracle height bound) and
is discharged from the u64 target and height monotonicity; the accounting clauses read only
the tables, which are the actual completed tables.  `ExactReplayRefinement` is split into its
order, consumption, context and registry clauses; its one-step height equation is replaced by
the shared target height, its u64 bound and the occurrence height binding.  This record is
deliberately not `Verified` and no `Accepted` record is built from it. -/
structure SharedHeightVerified (position : Position) (input : X.Input) : Prop where
  fixedContext : G.FixedContext (X.pre input) (epochSuccessor input)
  preQuantities : G.StateQuantitiesAdmitted (X.pre input)
  postQuantities : G.StateQuantitiesAdmitted (epochSuccessor input)
  effectPlan : EffectPlanAdmitted (X.result input).plan
  laneWrites : G.ExactLaneWrites (X.pre input) (epochSuccessor input) (X.result input).plan
  economicTables : G.ExactEconomicTables (X.pre input) (epochSuccessor input) (X.result input).plan
  supplyEffects : G.ExactSupplyEffects (X.pre input) (epochSuccessor input) (X.result input).plan
  conservationCoverage :
    G.ExactConservationCoverage (X.pre input) (epochSuccessor input) (X.result input).plan
  conservationRows :
    G.ConservationRowsMatchState (X.pre input) (epochSuccessor input) (X.result input).plan
  annotations : AnnotationMirrors (X.result input).plan
  ownedSupplyPre : G.OwnedMatchesSupply (X.pre input)
  ownedSupplyPost : G.OwnedMatchesSupply (epochSuccessor input)
  liabilitiesPre : G.ClaimantLiabilitiesBacked (X.pre input)
  liabilitiesPost : G.ClaimantLiabilitiesBacked (epochSuccessor input)
  terminal :
    G.ExactTerminalRefinement (X.pre input) (epochSuccessor input) (X.result input).plan ⟨[]⟩
  oracle :
    G.ExactOracleRefinement (X.pre input) (epochSuccessor input) (X.result input).plan ⟨[]⟩
  orderedOccurrences : G.OrderedOccurrenceIds [input.occurrence]
  occurrenceConsumptions :
    (X.result input).plan.occurrenceConsumptions = [input.occurrence.occurrenceId]
  occurrenceContext : G.OccurrenceContextMatches (X.pre input) input.occurrence
  replayRegistry :
    G.ReplayRegistryRefines (X.pre input).replayState (epochSuccessor input).replayState
      [input.occurrence]
  sharedHeight : (epochSuccessor input).height = position.source.height + 1
  heightFits : FitsU64 (epochSuccessor input).height
  occurrenceHeight : input.occurrence.height = (epochSuccessor input).height
  outboxClosed : G.PreO009OutboxClosed (X.result input).plan
  zeroOccurrence :
    G.ZeroOccurrenceStatic (X.pre input) (epochSuccessor input) (X.result input).plan ⟨[]⟩ ⟨[]⟩
      [input.occurrence]

/-- All shared-height obligations of an admitted, accepted attempt, from the carried state
invariant, the input requirements and the actual leaf verdict. -/
theorem sharedHeight_verified {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    SharedHeightVerified position input where
  fixedContext := epochSuccessor_fixed_context input
  preQuantities := invariant.quantities
  postQuantities := epochSuccessor_quantities invariant requirements
  effectPlan := C.complete_effect_plan_admitted (X.fields input) input.transfer invariant.state
    invariant.quantities
  laneWrites := epochSuccessor_lane_writes invariant requirements accepted
  economicTables :=
    (C.complete_accepted_exact_relations (fields := X.fields input) invariant.state accepted).1
  supplyEffects :=
    (C.complete_accepted_exact_relations (fields := X.fields input) invariant.state accepted).2
  conservationCoverage :=
    (C.complete_accepted_conservation (fields := X.fields input) invariant.state
      invariant.reservesEmpty requirements.commandWellFormed accepted).1
  conservationRows :=
    (C.complete_accepted_conservation (fields := X.fields input) invariant.state
      invariant.reservesEmpty requirements.commandWellFormed accepted).2
  annotations := epochSuccessor_annotations invariant requirements accepted
  ownedSupplyPre := invariant.owned
  ownedSupplyPost :=
    C.complete_accepted_preserves_owned_supply (fields := X.fields input) invariant.state
      invariant.owned accepted
  liabilitiesPre := invariant.backed
  liabilitiesPost := (epochSuccessor_owned_backed invariant).2
  terminal := epochSuccessor_terminal invariant.state accepted
  oracle := X.successor_oracle input
  orderedOccurrences := by simp [G.OrderedOccurrenceIds]
  occurrenceConsumptions := (X.result_accepted_plan_fields accepted).2.1
  occurrenceContext := requirements.context
  replayRegistry := epochSuccessor_replay_registry requirements
  sharedHeight := requirements.height
  heightFits := by
    show FitsU64 input.occurrence.height
    rw [requirements.height]
    exact requirements.targetFits
  occurrenceHeight := rfl
  outboxClosed := (X.result_accepted_plan_fields accepted).2.2
  zeroOccurrence := fun impossible => absurd impossible (List.cons_ne_nil _ _)

/-! ## The first position is the standalone successor -/

/-- At the first position the shared target height is the standalone one-step height, so the
constructed successor is exactly the standalone successor. -/
theorem epochSuccessor_first {position : Position} {input : X.Input}
    (requirements : EpochRequirements position input.transfer.pre input)
    (first : position.index = 0) : epochSuccessor input = X.successor input := by
  have prior := requirements.priorHeight
  unfold expectedPriorHeight at prior
  rw [if_pos first] at prior
  have height : input.occurrence.height = (X.pre input).height + 1 := by
    rw [requirements.height]
    show _ = input.transfer.pre.economic.height + 1
    rw [prior]
  unfold epochSuccessor X.successor
  rw [height]

/-- The standalone input admission at the first position. -/
theorem admitted_first {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input)
    (first : position.index = 0) : X.Admitted input := by
  have prior := requirements.priorHeight
  unfold expectedPriorHeight at prior
  rw [if_pos first] at prior
  refine Z.admitted_of_invariant invariant
    ⟨rfl, requirements.context, ?_, ?_, requirements.freshReplay, requirements.freshOccurrence,
      requirements.preLaneRoot, requirements.laneRootChanged, requirements.commandWellFormed,
      requirements.feeEligible⟩
  · rw [requirements.height, prior]
  · rw [prior]
    exact requirements.targetFits

/-- The existing `Verified` record holds at the first position by reuse of the standalone
theorem; no shared-height clause is needed there. -/
theorem epochSuccessor_first_verified {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input)
    (first : position.index = 0) (accepted : (K.step input.transfer).verdict = .accepted) :
    G.Verified (X.pre input) (X.result input).plan ⟨[]⟩ ⟨[]⟩ [input.occurrence]
      (epochSuccessor input) := by
  rw [epochSuccessor_first requirements first]
  exact X.successor_verified (admitted_first invariant requirements first) accepted

/-! ## The nine inherited state obligations -/

/-- Acceptance carries the shared-height metadata; rejection carries the exact pre-state. -/
theorem epochContinuedState_invariant {position : Position} {input : X.Input}
    (invariant : Z.StateInvariant input.transfer.pre)
    (requirements : EpochRequirements position input.transfer.pre input) :
    Z.StateInvariant (epochContinuedState input) := by
  cases verdict : (K.step input.transfer).verdict with
  | rejected code =>
      rw [epochContinuedState_rejected verdict]
      exact invariant
  | accepted =>
      rw [epochContinuedState_accepted verdict]
      have moduleAdmitted := K.step_preserves_state_admitted invariant.state
      rw [← X.result_post input] at moduleAdmitted
      have frame := X.result_post_frame input
      have release : (X.result input).post.moduleReleaseId = input.transfer.pre.moduleReleaseId :=
        (Z.continuedState_static_frame input).1
      refine ⟨?_, epochSuccessor_quantities invariant requirements,
        (epochSuccessor_owned_backed invariant).1, (epochSuccessor_owned_backed invariant).2,
        ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [K.StateAdmitted, epochSuccessor] using moduleAdmitted
      · simpa only [epochSuccessor, X.result_reserves] using invariant.reservesEmpty
      · simpa only [epochSuccessor, X.result_terminal] using invariant.terminalEmpty
      · change (X.result input).post.economic.outbox = []
        rw [congrArg (fun s : G.GlobalState => s.outbox) frame]
        exact invariant.outboxEmpty
      · change X.SingleEnabledLane (epochSuccessor input)
        unfold X.SingleEnabledLane
        change ∀ lane, (X.result input).post.economic.laneEnabled lane = true ↔
          lane = .assetTransfer
        rw [congrArg (fun s : G.GlobalState => s.laneEnabled) frame]
        exact invariant.singleLane
      · change (X.result input).post.economic.laneReleaseIds .assetTransfer =
          (X.result input).post.moduleReleaseId
        rw [congrArg (fun s : G.GlobalState => s.laneReleaseIds) frame, release]
        exact invariant.release

/-- Carried form: inherited state safety plus the next attempt's input requirements preserve
the nine obligations through the actual continuation. -/
theorem epochContinuation_invariant {position : Position} {carried : K.State} {next : X.Input}
    (invariant : Z.StateInvariant carried)
    (requirements : EpochRequirements position carried next) :
    Z.StateInvariant (epochContinuedState next) := by
  have pre := requirements.pre
  subst pre
  exact epochContinuedState_invariant invariant requirements

/-- Carried form of the shared-height obligations. -/
theorem epochContinuation_verified {position : Position} {carried : K.State} {next : X.Input}
    (invariant : Z.StateInvariant carried)
    (requirements : EpochRequirements position carried next)
    (accepted : (K.step next.transfer).verdict = .accepted) :
    SharedHeightVerified position next := by
  have pre := requirements.pre
  subst pre
  exact sharedHeight_verified invariant requirements accepted

/-- Carried form of the first-position `Verified` record. -/
theorem epochContinuation_first_verified {position : Position} {carried : K.State}
    {next : X.Input} (invariant : Z.StateInvariant carried)
    (requirements : EpochRequirements position carried next) (first : position.index = 0)
    (accepted : (K.step next.transfer).verdict = .accepted) :
    G.Verified (X.pre next) (X.result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence]
      (epochSuccessor next) := by
  have pre := requirements.pre
  subst pre
  exact epochSuccessor_first_verified invariant requirements first accepted

/-! ## Finite admitted prefix -/

/-- Ordered accepted attempts from a certified source.  The index of an attempt is the number of
earlier accepted attempts, each attempt is admitted against the carried state and accepted by the
actual leaf, and the carried state is the actual continuation.  A rejected attempt extends no
chain: the runtime fold aborts the whole epoch on its first rejected pair and publishes nothing.
-/
inductive EpochPrefix (source : K.State) : Nat → List G.CommandOccurrence → K.State → Prop
  | nil : EpochPrefix source 0 [] source
  | cons {index : Nat} {occurrences : List G.CommandOccurrence} {carried : K.State}
      {next : X.Input} (chain : EpochPrefix source index occurrences carried)
      (requirements : EpochRequirements ⟨source.economic, index⟩ carried next)
      (accepted : (K.step next.transfer).verdict = .accepted) :
      EpochPrefix source (index + 1) (occurrences ++ [next.occurrence]) (epochContinuedState next)

/-- The chain length is the position index, bounded by the runtime command ceiling. -/
theorem epochPrefix_length {source : K.State} {count : Nat}
    {occurrences : List G.CommandOccurrence} {carried : K.State}
    (chain : EpochPrefix source count occurrences carried) :
    occurrences.length = count ∧ count ≤ maxEpochCommands := by
  induction chain with
  | nil => exact ⟨rfl, Nat.zero_le _⟩
  | @cons index _ _ _ _ requirements _ ih =>
      have bound : index < maxEpochCommands := requirements.indexBound
      refine ⟨by simp [ih.1], ?_⟩
      omega

/-- Invariant preservation along an admitted accepted prefix, by induction on the chain. -/
theorem epochPrefix_invariant {source : K.State} {count : Nat}
    {occurrences : List G.CommandOccurrence} {carried : K.State}
    (certified : Z.StateInvariant source)
    (chain : EpochPrefix source count occurrences carried) : Z.StateInvariant carried := by
  induction chain with
  | nil => exact certified
  | cons _ requirements _ ih => exact epochContinuation_invariant ih requirements

/-- Along a chain the module frame is static, the context is the source context, the carried
height is the expected predecessor height of the next position (the source height before any
accepted attempt and the shared target height afterwards), and the replay registry is exactly
the source registry with every accepted occurrence inserted in order. -/
theorem epochPrefix_metadata {source : K.State} {count : Nat}
    {occurrences : List G.CommandOccurrence} {carried : K.State}
    (chain : EpochPrefix source count occurrences carried) :
    carried.moduleReleaseId = source.moduleReleaseId ∧ carried.policies = source.policies ∧
      SameContext source.economic carried.economic ∧
      carried.economic.height = expectedPriorHeight ⟨source.economic, count⟩ ∧
      carried.economic.replayState =
        occurrences.foldl X.insertReplay source.economic.replayState := by
  induction chain with
  | nil => exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  | @cons index _ carried next _ requirements accepted ih =>
      obtain ⟨release, policies, context, _, replay⟩ := ih
      have economic : (epochContinuedState next).economic = epochSuccessor next := by
        rw [epochContinuedState_accepted accepted]
      have preCarried : X.pre next = carried.economic :=
        congrArg (fun state : K.State => state.economic) requirements.pre
      have fixed := epochSuccessor_fixed_context next
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [(epochContinuedState_static_frame next).1, requirements.pre]
        exact release
      · rw [(epochContinuedState_static_frame next).2, requirements.pre]
        exact policies
      · rw [economic]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← fixed.1, preCarried]
          exact context.1
        · rw [← fixed.2.1, preCarried]
          exact context.2.1
        · rw [← fixed.2.2.2.1, preCarried]
          exact context.2.2.1
        · rw [← fixed.2.2.1, preCarried]
          exact context.2.2.2
      · rw [economic]
        show next.occurrence.height = _
        rw [requirements.height]
        simp [expectedPriorHeight]
      · rw [economic]
        show X.insertReplay (X.pre next).replayState next.occurrence = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, preCarried, replay]

/-- A nonempty prefix has between one and `maxEpochCommands` accepted attempts and carries the
shared target height; the runtime requires this nonempty range for a published epoch. -/
theorem epochPrefix_nonempty {source : K.State} {count : Nat}
    {occurrences : List G.CommandOccurrence} {carried : K.State}
    (chain : EpochPrefix source count occurrences carried) (nonempty : count ≠ 0) :
    1 ≤ count ∧ count ≤ maxEpochCommands ∧
      carried.economic.height = source.economic.height + 1 := by
  have length := epochPrefix_length chain
  have height := (epochPrefix_metadata chain).2.2.2.1
  refine ⟨by omega, length.2, ?_⟩
  rw [height]
  simp [expectedPriorHeight, nonempty]

/-- After a certified prefix, the next admitted accepted attempt satisfies the shared-height
obligations; at the first position it also satisfies the existing `Verified` record. -/
theorem epochPrefix_next_verified {source : K.State} {count : Nat}
    {occurrences : List G.CommandOccurrence} {carried : K.State} {next : X.Input}
    (certified : Z.StateInvariant source)
    (chain : EpochPrefix source count occurrences carried)
    (requirements : EpochRequirements ⟨source.economic, count⟩ carried next)
    (accepted : (K.step next.transfer).verdict = .accepted) :
    SharedHeightVerified ⟨source.economic, count⟩ next ∧
      (count = 0 → G.Verified (X.pre next) (X.result next).plan ⟨[]⟩ ⟨[]⟩ [next.occurrence]
        (epochSuccessor next)) := by
  have invariant := epochPrefix_invariant certified chain
  exact ⟨epochContinuation_verified invariant requirements accepted,
    fun first => epochContinuation_first_verified invariant requirements first accepted⟩

end AssetTransferEpochStateClosureV1
end Proofs
