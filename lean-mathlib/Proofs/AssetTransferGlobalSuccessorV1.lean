import Proofs.AssetTransferCustodyEffectPlanV1

/-!
# Restricted single-occurrence global successor for ASSET_TRANSFER V1

This file constructs the global successor state of one accepted custody-complete
transfer (`AssetTransferCustodyEffectPlanV1.complete`) and assembles the existing
`GlobalEconomicStateRefinementV2.Verified` record for it.  The construction mirrors
`project_single_occurrence_global_effects_v1`: the accepted post economic tables are
taken from the actual completed result, the height advances by exactly one, exactly one
replay row is inserted, only the enabled `ASSET_TRANSFER` lane root changes, and every
other metadata field, the oracle registry, the terminal registry, the history root and
the outbox are framed from the initial state.

## Input admission

`Admitted` is a predicate on the *input* only.  It states the quantitative admission of
the initial state, the restricted runtime scope (one enabled lane whose release is the
module release, empty reserves, empty terminal registry, empty outbox), the occurrence
context and height, replay-key and occurrence-identity freshness, the binding of the
private-port pre root to the initial global lane root, a checked distinct post lane
root, a width-admitted command, and fee eligibility evaluated on the actual
`policyFor` lookup.  No desired post-state, `Verified` field, post relation,
quantity-admission proof or replay output is a premise.  The `terminalEmpty`,
`outboxEmpty` and `release` clauses only pin the restricted runtime route: the terminal
registry, the outbox and the lane releases are framed unchanged, so those three clauses are
not consumed by any proof below.

## Roots and commitments

Roots are opaque strings.  `fields.preLaneRoot` is the admitted private-port pre root,
which admission binds to the initial global asset lane root; `fields.postLaneRoot` is the
supplied private-port post commitment, checked distinct from the pre root by an explicit
inequality premise rather than derived from positive movement.  `postStateRoot` is a
disclosed opaque external commitment for the successor `stateRoot`; no relation in
`Verified` reads the post `stateRoot`, so it cannot smuggle a table or replay relation.
Canonical hashing, authentication, receipts, publication, store heads and the runtime
guard order remain external and unproved.

## Executable step versus admission

`step` is executable and branches only on the actual leaf verdict; it is not an admission
checker.  The `Verified` theorem is conditional on `Admitted`; rejection is proved
separately as the exact leaf no-op with the empty plan and no occurrence.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferGlobalSuccessorV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace C
export Proofs.AssetTransferCustodyEffectPlanV1
  (complete complete_preserves_verdict_post complete_rejected_exact
   complete_preserves_other_plan_fields complete_effect_plan_admitted
   complete_accepted_exact_relations complete_accepted_conservation
   complete_accepted_preserves_owned_supply complete_annotation_mirrors_iff)
end C

namespace E
export Proofs.AssetTransferEffectPlanV1
  (CommitmentFields complete complete_preserves_verdict_post complete_accepted_plan
   selectedPlan_lane_writes selectedPlan_occurrences selectedPlan_outbox)
end E

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (Input State Result StateAdmitted policyFor selectedInput lift step accepted_selected_step
   rejected_step_noop step_preserves_state_quantities_admitted
   step_preserves_owned_supply_and_claimant_liabilities_backed)
end K

namespace S
export Proofs.AssetTransferSparseTablesV1 (step step_frame)
end S

namespace T
export Proofs.AssetTransferRefinementV1 (Policy Verdict RejectCode CommandWellFormed)
end T

namespace G
export Proofs.GlobalEconomicStateRefinementV2
  (GlobalState CommandOccurrence ReplayRegistry TerminalPlan OraclePlan
   StateQuantitiesAdmitted OwnedMatchesSupply ClaimantLiabilitiesBacked
   OccurrenceContextMatches ReplayOccurrenceIdsInjective OracleRegistryWithinGlobalHeight
   OracleRegistryAdmitted OracleOccurrenceWithinHeight FixedContext ExactLaneWrites
   LaneWrittenBy ExactEconomicTables ExactSupplyEffects ExactConservationCoverage
   ConservationRowsMatchState ExactTerminalRefinement ExactOracleRefinement
   ExactReplayRefinement ReplayRegistryRefines OrderedOccurrenceIds TerminalRegistryRefines
   TerminalOwningLaneWrites TerminalLiabilityEffects TerminalLiabilityAggregatesFitI128
   terminalLiabilityDeltaFor OracleRegistryRefines OracleLaneWrite PreO009OutboxClosed
   ZeroOccurrenceStatic Verified Accepted effectFor amountAt)
end G

/-! ## Input -/

/-- The complete input of one restricted global transition.  `transfer` is the actual
policy-selection input (context, command, module release, policies, initial global
economic state).  The remaining fields are the admitted occurrence, the private-port
pre root, the private-port post commitment and the opaque successor state root. -/
structure Input where
  transfer : K.Input
  occurrence : G.CommandOccurrence
  privatePortPreRoot : RootId
  postLaneRoot : RootId
  postStateRoot : RootId

/-- The initial global economic state of an input. -/
def pre (input : Input) : G.GlobalState := input.transfer.pre.economic

/-- Fee eligibility on the actual first-match lookup: the selected fee is zero or its owner
differs from the sender.  No caller-chosen policy is consulted. -/
def FeeEligible (input : Input) : Prop :=
  ∀ policy, K.policyFor input.transfer.pre.policies input.transfer.command.asset = some policy →
    (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.transfer.command.sender)

/-- Exactly the `ASSET_TRANSFER` lane is enabled. -/
def SingleEnabledLane (state : G.GlobalState) : Prop :=
  ∀ lane, state.laneEnabled lane = true ↔ lane = .assetTransfer

/-- Input admission.  Every clause is a premise on the input; none mentions the successor. -/
structure Admitted (input : Input) : Prop where
  state : K.StateAdmitted input.transfer.pre
  quantities : G.StateQuantitiesAdmitted (pre input)
  owned : G.OwnedMatchesSupply (pre input)
  backed : G.ClaimantLiabilitiesBacked (pre input)
  reservesEmpty : (pre input).reserves = []
  terminalEmpty : (pre input).terminalObligations = []
  outboxEmpty : (pre input).outbox = []
  singleLane : SingleEnabledLane (pre input)
  release : (pre input).laneReleaseIds .assetTransfer = input.transfer.pre.moduleReleaseId
  context : G.OccurrenceContextMatches (pre input) input.occurrence
  height : input.occurrence.height = (pre input).height + 1
  heightFits : FitsU64 ((pre input).height + 1)
  freshReplay : (pre input).replayState input.occurrence.replayId = none
  freshOccurrence : ∀ replayId prior, (pre input).replayState replayId = some prior →
    prior ≠ input.occurrence.occurrenceId
  preLaneRoot : input.privatePortPreRoot = (pre input).laneRoots .assetTransfer
  laneRootChanged : input.postLaneRoot ≠ (pre input).laneRoots .assetTransfer
  commandWellFormed : T.CommandWellFormed input.transfer.command
  feeEligible : FeeEligible input

/-! ## Construction -/

/-- The commitment fields handed to the custody completion: the admitted private-port pre
root, the supplied post commitment and the admitted occurrence identity. -/
def fields (input : Input) : E.CommitmentFields :=
  ⟨input.privatePortPreRoot, input.postLaneRoot, input.occurrence.occurrenceId⟩

/-- The actual custody-complete transfer result. -/
def result (input : Input) : K.Result :=
  C.complete (fields input) input.transfer

/-- Only the asset lane root changes. -/
def successorRoots (state : G.GlobalState) (postLaneRoot : RootId) : LaneId → RootId :=
  fun lane => if lane = .assetTransfer then postLaneRoot else state.laneRoots lane

/-- Exactly one replay insertion keyed by the occurrence replay identity. -/
def insertReplay (registry : G.ReplayRegistry) (occurrence : G.CommandOccurrence) :
    G.ReplayRegistry :=
  fun replayId =>
    if replayId = occurrence.replayId then some occurrence.occurrenceId else registry replayId

/-- The successor: the actual completed post economic state with the opaque post root, the
next height, the changed asset lane root and one replay insertion. -/
def successor (input : Input) : G.GlobalState :=
  { (result input).post.economic with
    stateRoot := input.postStateRoot
    height := (pre input).height + 1
    laneRoots := successorRoots (pre input) input.postLaneRoot
    replayState := insertReplay (pre input).replayState input.occurrence }

/-- One global transition result. -/
structure Result where
  verdict : T.Verdict
  post : G.GlobalState
  plan : EffectPlan
  occurrences : List G.CommandOccurrence

/-- Executable global step: an accepted leaf yields the successor and one occurrence; a
rejected leaf yields the initial state, the leaf plan (proved empty below) and no
occurrence.  This branches on the actual verdict only and performs no admission check. -/
def step (input : Input) : Result :=
  match (result input).verdict with
  | .accepted => ⟨.accepted, successor input, (result input).plan, [input.occurrence]⟩
  | .rejected code => ⟨.rejected code, pre input, (result input).plan, []⟩

/-! ## Metadata lemmas -/

theorem successorRoots_self (state : G.GlobalState) (root : RootId) :
    successorRoots state root .assetTransfer = root := by
  simp [successorRoots]

theorem successorRoots_other (state : G.GlobalState) (root : RootId) {lane : LaneId}
    (other : lane ≠ .assetTransfer) : successorRoots state root lane = state.laneRoots lane := by
  simp [successorRoots, other]

theorem insertReplay_self (registry : G.ReplayRegistry) (occurrence : G.CommandOccurrence) :
    insertReplay registry occurrence occurrence.replayId = some occurrence.occurrenceId := by
  simp [insertReplay]

theorem insertReplay_other (registry : G.ReplayRegistry) (occurrence : G.CommandOccurrence)
    {replayId : Identifier} (other : replayId ≠ occurrence.replayId) :
    insertReplay registry occurrence replayId = registry replayId := by
  simp [insertReplay, other]

/-- Inserting an occurrence identity absent from the initial registry keeps stored
occurrence identities injective.  Replay-key freshness is not needed here; it is consumed by
the `ReplayRegistryRefines` clause. -/
theorem insertReplay_injective {registry : G.ReplayRegistry} {occurrence : G.CommandOccurrence}
    (injective : ∀ left right occurrenceId, registry left = some occurrenceId →
      registry right = some occurrenceId → left = right)
    (freshOccurrence : ∀ replayId prior, registry replayId = some prior →
      prior ≠ occurrence.occurrenceId) :
    ∀ left right occurrenceId, insertReplay registry occurrence left = some occurrenceId →
      insertReplay registry occurrence right = some occurrenceId → left = right := by
  intro left right occurrenceId leftLookup rightLookup
  by_cases leftNew : left = occurrence.replayId
  · by_cases rightNew : right = occurrence.replayId
    · rw [leftNew, rightNew]
    · rw [leftNew, insertReplay_self] at leftLookup
      rw [insertReplay_other registry occurrence rightNew] at rightLookup
      exact absurd (Option.some.inj leftLookup).symm
        (freshOccurrence right occurrenceId rightLookup)
  · rw [insertReplay_other registry occurrence leftNew] at leftLookup
    by_cases rightNew : right = occurrence.replayId
    · rw [rightNew, insertReplay_self] at rightLookup
      exact absurd (Option.some.inj rightLookup).symm
        (freshOccurrence left occurrenceId leftLookup)
    · rw [insertReplay_other registry occurrence rightNew] at rightLookup
      exact injective left right occurrenceId leftLookup rightLookup

/-- Observations bounded by the initial height stay bounded by the incremented height. -/
theorem oracle_within_incremented_height {state : G.GlobalState}
    (within : G.OracleRegistryWithinGlobalHeight state) :
    ∀ oracleId occurrence, state.oracleOccurrences oracleId = some occurrence →
      G.OracleOccurrenceWithinHeight (state.height + 1) occurrence := by
  intro oracleId occurrence lookup
  have bound := within oracleId occurrence lookup
  exact ⟨bound.1, Nat.le_succ_of_le bound.2⟩

/-- Quantity admission transports across exactly the constructed metadata changes: a new
opaque root, a u64 height at least the old one, new lane roots and an injective replay
registry. -/
theorem quantities_transport {state : G.GlobalState} (admitted : G.StateQuantitiesAdmitted state)
    (root : RootId) {height : Nat} (roots : LaneId → RootId) {replay : G.ReplayRegistry}
    (heightFits : FitsU64 height) (heightMono : state.height ≤ height)
    (replayInjective : ∀ left right occurrenceId, replay left = some occurrenceId →
      replay right = some occurrenceId → left = right) :
    G.StateQuantitiesAdmitted
      { state with
        stateRoot := root
        height := height
        laneRoots := roots
        replayState := replay } := by
  obtain ⟨epoch, _, balances, supplies, custody, liabilities, reserves, balanceKeys,
    custodyKeys, liabilityKeys, reserveKeys, supplyKeys, totals, terminalKeys, terminalRows, _,
    oracleWithin, oracleKeys⟩ := admitted
  refine ⟨epoch, heightFits, balances, supplies, custody, liabilities, reserves, balanceKeys,
    custodyKeys, liabilityKeys, reserveKeys, supplyKeys, totals, terminalKeys, terminalRows,
    replayInjective, ?_, oracleKeys⟩
  intro oracleId occurrence lookup
  have bound := oracleWithin oracleId occurrence lookup
  exact ⟨bound.1, Nat.le_trans bound.2 heightMono⟩

/-! ## The actual leaf result -/

theorem result_verdict (input : Input) :
    (result input).verdict = (K.step input.transfer).verdict := by
  unfold result
  rw [(C.complete_preserves_verdict_post _ _).1, (E.complete_preserves_verdict_post _ _).1]

theorem result_post (input : Input) : (result input).post = (K.step input.transfer).post := by
  unfold result
  rw [(C.complete_preserves_verdict_post _ _).2, (E.complete_preserves_verdict_post _ _).2]

/-- Accepted or rejected, the leaf changes only the balance table of the initial state. -/
theorem result_post_frame (input : Input) :
    (result input).post.economic =
      { pre input with balances := (result input).post.economic.balances } := by
  rw [result_post]
  cases verdict : (K.step input.transfer).verdict with
  | rejected code =>
      rw [(K.rejected_step_noop verdict).1]
      rfl
  | accepted =>
      obtain ⟨policy, _, _, stepEq, _, _⟩ := K.accepted_selected_step verdict
      rw [stepEq]
      simp only [K.lift]
      exact S.step_frame _

theorem result_supplies (input : Input) :
    (result input).post.economic.supplies = (pre input).supplies := by
  have frame := congrArg GlobalState.supplies (result_post_frame input)
  exact frame

theorem result_custody (input : Input) :
    (result input).post.economic.custody = (pre input).custody := by
  have frame := congrArg GlobalState.custody (result_post_frame input)
  exact frame

theorem result_liabilities (input : Input) :
    (result input).post.economic.liabilities = (pre input).liabilities := by
  have frame := congrArg GlobalState.liabilities (result_post_frame input)
  exact frame

theorem result_reserves (input : Input) :
    (result input).post.economic.reserves = (pre input).reserves := by
  have frame := congrArg GlobalState.reserves (result_post_frame input)
  exact frame

theorem result_terminal (input : Input) :
    (result input).post.economic.terminalObligations = (pre input).terminalObligations := by
  have frame := congrArg GlobalState.terminalObligations (result_post_frame input)
  exact frame

theorem result_oracle (input : Input) :
    (result input).post.economic.oracleOccurrences = (pre input).oracleOccurrences := by
  have frame := congrArg GlobalState.oracleOccurrences (result_post_frame input)
  exact frame

theorem result_height (input : Input) :
    (result input).post.economic.height = (pre input).height := by
  have frame := congrArg GlobalState.height (result_post_frame input)
  exact frame

/-- The accepted completed plan carries exactly the constructed lane write, the admitted
occurrence identity and no outbox row. -/
theorem result_accepted_plan_fields {input : Input}
    (accepted : (K.step input.transfer).verdict = .accepted) :
    (result input).plan.laneWrites =
        [⟨.assetTransfer, input.privatePortPreRoot, input.postLaneRoot⟩] ∧
      (result input).plan.occurrenceConsumptions = [input.occurrence.occurrenceId] ∧
      (result input).plan.externalOutboxEnqueue = [] := by
  obtain ⟨policy, selection, _, _, _, _⟩ := K.accepted_selected_step accepted
  have other := C.complete_preserves_other_plan_fields (fields input) input.transfer
  unfold result
  refine ⟨?_, ?_, ?_⟩
  · rw [other.2.2.1, E.complete_accepted_plan accepted selection, E.selectedPlan_lane_writes]
    rfl
  · rw [other.2.2.2.1, E.complete_accepted_plan accepted selection, E.selectedPlan_occurrences]
    rfl
  · rw [other.2.2.2.2, E.complete_accepted_plan accepted selection, E.selectedPlan_outbox]

/-! ## Successor metadata -/

/-- The constructed metadata, stated as observable equations. -/
theorem successor_metadata (input : Input) :
    (successor input).stateRoot = input.postStateRoot ∧
      (successor input).height = (pre input).height + 1 ∧
      (successor input).laneRoots .assetTransfer = input.postLaneRoot ∧
      (∀ lane, lane ≠ .assetTransfer →
        (successor input).laneRoots lane = (pre input).laneRoots lane) ∧
      (successor input).replayState input.occurrence.replayId =
        some input.occurrence.occurrenceId ∧
      ∀ replayId, replayId ≠ input.occurrence.replayId →
        (successor input).replayState replayId = (pre input).replayState replayId := by
  refine ⟨rfl, rfl, successorRoots_self (pre input) input.postLaneRoot, ?_,
    insertReplay_self (pre input).replayState input.occurrence, ?_⟩
  · intro lane other
    exact successorRoots_other (pre input) input.postLaneRoot other
  · intro replayId other
    exact insertReplay_other (pre input).replayState input.occurrence other

theorem successor_fixed_context (input : Input) :
    G.FixedContext (pre input) (successor input) := by
  have frame := result_post_frame input
  have chain := congrArg GlobalState.chainId frame
  have deployment := congrArg GlobalState.deploymentRoot frame
  have epoch := congrArg GlobalState.writerEpoch frame
  have profile := congrArg GlobalState.profileRoot frame
  have history := congrArg GlobalState.historyRoot frame
  have outbox := congrArg GlobalState.outbox frame
  have releases := congrArg GlobalState.laneReleaseIds frame
  have enabled := congrArg GlobalState.laneEnabled frame
  exact ⟨chain.symm, deployment.symm, epoch.symm, profile.symm, history.symm, outbox.symm,
    releases.symm, enabled.symm⟩

/-- Lane writes are exact: the single write names the enabled asset lane, its pre root is the
initial global lane root, its post root is the changed successor root, and no other lane
root changes. -/
theorem successor_lane_writes {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.ExactLaneWrites (pre input) (successor input) (result input).plan := by
  obtain ⟨writes, _, _⟩ := result_accepted_plan_fields accepted
  have postRoots : (successor input).laneRoots = successorRoots (pre input) input.postLaneRoot :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro lane
    rw [postRoots]
    by_cases asset : lane = .assetTransfer
    · subst asset
      rw [successorRoots_self]
      constructor
      · intro _
        exact admitted.laneRootChanged.symm
      · intro _
        refine ⟨⟨.assetTransfer, input.privatePortPreRoot, input.postLaneRoot⟩, ?_, rfl⟩
        rw [writes]
        exact List.mem_singleton.mpr rfl
    · rw [successorRoots_other _ _ asset]
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
      exact (admitted.singleLane _).mpr rfl
    · rw [successorRoots_other _ _ asset] at changed
      exact absurd rfl changed
  · intro write member
    rw [writes, List.mem_singleton] at member
    subst member
    refine ⟨(admitted.singleLane _).mpr rfl, admitted.preLaneRoot, ?_⟩
    rw [postRoots]
    exact (successorRoots_self (pre input) input.postLaneRoot).symm

/-- Quantity admission of the successor from the initial admission, the leaf preservation
lemma, the u64 next height and both replay freshness premises. -/
theorem successor_quantities {input : Input} (admitted : Admitted input) :
    G.StateQuantitiesAdmitted (successor input) := by
  have preserved := K.step_preserves_state_quantities_admitted admitted.state admitted.quantities
  rw [← result_post input] at preserved
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, injective, _⟩ := admitted.quantities
  have inserted := insertReplay_injective injective admitted.freshOccurrence
  have heightMono : (result input).post.economic.height ≤ (pre input).height + 1 := by
    rw [result_height]
    exact Nat.le_succ _
  exact quantities_transport preserved input.postStateRoot
    (successorRoots (pre input) input.postLaneRoot) admitted.heightFits heightMono inserted

theorem successor_liabilities_backed {input : Input} (admitted : Admitted input) :
    G.ClaimantLiabilitiesBacked (successor input) := by
  have preserved := (K.step_preserves_owned_supply_and_claimant_liabilities_backed
    admitted.state admitted.owned admitted.backed).2
  rw [← result_post input] at preserved
  exact preserved

theorem successor_annotations {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    AnnotationMirrors (result input).plan := by
  obtain ⟨policy, selection, _, _, _, _⟩ := K.accepted_selected_step accepted
  exact (C.complete_annotation_mirrors_iff (fields input) admitted.state admitted.commandWellFormed
    accepted).mpr ⟨policy, selection, admitted.feeEligible policy selection⟩

/-- Exactly one ordered occurrence, context-bound, freshly inserted, one-step height. -/
theorem successor_replay {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.ExactReplayRefinement (pre input) (successor input) (result input).plan
      [input.occurrence] := by
  obtain ⟨_, occurrences, _⟩ := result_accepted_plan_fields accepted
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, admitted.heightFits, ?_⟩
  · simp [G.OrderedOccurrenceIds]
  · rw [occurrences]
    rfl
  · intro occurrence member
    rw [List.mem_singleton] at member
    subst member
    exact admitted.context
  · simp
  · intro occurrence member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨admitted.freshReplay, insertReplay_self (pre input).replayState input.occurrence,
      admitted.freshOccurrence⟩
  · intro replayId untouched
    have other : replayId ≠ input.occurrence.replayId := fun same =>
      untouched input.occurrence (List.mem_singleton.mpr rfl) same.symm
    exact insertReplay_other (pre input).replayState input.occurrence other
  · rfl
  · intro occurrence member
    rw [List.mem_singleton] at member
    subst member
    exact admitted.height

/-- The empty terminal plan refines the framed terminal registry; the accepted plan has no
liability effect because the leaf frames the liability table. -/
theorem successor_terminal {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.ExactTerminalRefinement (pre input) (successor input) (result input).plan ⟨[]⟩ := by
  have terminal := result_terminal input
  have liabilityZero : ∀ owner asset domain,
      G.effectFor .liability (result input).plan owner asset domain = 0 := by
    intro owner asset domain
    have tables := (C.complete_accepted_exact_relations (fields := fields input) admitted.state
      accepted).1.2.2.1 owner asset domain
    have liabilities : (C.complete (fields input) input.transfer).post.economic.liabilities =
        input.transfer.pre.economic.liabilities := result_liabilities input
    rw [liabilities, Int.sub_self] at tables
    exact tables.symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · intro delta member
    simp at member
  · intro obligationId _
    show terminalLookup (successor input).terminalObligations obligationId = _
    rw [show (successor input).terminalObligations = (pre input).terminalObligations from terminal]
  · intro delta member
    simp at member
  · intro owner asset domain
    simp [RunningTotalsFitI128]
  · intro owner asset domain
    rw [liabilityZero]
    rfl

theorem successor_oracle (input : Input) :
    G.ExactOracleRefinement (pre input) (successor input) (result input).plan ⟨[]⟩ := by
  refine ⟨⟨?_, ?_, ?_⟩, Or.inl rfl⟩
  · simp
  · intro delta member
    simp at member
  · intro oracleId _
    exact congrArg (fun registry => registry oracleId) (result_oracle input)

/-! ## The combined witness -/

/-- All nineteen fields of the existing `Verified` record for the constructed successor, from
input admission and the actual accepted leaf verdict. -/
theorem successor_verified {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    G.Verified (pre input) (result input).plan ⟨[]⟩ ⟨[]⟩ [input.occurrence] (successor input) where
  fixedContext := successor_fixed_context input
  preQuantities := admitted.quantities
  postQuantities := successor_quantities admitted
  effectPlan :=
    C.complete_effect_plan_admitted (fields input) input.transfer admitted.state admitted.quantities
  laneWrites := successor_lane_writes admitted accepted
  economicTables :=
    (C.complete_accepted_exact_relations (fields := fields input) admitted.state accepted).1
  supplyEffects :=
    (C.complete_accepted_exact_relations (fields := fields input) admitted.state accepted).2
  conservationCoverage :=
    (C.complete_accepted_conservation (fields := fields input) admitted.state
      admitted.reservesEmpty admitted.commandWellFormed accepted).1
  conservationRows :=
    (C.complete_accepted_conservation (fields := fields input) admitted.state
      admitted.reservesEmpty admitted.commandWellFormed accepted).2
  annotations := successor_annotations admitted accepted
  ownedSupplyPre := admitted.owned
  ownedSupplyPost :=
    C.complete_accepted_preserves_owned_supply (fields := fields input) admitted.state
      admitted.owned accepted
  liabilitiesPre := admitted.backed
  liabilitiesPost := successor_liabilities_backed admitted
  terminal := successor_terminal admitted accepted
  oracle := successor_oracle input
  replay := successor_replay admitted accepted
  outboxClosed := (result_accepted_plan_fields accepted).2.2
  zeroOccurrence := fun impossible => absurd impossible (List.cons_ne_nil _ _)

/-- An accepted leaf makes `step` return the successor with exactly one occurrence. -/
theorem step_accepted {input : Input} (accepted : (K.step input.transfer).verdict = .accepted) :
    step input = ⟨.accepted, successor input, (result input).plan, [input.occurrence]⟩ := by
  have verdict : (result input).verdict = .accepted := by
    rw [result_verdict]
    exact accepted
  simp [step, verdict]

/-- A rejected leaf makes `step` the exact no-op: initial state, empty plan, no occurrence. -/
theorem step_rejected_exact {input : Input} {code : T.RejectCode}
    (rejected : (K.step input.transfer).verdict = .rejected code) :
    step input = ⟨.rejected code, pre input, EffectPlan.empty, []⟩ := by
  have leaf := C.complete_rejected_exact (fields := fields input) rejected
  unfold step result
  rw [leaf]

/-- The existing `Accepted` record for an admitted, accepted input. -/
def acceptedWitness {input : Input} (admitted : Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) : G.Accepted (pre input) :=
  ⟨(result input).plan, ⟨[]⟩, ⟨[]⟩, [input.occurrence], successor input,
    successor_verified admitted accepted⟩

end AssetTransferGlobalSuccessorV1
end Proofs
