import Proofs.AssetLaneCustodyCoordinatorTraceV2
import AdmissionPositiveWitness

/-!
Semantic attack controls for the ordered custody-coordinator outcome.

The fixture is imported from the existing admission witness: the exact
`custody_state()` and its three runtime contexts and commands. The Python gate
checks the imported values against the runtime serializers. `digest` is a cheap byte observer (length and a rolling checksum)
and the commitment functions are concrete stubs for the uninterpreted
parameters: no runtime hash, receipt authenticity or publication authority is
claimed anywhere below. `deploymentRoot` and `profileRoot` stand for the two
complete-context occurrence coordinates that the finite `Occurrence` model does
not carry; the Python gate binds them to actual runtime values.

Stage 5 has no fixture-level falsifier here: the aggregate resource branch needs
a complete state whose post exceeds the outer byte ceiling, which the existing
runtime row-growth and one-byte boundary gates already exhibit. Stage 6 has no
injected falsifier by construction, because the leaf post is derived internally;
the dropped-row control below therefore compares the derived reprojection with a
mutated leaf state instead.
-/

set_option warningAsError true
set_option maxRecDepth 100000

namespace CoordinatorOutcomeControls

open AdmissionWitness (pre rootSyntax namespaceSyntax transferPolicy managedPolicy
  transferContext transferCommand issueContext issueCommand burnContext burnCommand
  transferAction issueAction burnAction transferCommit managedCommit)

open Proofs.AssetLaneCustodyCoordinatorOutcomeV2
open Proofs.GlobalSettlementCoreV2
open Proofs.RegisteredSupplySupportV1
open Proofs.RegisteredSupplyUpdateV1

namespace G
export Proofs.GlobalEconomicStateRefinementV2 (AmountRow amountForAsset supplyFor)
end G
namespace Ad
export Proofs.AssetLaneCustodyAdmissionV2 (ConstructorAdmission ConstructorMetadata
  PolicyOriginBindings RecordSyntax RegistrationPolicySyntax CustodyOrdered assetClassOf)
end Ad
namespace Lf
export Proofs.AssetTransferFiniteOutcomeV2 (MetadataAdmission CommandAdmission Resources
  accepted_iff accepted_post_effects candidate candidateFor project)
end Lf
namespace Lm
export Proofs.ManagedAssetFiniteOutcomeV2 (MetadataAdmission PolicySyntax)
end Lm
namespace Og
export Proofs.AssetOriginRegistryRefinementV2 (ValidState zeroRoot opaqueRootA opaqueRootB)
end Og
namespace Bt
export Proofs.AssetLaneFiniteByteAccountingV2 (Bytes ValidToken BalanceTokens SupplyTokens)
end Bt
namespace S
export Proofs.AssetTransferSparseTablesV1 (Unique PositiveAccounts accounts balanceWire)
end S
namespace MA
export Proofs.ManagedAssetFiniteAccountingV2 (updateRows)
end MA
namespace FA
export Proofs.AssetTransferFiniteAccountingV2 (transferRows)
end FA
namespace K
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn)
end K

attribute [local instance] lexOrd

local instance tokenDecidable (value : String) : Decidable (Bt.ValidToken value) := by
  unfold Bt.ValidToken
  infer_instance

local instance rootSyntaxDecidable (value : String) : Decidable (rootSyntax value) := by
  unfold rootSyntax
  infer_instance

local instance namespaceSyntaxDecidable (asset : String)
    (assetClass : Proofs.AssetTransferRefinementV2.AssetClass) :
    Decidable (namespaceSyntax asset assetClass) := by
  unfold namespaceSyntax
  infer_instance

/-- The dormant zero state, `custody_state(0, 0)`. -/
def zeroPre : D.FullState :=
  { pre with
    transfer := { pre.transfer with balances := [], supplies := [⟨"USD", 0⟩] }
    custody := [] }

/-! ## Root observers, commitments and the complete context coordinates -/

/-- A cheap discriminating byte observer. It is not a cryptographic hash. -/
def digest (bytes : Bt.Bytes) : String :=
  toString bytes.length ++ ":" ++
    toString (bytes.foldl (fun acc byte => (acc * 31 + byte.toNat) % 1000003) 7)

def leafRoots : Roots :=
  { digest := digest
    transfer := ⟨fun _ => "abstract-transfer-root"⟩
    managed := Proofs.ManagedAssetLifecycleRefinementV2.lifecycleRoots }

def planCommit (plan : EffectPlan) : RootId :=
  "plan-root:" ++ toString plan.rows.length ++ "/" ++ toString plan.assetConservation.length ++
    "/" ++ toString plan.feeConservation.length ++ "/" ++ toString plan.laneWrites.length ++
    "/" ++ toString plan.occurrenceConsumptions.length ++ "/" ++
    toString plan.externalOutboxEnqueue.length

def journalCommit (journal : Journal) : RootId :=
  "journal-root:" ++ journal.chainId ++ ":" ++ journal.commandOccurrenceId

def receiptCommit (domain : String) (body : ReceiptBody) : RootId :=
  domain ++ "|" ++ body.route ++ "|" ++ body.sourceLeafJournalRoot ++ "|" ++
    body.sourceLeafReceiptRoot ++ "|" ++ body.preLaneRoot ++ "|" ++ body.postLaneRoot ++ "|" ++
    body.effectPlanRoot ++ "|" ++ body.privatePortRoot ++ "|" ++
    body.terminalObligationsRoot ++ "|" ++ body.oracleOccurrencePlanRoot

def commits : Commitments :=
  { effectPlanRoot := planCommit
    journalRoot := journalCommit
    receiptRoot := receiptCommit
    transferPolicy := transferCommit
    managedPolicy := managedCommit }

/-- The runtime fixture chain id and writer epoch; the two roots stand for the
occurrence coordinates the finite model omits. -/
def chainId : String := "asset-lane-v2-test"
def deploymentRoot : RootId := Og.opaqueRootA
def profileRoot : RootId := Og.opaqueRootB
def writerEpoch : Nat := 4

def foreignRoot : RootId :=
  "0x3333333333333333333333333333333333333333333333333333333333333333"

/-- An opaque source leaf receipt root: leaf receipt authenticity is external. -/
def leafReceiptRoot : RootId :=
  "0x4444444444444444444444444444444444444444444444444444444444444444"

def transferOccurrenceId : RootId :=
  "0xc6c1d5ddb07287ae20ca4af8eba9732aa3bcbb47005559d0124f755b96dfd30b"
def issueOccurrenceId : RootId :=
  "0x4ee8ec9417ce4725edc12891224e46822de320c3f754c2c7fd4b5d994c6a6b50"
def burnOccurrenceId : RootId :=
  "0x99e839ed9096385b2e7e88d3b92f368d2be0362c987f3e74d5b851d332b6147e"

def inputFor (action : F.Action) : Input :=
  ⟨chainId, deploymentRoot, profileRoot, writerEpoch, action⟩

/-- The honest source packet: the existing-shape journal over the actual
internal coordinates, and exactly the actual finite leaf effect plan. -/
def sourceFor (action : F.Action) (occurrence receipt : RootId) : SourceCandidate :=
  { journal :=
      { chainId := chainId
        deploymentRoot := deploymentRoot
        profileRoot := profileRoot
        writerEpoch := writerEpoch
        laneId := .assetTransfer
        moduleReleaseId := pre.transfer.moduleReleaseId
        commandOccurrenceId := occurrence
        preLaneRoot := leafPreRoot digest pre action
        postLaneRoot := leafPostRoot digest pre action
        effectPlanRoot := planCommit (finitePlan digest pre action)
        privatePortRoot := Og.zeroRoot
        receiptRoot := receipt
        terminalObligationsRoot := Og.zeroRoot
        oracleOccurrencePlanRoot := Og.zeroRoot }
    effects := finitePlan digest pre action }

def transferSource : SourceCandidate :=
  sourceFor transferAction transferOccurrenceId leafReceiptRoot
def issueSource : SourceCandidate := sourceFor issueAction issueOccurrenceId leafReceiptRoot
def burnSource : SourceCandidate := sourceFor burnAction burnOccurrenceId leafReceiptRoot

/-- Every journal coordinate and the finite refinement hold by construction. -/
theorem relationFor (action : F.Action) (occurrence receipt : RootId)
    (release : contextRelease action = pre.transfer.moduleReleaseId)
    (present : occurrenceId action = some occurrence) :
    SourceRelation leafRoots commits pre (inputFor action)
      (sourceFor action occurrence receipt) := by
  refine {
    laneId := rfl
    chainId := rfl
    deploymentRoot := rfl
    profileRoot := rfl
    writerEpoch := rfl
    release := release
    moduleReleaseId := rfl
    preLaneRoot := rfl
    postLaneRoot := rfl
    effectPlanRoot := rfl
    privatePortRoot := rfl
    terminalObligationsRoot := rfl
    oracleOccurrencePlanRoot := rfl
    commandOccurrenceId := ?_
    refines := rfl }
  intro other otherPresent
  exact Option.some.inj (present.symm.trans otherPresent)

theorem transferRelation :
    SourceRelation leafRoots commits pre (inputFor transferAction) transferSource :=
  relationFor transferAction transferOccurrenceId leafReceiptRoot rfl rfl

theorem issueRelation :
    SourceRelation leafRoots commits pre (inputFor issueAction) issueSource :=
  relationFor issueAction issueOccurrenceId leafReceiptRoot rfl rfl

theorem burnRelation :
    SourceRelation leafRoots commits pre (inputFor burnAction) burnSource :=
  relationFor burnAction burnOccurrenceId leafReceiptRoot rfl rfl

theorem transferSelectedSource :
    FT.policyFor (E.transferSource (D.erase pre)) transferCommand.asset = some transferPolicy :=
  AdmissionWitness.transfer_selected

theorem managedSelected :
    FM.policyFor (E.managedSource (D.erase pre)) issueCommand.asset = some managedPolicy := by
  decide

theorem transferLeafAccepted :
    (FT.transition digest transferContext pre.transfer transferCommand).verdict = .accepted := by
  apply (Lf.accepted_iff _ _ _ _).2
  constructor
  · decide
  · unfold Lf.Resources
    simp only [Lf.candidate, AdmissionWitness.transfer_selected, Lf.candidateFor]
    rw [AdmissionWitness.transfer_candidate_rows]
    decide

theorem transferLeafAcceptedSource :
    (FT.transition digest transferContext (E.transferSource (D.erase pre))
      transferCommand).verdict = .accepted := transferLeafAccepted

theorem issueLeafAccepted :
    (FM.transition digest issueContext (E.managedSource (D.erase pre)) issueCommand).verdict =
      .accepted := by
  decide +kernel

theorem burnLeafAccepted :
    (FM.transition digest burnContext (E.managedSource (D.erase pre)) burnCommand).verdict =
      .accepted := by
  decide +kernel

theorem transferPostResources : D.Resources (D.step digest pre transferAction) := by
  simp only [transferAction]
  unfold D.Resources D.stateBytes
  have frame := D.step_metadata digest pre (.transfer transferContext transferCommand)
  rw [A.transfer_accepted_full_projection transferLeafAccepted, frame.1, frame.2.1, frame.2.2]
  rw [(Lf.accepted_post_effects transferLeafAccepted).1]
  simp only [Lf.candidate, AdmissionWitness.transfer_selected, Lf.candidateFor]
  rw [AdmissionWitness.transfer_candidate_rows]
  simp [pre]
  decide

theorem issuePostResources : D.Resources (D.step digest pre issueAction) := by
  decide +kernel

theorem burnPostResources : D.Resources (D.step digest pre burnAction) := by
  decide +kernel

theorem transferVerdictNone : leafVerdict digest pre transferAction = none := by
  simp only [transferAction, leafVerdict, transferLeafAcceptedSource]

theorem issueVerdictNone : leafVerdict digest pre issueAction = none := by
  simp only [issueAction, leafVerdict, issueLeafAccepted]

theorem burnVerdictNone : leafVerdict digest pre burnAction = none := by
  simp only [burnAction, leafVerdict, burnLeafAccepted]

theorem transferPresent : occurrenceId transferAction = some transferOccurrenceId := rfl
theorem issuePresent : occurrenceId issueAction = some issueOccurrenceId := rfl
theorem burnPresent : occurrenceId burnAction = some burnOccurrenceId := rfl

/-! ## Nonvacuous accepted transfer, issue and burn outcomes -/

theorem transferSourceBindings :
    SourceBindings leafRoots commits pre (inputFor transferAction) transferOccurrenceId
      transferSource := by
  obtain ⟨_, occurrence, _, _, _, present, sourceOk, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    accepted_transfer_outcome (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor transferAction) (ctx := transferContext) (command := transferCommand)
      (source := transferSource) AdmissionWitness.constructor_admission_witness AdmissionWitness.initial_policy_origin_bindings AdmissionWitness.transfer_action_admitted rfl
      transferLeafAcceptedSource transferRelation transferPostResources
  have sameOccurrence : occurrence = transferOccurrenceId :=
    Option.some.inj (present.symm.trans transferPresent)
  subst sameOccurrence
  exact sourceOk

/-- The accepted transfer outcome is nonvacuous on the actual fixture: the leaf
authorization verdict, the exact projection and reprojection, the internally
computed post, preserved constructor admission, completed plan admission, the
exact completed conservation row and the accepted-result bindings all hold. -/
theorem transfer_accepted_controls :
    (Proofs.AssetTransferRefinementV2.transition leafRoots.transfer transferContext
        (C.transferView (D.erase pre) transferPolicy) transferCommand).verdict = .accepted ∧
      Projection leafRoots pre (inputFor transferAction) transferSource ∧
      Reprojection digest pre transferAction ∧
      transition leafRoots commits pre (inputFor transferAction) transferSource =
        .accepted (completed leafRoots commits pre (inputFor transferAction) transferSource) ∧
      (completed leafRoots commits pre (inputFor transferAction) transferSource).post =
        D.step digest pre transferAction ∧
      Ad.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre transferAction) ∧
      EffectPlanAdmitted (completedEffects digest pre transferAction transferSource) ∧
      (completedEffects digest pre transferAction transferSource).assetConservation =
        [E.transferCompletedConservation (D.erase pre)
          (D.erase (D.step digest pre transferAction)) transferCommand] ∧
      AcceptedBindings leafRoots commits
        (completed leafRoots commits pre (inputFor transferAction) transferSource) := by
  obtain ⟨policy, _, selected, _, scalar, _, _, projection, reprojection, outcome, post,
    postAdmitted, _, planAdmitted, conservation, _, _, acceptedBindings⟩ :=
    accepted_transfer_outcome (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor transferAction) (ctx := transferContext) (command := transferCommand)
      (source := transferSource) AdmissionWitness.constructor_admission_witness AdmissionWitness.initial_policy_origin_bindings AdmissionWitness.transfer_action_admitted rfl
      transferLeafAcceptedSource transferRelation transferPostResources
  have samePolicy : policy = transferPolicy :=
    Option.some.inj (selected.symm.trans transferSelectedSource)
  subst samePolicy
  exact ⟨scalar, projection, reprojection, outcome, post, postAdmitted, planAdmitted,
    conservation, acceptedBindings⟩

/-- The accepted managed issue outcome, with the accounts-only source totals
recovered from the managed projection of the complete tables. -/
theorem issue_accepted_controls :
    (Proofs.ManagedAssetLifecycleRefinementV2.transition leafRoots.managed issueContext
        (C.managedView (D.erase pre) managedPolicy) issueCommand).verdict = .accepted ∧
      Projection leafRoots pre (inputFor issueAction) issueSource ∧
      Reprojection digest pre issueAction ∧
      transition leafRoots commits pre (inputFor issueAction) issueSource =
        .accepted (completed leafRoots commits pre (inputFor issueAction) issueSource) ∧
      (completed leafRoots commits pre (inputFor issueAction) issueSource).post =
        D.step digest pre issueAction ∧
      Ad.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre issueAction) ∧
      EffectPlanAdmitted (completedEffects digest pre issueAction issueSource) ∧
      (completedEffects digest pre issueAction issueSource).assetConservation =
        [E.managedCompletedConservation (D.erase pre)
          (D.erase (D.step digest pre issueAction)) issueCommand] ∧
      AcceptedBindings leafRoots commits
        (completed leafRoots commits pre (inputFor issueAction) issueSource) := by
  obtain ⟨policy, _, selected, _, scalar, _, _, projection, reprojection, outcome, post,
    postAdmitted, _, planAdmitted, conservation, _, _, acceptedBindings⟩ :=
    accepted_managed_outcome (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor issueAction) (ctx := issueContext) (command := issueCommand)
      (source := issueSource) AdmissionWitness.constructor_admission_witness AdmissionWitness.initial_policy_origin_bindings AdmissionWitness.issue_action_admitted rfl
      issueLeafAccepted issueRelation issuePostResources
  have samePolicy : policy = managedPolicy :=
    Option.some.inj (selected.symm.trans managedSelected)
  subst samePolicy
  exact ⟨scalar, projection, reprojection, outcome, post, postAdmitted, planAdmitted,
    conservation, acceptedBindings⟩

/-- The accepted managed burn outcome on the same fixture. -/
theorem burn_accepted_controls :
    transition leafRoots commits pre (inputFor burnAction) burnSource =
        .accepted (completed leafRoots commits pre (inputFor burnAction) burnSource) ∧
      (completed leafRoots commits pre (inputFor burnAction) burnSource).post =
        D.step digest pre burnAction ∧
      Ad.ConstructorAdmission rootSyntax namespaceSyntax (D.step digest pre burnAction) ∧
      EffectPlanAdmitted (completedEffects digest pre burnAction burnSource) ∧
      (completedEffects digest pre burnAction burnSource).assetConservation =
        [E.managedCompletedConservation (D.erase pre)
          (D.erase (D.step digest pre burnAction)) burnCommand] ∧
      AcceptedBindings leafRoots commits
        (completed leafRoots commits pre (inputFor burnAction) burnSource) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, outcome, post, postAdmitted, _, planAdmitted, conservation,
    _, _, acceptedBindings⟩ :=
    accepted_managed_outcome (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor burnAction) (ctx := burnContext) (command := burnCommand)
      (source := burnSource) AdmissionWitness.constructor_admission_witness AdmissionWitness.initial_policy_origin_bindings AdmissionWitness.burn_action_admitted rfl
      burnLeafAccepted burnRelation burnPostResources
  exact ⟨outcome, post, postAdmitted, planAdmitted, conservation, acceptedBindings⟩

/-! ## Mutant source packets -/

/-- A stale complete-context coordinate: the journal claims a foreign profile
root while every other field is intact. -/
def staleProfileSource : SourceCandidate :=
  { transferSource with
    journal := { transferSource.journal with profileRoot := foreignRoot } }

/-- A stale leaf frame: the journal claims a foreign leaf pre-lane root. -/
def staleLeafRootSource : SourceCandidate :=
  { transferSource with
    journal := { transferSource.journal with preLaneRoot := foreignRoot } }

def transferConservationRow : AssetConservationRow := ⟨"USD", 80, 80, 100, 100, 0, 0⟩
def unchangedAudRow : AssetConservationRow := ⟨"AUD", 0, 0, 0, 0, 0, 0⟩
def wrongAssetRow : AssetConservationRow := ⟨"AUD", 80, 80, 100, 100, 0, 0⟩

def twoRowEffects : EffectPlan :=
  { transferSource.effects with assetConservation := [transferConservationRow, unchangedAudRow] }

/-- Valid source effects with two conservation rows and a repaired effect root:
source binding passes and the exact one-row projection must fail. -/
def twoRowSource : SourceCandidate :=
  { transferSource with
    journal := { transferSource.journal with effectPlanRoot := planCommit twoRowEffects }
    effects := twoRowEffects }

def wrongAssetEffects : EffectPlan :=
  { transferSource.effects with assetConservation := [wrongAssetRow] }

def wrongAssetSource : SourceCandidate :=
  { transferSource with
    journal := { transferSource.journal with effectPlanRoot := planCommit wrongAssetEffects }
    effects := wrongAssetEffects }

def outboxEnqueue : ExternalOutboxEnqueue :=
  ⟨foreignRoot, "external-adapter", foreignRoot, foreignRoot⟩

def outboxEffects : EffectPlan :=
  { transferSource.effects with externalOutboxEnqueue := [outboxEnqueue] }

/-- An added external outbox with a repaired effect root. -/
def outboxSource : SourceCandidate :=
  { transferSource with
    journal := { transferSource.journal with effectPlanRoot := planCommit outboxEffects }
    effects := outboxEffects }

/-- Competing faults: a stale chain id and a wrong-asset row at once. -/
def competingSource : SourceCandidate :=
  { wrongAssetSource with
    journal := { wrongAssetSource.journal with chainId := "foreign-chain" } }

/-- The two-row and wrong-asset packets keep every source binding field. -/
theorem mutantSourceBindings :
    SourceBindings leafRoots commits pre (inputFor transferAction) transferOccurrenceId
        twoRowSource ∧
      SourceBindings leafRoots commits pre (inputFor transferAction) transferOccurrenceId
        wrongAssetSource := by
  rcases transferSourceBindings with ⟨laneId, chain, deploy, profile, epoch, release,
    moduleRelease, occurrence, preRoot, occurrences, lanes, postRoot, -, outbox, priv, term,
    oracle⟩
  exact ⟨⟨laneId, chain, deploy, profile, epoch, release, moduleRelease, occurrence,
      preRoot, occurrences, lanes, postRoot, rfl, outbox, priv, term, oracle⟩,
    ⟨laneId, chain, deploy, profile, epoch, release, moduleRelease, occurrence,
      preRoot, occurrences, lanes, postRoot, rfl, outbox, priv, term, oracle⟩⟩

/-- Exact cardinality: two conservation rows fail the one-row projection and the
coordinator returns its own projection code. -/
theorem two_conservation_rows_fail_the_exact_projection :
    ¬ Projection leafRoots pre (inputFor transferAction) twoRowSource ∧
      transition leafRoots commits pre (inputFor transferAction) twoRowSource =
        .rejected (.coordinator .projectionMismatch) := by
  have mismatch : ¬ Projection leafRoots pre (inputFor transferAction) twoRowSource := by decide
  refine ⟨mismatch, ?_⟩
  exact (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
    (action := inputFor transferAction) (source := twoRowSource)
    (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
    transferPresent).2.1 mutantSourceBindings.1 mismatch

/-- A wrong command asset in an otherwise well-bound source row is a projection
rejection, not an accepted completion. -/
theorem wrong_asset_row_fails_the_exact_projection :
    ¬ Projection leafRoots pre (inputFor transferAction) wrongAssetSource ∧
      transition leafRoots commits pre (inputFor transferAction) wrongAssetSource =
        .rejected (.coordinator .projectionMismatch) := by
  have mismatch : ¬ Projection leafRoots pre (inputFor transferAction) wrongAssetSource := by
    decide
  refine ⟨mismatch, ?_⟩
  exact (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
    (action := inputFor transferAction) (source := wrongAssetSource)
    (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
    transferPresent).2.1 mutantSourceBindings.2 mismatch

/-- Stale source coordinates are coordinator source rejections. -/
theorem stale_source_fields_are_source_mismatches :
    transition leafRoots commits pre (inputFor transferAction) staleProfileSource =
        .rejected (.coordinator .candidateBindingMismatch) ∧
      transition leafRoots commits pre (inputFor transferAction) staleLeafRootSource =
        .rejected (.coordinator .candidateBindingMismatch) := by
  constructor
  · refine (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor transferAction) (source := staleProfileSource)
      (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
      transferPresent).1 ?_
    intro bindings
    rcases bindings with ⟨-, -, -, profile, -, -, -, -, -, -, -, -, -, -, -, -, -⟩
    exact absurd profile (by decide)
  · refine (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
      (action := inputFor transferAction) (source := staleLeafRootSource)
      (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
      transferPresent).1 ?_
    intro bindings
    rcases bindings with ⟨-, -, -, -, -, -, -, -, preRoot, -, -, -, -, -, -, -, -⟩
    exact absurd preRoot (by decide +kernel)

/-- An added external outbox with a repaired effect root must still fail the
source relation, and must not be silently dropped by completion. -/
theorem added_external_outbox_is_a_source_mismatch :
    transition leafRoots commits pre (inputFor transferAction) outboxSource =
      .rejected (.coordinator .candidateBindingMismatch) := by
  refine (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
    (action := inputFor transferAction) (source := outboxSource)
    (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
    transferPresent).1 ?_
  intro bindings
  rcases bindings with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, outbox, -, -, -⟩
  exact absurd outbox (by decide)

/-- Competing faults: the source mismatch precedes the projection failure. -/
theorem source_mismatch_precedes_the_projection_failure :
    ¬ Projection leafRoots pre (inputFor transferAction) competingSource ∧
      transition leafRoots commits pre (inputFor transferAction) competingSource =
        .rejected (.coordinator .candidateBindingMismatch) := by
  have mismatch : ¬ Projection leafRoots pre (inputFor transferAction) competingSource := by
    decide
  refine ⟨mismatch, ?_⟩
  refine (staged_rejection_order (roots := leafRoots) (commits := commits) (pre := pre)
    (action := inputFor transferAction) (source := competingSource)
    (occurrence := transferOccurrenceId) AdmissionWitness.initial_policy_origin_bindings transferVerdictNone
    transferPresent).1 ?_
  intro bindings
  rcases bindings with ⟨-, chain, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩
  exact absurd chain (by decide)

/-! ## Aggregate frame, receipt identity and leaf-code controls -/

/-- The completed lane write is the complete-state pair, the source journal
keeps the leaf pre root, and the two roots differ under the byte observer: a
journal mutant that reuses the leaf frame is not the completed write. -/
theorem completed_lane_write_is_not_the_leaf_frame :
    completeRoot digest pre ≠ leafPreRoot digest pre transferAction ∧
      (completedEffects digest pre transferAction transferSource).laneWrites =
        [⟨LaneId.assetTransfer, completeRoot digest pre,
          completeRoot digest (D.step digest pre transferAction)⟩] ∧
      transferSource.journal.preLaneRoot = leafPreRoot digest pre transferAction :=
  ⟨by decide +kernel, rfl, rfl⟩

def receiptMutantCommits : Commitments :=
  { commits with journalRoot := fun journal => journal.receiptRoot }

/-- Substituting the source receipt root for the source journal root and
recomputing the outer receipt changes the actual receipt body. -/
theorem receipt_mutant_body_differs :
    journalCommit transferSource.journal ≠ transferSource.journal.receiptRoot ∧
      completedReceiptBody leafRoots commits pre transferAction transferSource ≠
        completedReceiptBody leafRoots receiptMutantCommits pre transferAction transferSource := by
  have different : journalCommit transferSource.journal ≠ transferSource.journal.receiptRoot := by
    decide
  refine ⟨different, ?_⟩
  intro equal
  exact different (congrArg ReceiptBody.sourceLeafJournalRoot equal)

def droppedManagedLeaf : FM.State :=
  ⟨"0x2e33c221765009e5181427a67296d9a5c6f61d9483a4235b9bf5e7e2d282252f", [managedPolicy], [],
    [⟨"USD", 102⟩]⟩

/-- The reprojection is an exact leaf-state equality: a post whose managed rows
were dropped, even with the same policy list, is not the derived reprojection. -/
theorem dropped_managed_row_is_not_the_reprojection :
    E.managedSource (D.erase (D.step digest pre issueAction)) =
        (FM.transition digest issueContext (E.managedSource (D.erase pre)) issueCommand).post ∧
      E.managedSource (D.erase (D.step digest pre issueAction)) ≠ droppedManagedLeaf ∧
      droppedManagedLeaf.policies = (E.managedSource (D.erase pre)).policies := by
  refine ⟨A.managed_accepted_full_projection AdmissionWitness.complete AdmissionWitness.issue_action_admitted issueLeafAccepted,
    ?_, ?_⟩
  · decide +kernel
  · decide

def driftPre : D.FullState :=
  { pre with
    originRegistry := { pre.originRegistry with
      assets := pre.originRegistry.assets.map
        (fun record => { record with transferPolicyRoot := foreignRoot }) } }

/-- Registry versus leaf: the finite leaf would accept, yet stage 1 rejects with
the coordinator registry code before leaf dispatch and before the source packet
is read. -/
theorem registry_binding_precedes_an_accepting_leaf :
    ¬ Ad.PolicyOriginBindings transferCommit managedCommit driftPre ∧
      leafVerdict digest driftPre transferAction = none ∧
      transition leafRoots commits driftPre (inputFor transferAction) transferSource =
        .rejected (.coordinator .registryBindingMismatch) := by
  have mismatch : ¬ Ad.PolicyOriginBindings transferCommit managedCommit driftPre := by decide
  have verdict : leafVerdict digest driftPre transferAction = none := transferVerdictNone
  exact ⟨mismatch, verdict,
    registry_binding_mismatch_precedes_leaf leafRoots commits driftPre (inputFor transferAction)
      transferSource mismatch⟩

def zeroLeafCode : RejectCode := .transferLeaf (.economic .insufficientBalance)

/-- Zero-state behavior: the actual leaf rejects, the coordinator returns the
exact leaf code on the leaf route, and the outcome is an exact no-op. -/
theorem zero_state_transfer_is_an_exact_leaf_rejection :
    leafVerdict digest zeroPre transferAction = some zeroLeafCode ∧
      zeroLeafCode.route = Route.transfer ∧
      transition leafRoots commits zeroPre (inputFor transferAction) transferSource =
        .rejected zeroLeafCode ∧
      (transition leafRoots commits zeroPre (inputFor transferAction)
        transferSource).postState = zeroPre ∧
      (transition leafRoots commits zeroPre (inputFor transferAction)
        transferSource).effects = EffectPlan.empty := by
  have verdict : leafVerdict digest zeroPre transferAction = some zeroLeafCode := by
    decide +kernel
  have bindings : Ad.PolicyOriginBindings transferCommit managedCommit zeroPre := by decide
  have rejected := leaf_rejection_preserves_route_and_code leafRoots commits zeroPre
    (inputFor transferAction) transferSource zeroLeafCode bindings verdict
  refine ⟨verdict, rfl, rejected.1, ?_, ?_⟩
  · rw [rejected.1]
    exact (rejected_is_exact_no_op zeroPre zeroLeafCode).1
  · rw [rejected.1]
    exact (rejected_is_exact_no_op zeroPre zeroLeafCode).2.1

/-- These attempts include a genuine transfer and a stale source packet.
Later source packets need not be accepted for the prefix invariant to hold. -/
def mixedAttempts : List (Input × SourceCandidate) :=
  [(inputFor transferAction, transferSource), (inputFor transferAction, staleProfileSource),
    (inputFor issueAction, issueSource), (inputFor burnAction, burnSource)]

theorem mixed_prefix_admission_control (front rest : List (Input × SourceCandidate))
    (split : mixedAttempts = front ++ rest) :
    A.ConstructorAdmission rootSyntax namespaceSyntax
        (Proofs.AssetLaneCustodyCoordinatorTraceV2.execute leafRoots commits pre front) ∧
      A.PolicyOriginBindings transferCommit managedCommit
        (Proofs.AssetLaneCustodyCoordinatorTraceV2.execute leafRoots commits pre front) := by
  apply Proofs.AssetLaneCustodyCoordinatorTraceV2.every_prefix_preserves_complete_admission
    leafRoots commits pre mixedAttempts AdmissionWitness.constructor_admission_witness
    AdmissionWitness.initial_policy_origin_bindings ?_ front rest split
  intro attempt member
  simp only [mixedAttempts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact AdmissionWitness.transfer_action_admitted
  · exact AdmissionWitness.transfer_action_admitted
  · exact AdmissionWitness.issue_action_admitted
  · exact AdmissionWitness.burn_action_admitted

end CoordinatorOutcomeControls
