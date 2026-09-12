import Proofs.AssetLaneCustodyAdmissionV2

/-!
# Ordered custody-coordinator outcome over the complete custody state

`transition roots commits pre action sourceCandidate : Outcome pre` models the ordered
finite decision of `transition_asset_lane_custody_v2`. It derives the actual
finite FT/FM leaf verdict, the leaf post and the complete post state internally
from `pre` and `action`. `sourceCandidate` owns only the
existing-shape source journal and the source effect plan: it carries no post
state, no success flag and no admission Boolean, and it grants no caller
authority. The packet is an explicit observation of fixed internal leaf output,
not a live external injection API.

Stage order after typed runtime input construction and fixed-schema admission:

1. `PolicyOriginBindings`, else the coordinator code `REGISTRY_BINDING_MISMATCH`.
2. the actual FT/FM verdict, retaining the exact leaf route and leaf code.
3. `SourceBindings` over the context/journal coordinates, release, occurrence,
   leaf pre/post roots, the singleton lane write and occurrence consumption, the
   empty outbox, zero external roots and effect commitment, else
   `CANDIDATE_BINDING_MISMATCH`.
4. `Projection`: the exact one-row command-asset conservation projection with
   accounts-only source totals, else `PROJECTION_MISMATCH`.
5. `Resources` of the internally derived `D.step` post, else
   `STATE_RESOURCE_LIMIT`.
6. `Reprojection`: exact full transfer or managed reprojection of the accepted
   leaf, with the transfer policy list preserved, else `PROJECTION_MISMATCH`.
7. completion: complete physical conservation totals, the one complete-state
   lane write, and the exact rebound journal and receipt body.

The four complete-context coordinates that the existing finite `Context` and
`Occurrence` model omits stay explicit in `Input`: `chainId`, `deploymentRoot`,
`profileRoot` and `writerEpoch`. Occurrence, release and command identity are
the existing ones. `Journal` holds the fourteen semantic fields of
`LaneModuleTransitionJournalV2` after fixed-schema admission (Python injects
that schema; Rust stores it explicitly); `ReceiptBody` is the nine-field body of
the runtime receipt domain `asset-lane-custody-coordinator-receipt-v2`.

Limits. `Roots.digest`, the two leaf root models and every `Commitments` field
are uninterpreted parameters: no Lean hash, codec, parser or root authenticity
is claimed, root equality authenticates nothing, and receipt identity is a body
and domain representation only. Only the aggregate resource decision is a typed
rejection here; every other complete-state constructor condition is *derived*
for the accepted case from initial constructor admission, input shape and the
actual accepted finite leaf. Unmodeled constructor failures are not
reinterpreted as typed no-ops.
This derives modeled structural predicates only. Exact runtime types, root
syntax, canonical/schema admission and the mapping from `Input` to the owned
runtime context remain external refinement obligations. Reprojection compares
internally derived actual-leaf posts; retained runtime fault-injection tests
separately cover faulty observed leaf posts. No universal runtime-constructor
unreachability follows from these model theorems.
Some source conjuncts also hold by accepted-result construction downstream;
`SourceBindings` states the honest field correspondence and no uniqueness of
those guards is claimed. Coordinator codes are distinguished from leaf codes by
their route, not by the shared `STATE_RESOURCE_LIMIT` wire string. Nothing here
establishes guest qualification, publication, finality or recovery.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyCoordinatorOutcomeV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2 RegisteredSupplySupportV1

namespace A
export AssetLaneCustodyAdmissionV2 (ConstructorAdmission PolicyOriginBindings
  policy_origin_bindings_preserved step_preserves_constructor_admission
  transfer_accepted_full_projection managed_accepted_full_projection)
end A
namespace D
export AssetLaneCustodyCompleteStateV2 (FullState erase step stateBytes Resources
  erase_step erase_transfer_source step_metadata step_transfer_metadata)
end D
namespace C
export AssetLaneCustodyRefinementV2 (State RowsRepresentable physicalFor supplyAt
  transferView managedView transferPost)
end C
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource transferPostFromLeaf
  managedPostFromLeaf completePlan completeConservationRow transferCompletedConservation
  managedCompletedConservation transferEffectPlan managedEffectPlan
  transfer_accepted_completion managed_accepted_completion managed_source_supply)
end E
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action step)
end F
namespace X
export AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  transfer_source_structural managed_source_structural)
end X
namespace TP
export AssetTransferFiniteEffectPlanV2 (transferPlan transferConservation
  transfer_accepted_fields)
end TP
namespace MP
export AssetLaneFiniteEffectPlanV2 (managedPlan managedConservation managed_accepted_fields)
end MP
namespace FT
export AssetTransferFiniteOutcomeV2 (State RejectCode Verdict transition stateRoot policyFor
  policyFor_spec candidate_immutable accepted_post_effects)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (State RejectCode Verdict Structural transition stateRoot
  policyFor policyFor_spec accepted_post_effects)
end FM
namespace T
export AssetTransferRefinementV2 (Context Command Policy AssetClass RootModel)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Context Command Policy RootModel signedAmount)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes)
end B
namespace H
export AssetLaneSharedProjectionV2 (selectRows_total)
end H
namespace R
export AssetLaneCustodyRecompositionV2 (managedAssets)
end R
namespace O
export AssetOriginRegistryRefinementV2 (zeroRoot)
end O

/-! ## Owned coordinator values -/

/-- The closed route tag of `AssetLaneRouteV2`. -/
inductive Route where
  | transfer
  | managedLifecycle
  | coordinator
  deriving DecidableEq, Repr

def Route.code : Route → String
  | .transfer => "TRANSFER"
  | .managedLifecycle => "MANAGED_LIFECYCLE"
  | .coordinator => "COORDINATOR"

/-- The route is derived from the owned command, never supplied by the source. -/
def routeOf : F.Action → Route
  | .transfer _ _ => .transfer
  | .managed _ _ => .managedLifecycle

/-- The four coordinator-owned rejection codes of
`AssetLaneCoordinatorRejectCodeV2`. -/
inductive CoordinatorRejectCode where
  | registryBindingMismatch
  | candidateBindingMismatch
  | projectionMismatch
  | stateResourceLimit
  deriving DecidableEq, Repr

def CoordinatorRejectCode.code : CoordinatorRejectCode → String
  | .registryBindingMismatch => "REGISTRY_BINDING_MISMATCH"
  | .candidateBindingMismatch => "CANDIDATE_BINDING_MISMATCH"
  | .projectionMismatch => "PROJECTION_MISMATCH"
  | .stateResourceLimit => "STATE_RESOURCE_LIMIT"

def allCoordinatorRejectCodes : List CoordinatorRejectCode :=
  [.registryBindingMismatch, .candidateBindingMismatch, .projectionMismatch,
    .stateResourceLimit]

/-- A coordinator code and a leaf code are separate constructors; the leaf codes
are the existing finite FT/FM codes, reused unchanged. -/
inductive RejectCode where
  | coordinator (code : CoordinatorRejectCode)
  | transferLeaf (code : FT.RejectCode)
  | managedLeaf (code : FM.RejectCode)
  deriving DecidableEq, Repr

def RejectCode.route : RejectCode → Route
  | .coordinator _ => .coordinator
  | .transferLeaf _ => .transfer
  | .managedLeaf _ => .managedLifecycle

def RejectCode.code : RejectCode → String
  | .coordinator code => code.code
  | .transferLeaf code => code.code
  | .managedLeaf code => code.code

/-- The fourteen semantic journal fields after fixed-schema admission. The
runtime schema is implicit here; RootId is a model string, not a validated root. -/
structure Journal where
  chainId : String
  deploymentRoot : RootId
  profileRoot : RootId
  writerEpoch : Nat
  laneId : LaneId
  moduleReleaseId : RootId
  commandOccurrenceId : RootId
  preLaneRoot : RootId
  postLaneRoot : RootId
  effectPlanRoot : RootId
  privatePortRoot : RootId
  receiptRoot : RootId
  terminalObligationsRoot : RootId
  oracleOccurrencePlanRoot : RootId
  deriving DecidableEq, Repr

/-- The exact runtime custody-receipt hash domain. -/
def receiptDomain : String := "asset-lane-custody-coordinator-receipt-v2"

/-- The exact nine-field receipt body of the runtime `_receipt_root`. It reads no
receipt root, so receipt identity is not self-referential. -/
structure ReceiptBody where
  route : String
  sourceLeafJournalRoot : RootId
  sourceLeafReceiptRoot : RootId
  preLaneRoot : RootId
  postLaneRoot : RootId
  effectPlanRoot : RootId
  privatePortRoot : RootId
  terminalObligationsRoot : RootId
  oracleOccurrencePlanRoot : RootId
  deriving DecidableEq, Repr

def receiptBody (route : Route) (sourceLeafJournalRoot sourceLeafReceiptRoot : RootId)
    (journal : Journal) : ReceiptBody :=
  { route := route.code
    sourceLeafJournalRoot := sourceLeafJournalRoot
    sourceLeafReceiptRoot := sourceLeafReceiptRoot
    preLaneRoot := journal.preLaneRoot
    postLaneRoot := journal.postLaneRoot
    effectPlanRoot := journal.effectPlanRoot
    privatePortRoot := journal.privatePortRoot
    terminalObligationsRoot := journal.terminalObligationsRoot
    oracleOccurrencePlanRoot := journal.oracleOccurrencePlanRoot }

/-- Root observers: the byte digest shared by both finite leaves and the
existing complete-state encoder, and the two existing scalar leaf root models.
None of them is an implementation of a runtime hash. -/
structure Roots where
  digest : B.Bytes → RootId
  transfer : T.RootModel
  managed : M.RootModel

/-- Runtime commitment functions, kept as explicit uninterpreted parameters. -/
structure Commitments where
  effectPlanRoot : EffectPlan → RootId
  journalRoot : Journal → RootId
  receiptRoot : String → ReceiptBody → RootId
  transferPolicy : T.Policy → String
  managedPolicy : M.Policy → String

/-- Typed coordinator input: the four complete-context coordinates the finite
leaf model omits, plus the existing mixed leaf action. -/
structure Input where
  chainId : String
  deploymentRoot : RootId
  profileRoot : RootId
  writerEpoch : Nat
  leaf : F.Action

/-- The source observation: no post state, route, verdict or flag. -/
structure SourceCandidate where
  journal : Journal
  effects : EffectPlan
  deriving DecidableEq, Repr

/-- The owned accepted result of `AssetLaneCustodyAcceptedV2`. -/
structure Accepted where
  route : Route
  sourceLeafJournalRoot : RootId
  sourceLeafReceiptRoot : RootId
  post : D.FullState
  effects : EffectPlan
  journal : Journal
  deriving DecidableEq, Repr

/-- Rejection retains no post state and no effects by construction. -/
inductive Outcome (pre : D.FullState) where
  | accepted (result : Accepted)
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

def Outcome.postState {pre : D.FullState} : Outcome pre → D.FullState
  | .accepted result => result.post
  | .rejected _ => pre

def Outcome.effects {pre : D.FullState} : Outcome pre → EffectPlan
  | .accepted result => result.effects
  | .rejected _ => EffectPlan.empty

def Outcome.route {pre : D.FullState} : Outcome pre → Route
  | .accepted result => result.route
  | .rejected code => code.route

/-! ## Internally derived leaf and complete observations -/

/-- The complete custody-state root reuses the existing complete-state encoder. -/
def completeRoot (digest : B.Bytes → RootId) (state : D.FullState) : RootId :=
  digest (D.stateBytes state)

/-- Stage 2: the actual finite leaf verdict, with the exact leaf code retained. -/
def leafVerdict (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → Option RejectCode
  | .transfer ctx command =>
      match (FT.transition digest ctx (E.transferSource (D.erase pre)) command).verdict with
      | .accepted => none
      | .rejected code => some (.transferLeaf code)
  | .managed ctx command =>
      match (FM.transition digest ctx (E.managedSource (D.erase pre)) command).verdict with
      | .accepted => none
      | .rejected code => some (.managedLeaf code)

def leafPreRoot (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → RootId
  | .transfer _ _ => FT.stateRoot digest (E.transferSource (D.erase pre))
  | .managed _ _ => FM.stateRoot digest (E.managedSource (D.erase pre))

def leafPostRoot (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → RootId
  | .transfer ctx command =>
      FT.stateRoot digest (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post
  | .managed ctx command =>
      FM.stateRoot digest (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post

/-- The existing command occurrence identity, read from the leaf context. -/
def occurrenceId : F.Action → Option RootId
  | .transfer ctx _ =>
      match ctx.occurrence with
      | none => none
      | some occurrence => some occurrence.occurrenceId
  | .managed ctx _ =>
      match ctx.occurrence with
      | none => none
      | some occurrence => some occurrence.occurrenceId

def contextRelease : F.Action → RootId
  | .transfer ctx _ => ctx.moduleReleaseId
  | .managed ctx _ => ctx.moduleReleaseId

def commandAsset : F.Action → Asset
  | .transfer _ command => command.asset
  | .managed _ command => command.asset

/-- The declared assets of the accepted leaf post, as the runtime projection
guard reads them. -/
def leafPolicyAssets (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → List Asset
  | .transfer ctx command =>
      (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post.policies.map
        (fun policy => policy.asset)
  | .managed ctx command =>
      (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post.policies.map
        (fun policy => policy.asset)

/-- Accounts-only complete pre total, exactly `pre.account_atoms(row.asset)`. -/
def accountsPre (pre : D.FullState) (action : F.Action) : Int :=
  amountForAsset pre.transfer.balances (commandAsset action)

/-- Accounts-only leaf post total, exactly the runtime sum over the accepted
leaf post balance rows for the command asset. -/
def accountsPost (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → Int
  | .transfer ctx command =>
      amountForAsset
        (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post.balances
        command.asset
  | .managed ctx command =>
      amountForAsset
        (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post.balances
        command.asset

/-- Complete pre supply, exactly `pre.transfer_state.supply_atoms(row.asset)`. -/
def supplyPre (pre : D.FullState) (action : F.Action) : Int :=
  C.supplyAt (D.erase pre) (commandAsset action)

def supplyPost (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → Int
  | .transfer ctx command =>
      supplyFor
        (numericRows (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post.supplies)
        command.asset
  | .managed ctx command =>
      supplyFor
        (numericRows (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post.supplies)
        command.asset

/-- The existing actual finite transfer or managed effect plan of the internally
derived leaf result. -/
def finitePlan (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → EffectPlan
  | .transfer ctx command => TP.transferPlan digest ctx (E.transferSource (D.erase pre)) command
  | .managed ctx command => MP.managedPlan digest ctx (E.managedSource (D.erase pre)) command

/-! ## Stage predicates -/

/-- The field equalities of Python `_source_holds` for the genuine command's
leaf class. Rust first validates the source candidate. Root syntax, fixed-schema
admission and faulty candidate-kind/post defense are external to this model.
Occurrence presence is the `occurrenceId` match in `transition`. -/
def SourceBindings (roots : Roots) (commits : Commitments) (pre : D.FullState) (action : Input)
    (occurrence : RootId) (source : SourceCandidate) : Prop :=
  source.journal.laneId = LaneId.assetTransfer ∧
    source.journal.chainId = action.chainId ∧
    source.journal.deploymentRoot = action.deploymentRoot ∧
    source.journal.profileRoot = action.profileRoot ∧
    source.journal.writerEpoch = action.writerEpoch ∧
    contextRelease action.leaf = pre.transfer.moduleReleaseId ∧
    source.journal.moduleReleaseId = pre.transfer.moduleReleaseId ∧
    source.journal.commandOccurrenceId = occurrence ∧
    source.journal.preLaneRoot = leafPreRoot roots.digest pre action.leaf ∧
    source.effects.occurrenceConsumptions = [occurrence] ∧
    source.effects.laneWrites =
      [⟨LaneId.assetTransfer, leafPreRoot roots.digest pre action.leaf,
        leafPostRoot roots.digest pre action.leaf⟩] ∧
    source.journal.postLaneRoot = leafPostRoot roots.digest pre action.leaf ∧
    source.journal.effectPlanRoot = commits.effectPlanRoot source.effects ∧
    source.effects.externalOutboxEnqueue = [] ∧
    source.journal.privatePortRoot = O.zeroRoot ∧
    source.journal.terminalObligationsRoot = O.zeroRoot ∧
    source.journal.oracleOccurrencePlanRoot = O.zeroRoot

instance sourceBindingsDecidable (roots : Roots) (commits : Commitments) (pre : D.FullState)
    (action : Input) (occurrence : RootId) (source : SourceCandidate) :
    Decidable (SourceBindings roots commits pre action occurrence source) := by
  unfold SourceBindings
  infer_instance

/-- Stage 4, enumerating every field of the runtime `_account_projection_holds`
guard, including exact one-row cardinality and accounts-only source totals. -/
def AccountProjection (asset : Asset) (leafAssets : List Asset)
    (accountsPreAtoms accountsPostAtoms supplyPreAtoms supplyPostAtoms : Int)
    (source : SourceCandidate) : Prop :=
  ∃ row ∈ source.effects.assetConservation,
    source.effects.assetConservation = [row] ∧
      row.asset = asset ∧
      row.asset ∈ leafAssets ∧
      row.ownedAndCustodiedPreAtoms = accountsPreAtoms ∧
      row.ownedAndCustodiedPostAtoms = accountsPostAtoms ∧
      row.supplyPreAtoms = supplyPreAtoms ∧
      row.supplyPostAtoms = supplyPostAtoms

def Projection (roots : Roots) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) : Prop :=
  AccountProjection (commandAsset action.leaf) (leafPolicyAssets roots.digest pre action.leaf)
    (accountsPre pre action.leaf) (accountsPost roots.digest pre action.leaf)
    (supplyPre pre action.leaf) (supplyPost roots.digest pre action.leaf) source

instance projectionDecidable (roots : Roots) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) : Decidable (Projection roots pre action source) := by
  unfold Projection AccountProjection
  infer_instance

/-- Stage 6: the exact full leaf reprojection of the derived complete post, with
every transfer policy preserved. -/
def Reprojection (digest : B.Bytes → RootId) (pre : D.FullState) : F.Action → Prop
  | .transfer ctx command =>
      (D.step digest pre (.transfer ctx command)).transfer =
          (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post ∧
        (D.step digest pre (.transfer ctx command)).transfer.policies = pre.transfer.policies
  | .managed ctx command =>
      E.managedSource (D.erase (D.step digest pre (.managed ctx command))) =
          (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post ∧
        (D.step digest pre (.managed ctx command)).transfer.policies = pre.transfer.policies

instance reprojectionDecidable (digest : B.Bytes → RootId) (pre : D.FullState)
    (action : F.Action) : Decidable (Reprojection digest pre action) := by
  cases action with
  | transfer ctx command => exact inferInstanceAs (Decidable (_ ∧ _))
  | managed ctx command => exact inferInstanceAs (Decidable (_ ∧ _))

instance policyOriginBindingsDecidable (transferCommit : T.Policy → String)
    (managedCommit : M.Policy → String) (state : D.FullState) :
    Decidable (A.PolicyOriginBindings transferCommit managedCommit state) := by
  unfold A.PolicyOriginBindings
  infer_instance

/-! ## Stage 7 completion -/

/-- Complete physical conservation totals and the one complete-state lane write;
every other source effect field is retained exactly. -/
def completedEffects (digest : B.Bytes → RootId) (pre : D.FullState) (action : F.Action)
    (source : SourceCandidate) : EffectPlan :=
  E.completePlan (D.erase pre) (D.erase (D.step digest pre action)) (completeRoot digest pre)
    (completeRoot digest (D.step digest pre action)) source.effects

/-- The source journal rebound to the complete pre/post roots and the completed
effect-plan root, before receipt identity is computed. -/
def reboundJournal (roots : Roots) (commits : Commitments) (pre : D.FullState)
    (action : F.Action) (source : SourceCandidate) : Journal :=
  { source.journal with
    preLaneRoot := completeRoot roots.digest pre
    postLaneRoot := completeRoot roots.digest (D.step roots.digest pre action)
    effectPlanRoot := commits.effectPlanRoot (completedEffects roots.digest pre action source) }

/-- The receipt commits to the derived route, both source leaf roots and the
rebound journal frame. -/
def completedReceiptBody (roots : Roots) (commits : Commitments) (pre : D.FullState)
    (action : F.Action) (source : SourceCandidate) : ReceiptBody :=
  receiptBody (routeOf action) (commits.journalRoot source.journal) source.journal.receiptRoot
    (reboundJournal roots commits pre action source)

def completedJournal (roots : Roots) (commits : Commitments) (pre : D.FullState)
    (action : F.Action) (source : SourceCandidate) : Journal :=
  { reboundJournal roots commits pre action source with
    receiptRoot :=
      commits.receiptRoot receiptDomain (completedReceiptBody roots commits pre action source) }

def completed (roots : Roots) (commits : Commitments) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) : Accepted :=
  { route := routeOf action.leaf
    sourceLeafJournalRoot := commits.journalRoot source.journal
    sourceLeafReceiptRoot := source.journal.receiptRoot
    post := D.step roots.digest pre action.leaf
    effects := completedEffects roots.digest pre action.leaf source
    journal := completedJournal roots commits pre action.leaf source }

/-- The recheck performed by the runtime accepted-result constructor. Some of
its conjuncts duplicate stage 3; they are stated for honest field
correspondence, not as independent guards. -/
structure AcceptedBindings (roots : Roots) (commits : Commitments) (result : Accepted) : Prop where
  namedLeaf : result.route ≠ Route.coordinator
  laneId : result.journal.laneId = LaneId.assetTransfer
  moduleReleaseId : result.journal.moduleReleaseId = result.post.transfer.moduleReleaseId
  postLaneRoot : result.journal.postLaneRoot = completeRoot roots.digest result.post
  effectPlanRoot : result.journal.effectPlanRoot = commits.effectPlanRoot result.effects
  laneWrites : result.effects.laneWrites =
    [⟨LaneId.assetTransfer, result.journal.preLaneRoot, completeRoot roots.digest result.post⟩]
  occurrenceConsumptions :
    result.effects.occurrenceConsumptions = [result.journal.commandOccurrenceId]
  externalOutboxEnqueue : result.effects.externalOutboxEnqueue = []
  privatePortRoot : result.journal.privatePortRoot = O.zeroRoot
  terminalObligationsRoot : result.journal.terminalObligationsRoot = O.zeroRoot
  oracleOccurrencePlanRoot : result.journal.oracleOccurrencePlanRoot = O.zeroRoot
  receiptRoot : result.journal.receiptRoot = commits.receiptRoot receiptDomain
    (receiptBody result.route result.sourceLeafJournalRoot result.sourceLeafReceiptRoot
      result.journal)
  originBindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy result.post

/-! ## The ordered transition -/

/-- Stages 3 to 7 on the internally derived leaf result. -/
def stages (roots : Roots) (commits : Commitments) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) (occurrence : RootId) : Outcome pre :=
  if SourceBindings roots commits pre action occurrence source then
    if Projection roots pre action source then
      if D.Resources (D.step roots.digest pre action.leaf) then
        if Reprojection roots.digest pre action.leaf then
          .accepted (completed roots commits pre action source)
        else .rejected (.coordinator .projectionMismatch)
      else .rejected (.coordinator .stateResourceLimit)
    else .rejected (.coordinator .projectionMismatch)
  else .rejected (.coordinator .candidateBindingMismatch)

/-- The whole ordered coordinator decision. Stage 1 precedes leaf dispatch;
the leaf verdict and every completed field are derived internally. -/
def transition (roots : Roots) (commits : Commitments) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) : Outcome pre :=
  if A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre then
    match leafVerdict roots.digest pre action.leaf with
    | some code => .rejected code
    | none =>
        match occurrenceId action.leaf with
        | none => .rejected (.coordinator .candidateBindingMismatch)
        | some occurrence => stages roots commits pre action source occurrence
  else .rejected (.coordinator .registryBindingMismatch)

/-! ## Source relation and finite refinement -/

/-- The source premise assumes the observed journal coordinates and the
context/pre-state release relation, plus refinement of the source effects to
the actual finite plan; every effect-side field of `SourceBindings` is derived. -/
structure SourceRelation (roots : Roots) (commits : Commitments) (pre : D.FullState)
    (action : Input) (source : SourceCandidate) : Prop where
  laneId : source.journal.laneId = LaneId.assetTransfer
  chainId : source.journal.chainId = action.chainId
  deploymentRoot : source.journal.deploymentRoot = action.deploymentRoot
  profileRoot : source.journal.profileRoot = action.profileRoot
  writerEpoch : source.journal.writerEpoch = action.writerEpoch
  release : contextRelease action.leaf = pre.transfer.moduleReleaseId
  moduleReleaseId : source.journal.moduleReleaseId = pre.transfer.moduleReleaseId
  preLaneRoot : source.journal.preLaneRoot = leafPreRoot roots.digest pre action.leaf
  postLaneRoot : source.journal.postLaneRoot = leafPostRoot roots.digest pre action.leaf
  effectPlanRoot : source.journal.effectPlanRoot = commits.effectPlanRoot source.effects
  privatePortRoot : source.journal.privatePortRoot = O.zeroRoot
  terminalObligationsRoot : source.journal.terminalObligationsRoot = O.zeroRoot
  oracleOccurrencePlanRoot : source.journal.oracleOccurrencePlanRoot = O.zeroRoot
  commandOccurrenceId : ∀ occurrence, occurrenceId action.leaf = some occurrence →
    source.journal.commandOccurrenceId = occurrence
  refines : source.effects = finitePlan roots.digest pre action.leaf

/-- `SourceRefinesFinite` names the refinement conjunct on its own: the observed
source effects are exactly the existing actual finite transfer or managed effect
plan of the internally derived leaf result. -/
def SourceRefinesFinite (roots : Roots) (pre : D.FullState) (action : Input)
    (source : SourceCandidate) : Prop :=
  source.effects = finitePlan roots.digest pre action.leaf

/-- The completed result satisfies the modeled accepted-constructor bindings.
The source relation supplies the observed journal fields; post policy bindings
come from preservation. Root syntax and hashing remain external premises. -/
theorem completed_accepted_bindings {roots : Roots} {commits : Commitments}
    {pre : D.FullState} {action : Input} {source : SourceCandidate} {occurrence : RootId}
    (sourceOk : SourceBindings roots commits pre action occurrence source)
    (postBindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
      (D.step roots.digest pre action.leaf)) :
    AcceptedBindings roots commits (completed roots commits pre action source) := by
  rcases sourceOk with ⟨lane, _, _, _, _, _, release, occurrenceId, _, consumptions,
    _, _, _, outbox, privateRoot, terminalRoot, oracleRoot⟩
  refine {
    namedLeaf := ?_
    laneId := lane
    moduleReleaseId := ?_
    postLaneRoot := rfl
    effectPlanRoot := rfl
    laneWrites := rfl
    occurrenceConsumptions := ?_
    externalOutboxEnqueue := outbox
    privatePortRoot := privateRoot
    terminalObligationsRoot := terminalRoot
    oracleOccurrencePlanRoot := oracleRoot
    receiptRoot := rfl
    originBindings := postBindings }
  · show routeOf action.leaf ≠ Route.coordinator
    cases action.leaf <;> simp [routeOf]
  · show source.journal.moduleReleaseId =
      (D.step roots.digest pre action.leaf).transfer.moduleReleaseId
    rw [release, (D.step_transfer_metadata roots.digest pre action.leaf).1]
  · show source.effects.occurrenceConsumptions = [source.journal.commandOccurrenceId]
    rw [consumptions, occurrenceId]

/-! ## Rejection, order and completion theorems -/

/-- Rejection is an exact no-op with the caller's pre state, the six empty
effect fields, and the route owned by the code constructor. -/
theorem rejected_is_exact_no_op (pre : D.FullState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).postState = pre ∧
      (Outcome.rejected code : Outcome pre).effects = EffectPlan.empty ∧
      (Outcome.rejected code : Outcome pre).effects.IsEmpty ∧
      (Outcome.rejected code : Outcome pre).route = code.route :=
  ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Coordinator codes and leaf codes are distinguished by route, and the four
coordinator wire codes are exactly the runtime enumeration. Note that
`STATE_RESOURCE_LIMIT` is a shared wire string across routes. -/
theorem rejection_codes_are_route_closed :
    (∀ code : CoordinatorRejectCode, (RejectCode.coordinator code).route = Route.coordinator) ∧
      (∀ code : FT.RejectCode, (RejectCode.transferLeaf code).route = Route.transfer) ∧
      (∀ code : FM.RejectCode, (RejectCode.managedLeaf code).route = Route.managedLifecycle) ∧
      allCoordinatorRejectCodes.map CoordinatorRejectCode.code =
        ["REGISTRY_BINDING_MISMATCH", "CANDIDATE_BINDING_MISMATCH", "PROJECTION_MISMATCH",
          "STATE_RESOURCE_LIMIT"] :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

/-- Stage 1 precedes leaf dispatch, the source packet and every later stage. -/
theorem registry_binding_mismatch_precedes_leaf (roots : Roots) (commits : Commitments)
    (pre : D.FullState) (action : Input) (source : SourceCandidate)
    (mismatch : ¬ A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre) :
    transition roots commits pre action source =
      .rejected (.coordinator .registryBindingMismatch) := by
  unfold transition
  rw [if_neg mismatch]

/-- Stage 2 retains the exact finite leaf code and its leaf route. -/
theorem leaf_rejection_preserves_route_and_code (roots : Roots) (commits : Commitments)
    (pre : D.FullState) (action : Input) (source : SourceCandidate) (code : RejectCode)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (verdict : leafVerdict roots.digest pre action.leaf = some code) :
    transition roots commits pre action source = .rejected code ∧
      code.route = routeOf action.leaf := by
  constructor
  · unfold transition
    rw [if_pos bindings, verdict]
  · obtain ⟨chainId, deploymentRoot, profileRoot, writerEpoch, leaf⟩ := action
    have shape : leafVerdict roots.digest pre leaf = some code := verdict
    cases leaf with
    | transfer ctx command =>
        cases inner : (FT.transition roots.digest ctx (E.transferSource (D.erase pre))
            command).verdict with
        | accepted =>
            rw [show leafVerdict roots.digest pre (.transfer ctx command) = none by
              simp only [leafVerdict, inner]] at shape
            exact absurd shape (by simp)
        | rejected leafCode =>
            rw [show leafVerdict roots.digest pre (.transfer ctx command) =
                some (.transferLeaf leafCode) by simp only [leafVerdict, inner]] at shape
            rw [← Option.some.inj shape]
            rfl
    | managed ctx command =>
        cases inner : (FM.transition roots.digest ctx (E.managedSource (D.erase pre))
            command).verdict with
        | accepted =>
            rw [show leafVerdict roots.digest pre (.managed ctx command) = none by
              simp only [leafVerdict, inner]] at shape
            exact absurd shape (by simp)
        | rejected leafCode =>
            rw [show leafVerdict roots.digest pre (.managed ctx command) =
                some (.managedLeaf leafCode) by simp only [leafVerdict, inner]] at shape
            rw [← Option.some.inj shape]
            rfl

private theorem transition_stages {roots : Roots} {commits : Commitments} {pre : D.FullState}
    {action : Input} {source : SourceCandidate} {occurrence : RootId}
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (verdict : leafVerdict roots.digest pre action.leaf = none)
    (present : occurrenceId action.leaf = some occurrence) :
    transition roots commits pre action source = stages roots commits pre action source occurrence := by
  unfold transition
  rw [if_pos bindings]
  simp only [verdict, present]

/-- Missing occurrence owns a leaf-specific typed rejection code. -/
def missingOccurrenceCode : F.Action → RejectCode
  | .transfer _ _ => .transferLeaf (.economic .missingOccurrence)
  | .managed _ _ => .managedLeaf (.economic .missingOccurrence)

/-- Both actual finite leaves check occurrence presence first. -/
theorem missing_occurrence_leaf_verdict (digest : B.Bytes → RootId) (pre : D.FullState)
    (action : F.Action) (absent : occurrenceId action = none) :
    leafVerdict digest pre action = some (missingOccurrenceCode action) := by
  cases action with
  | transfer ctx command =>
      cases present : ctx.occurrence with
      | none =>
          simp [leafVerdict, missingOccurrenceCode, FT.transition,
            AssetTransferFiniteOutcomeV2.economicRejectCode,
            AssetTransferFiniteOutcomeV2.contextRejectCode,
            AssetTransferFiniteOutcomeV2.reject, present]
      | some occurrence => simp [occurrenceId, present] at absent
  | managed ctx command =>
      cases present : ctx.occurrence with
      | none =>
          simp [leafVerdict, missingOccurrenceCode, FM.transition,
            ManagedAssetFiniteOutcomeV2.economicRejectCode,
            ManagedAssetFiniteOutcomeV2.contextRejectCode,
            ManagedAssetFiniteOutcomeV2.reject, present]
      | some occurrence => simp [occurrenceId, present] at absent

/-- An actual accepted finite leaf always supplies an occurrence. This rules
out the coordinator's defensive missing-occurrence branch on actual leaves. -/
theorem accepted_leaf_has_occurrence (digest : B.Bytes → RootId) (pre : D.FullState)
    (action : F.Action) (accepted : leafVerdict digest pre action = none) :
    ∃ occurrence, occurrenceId action = some occurrence := by
  cases present : occurrenceId action with
  | none =>
      have rejected := missing_occurrence_leaf_verdict digest pre action present
      rw [accepted] at rejected
      cases rejected
  | some occurrence => exact ⟨occurrence, rfl⟩

/-- Once registry binding passes, a missing occurrence returns the exact
MISSING_OCCURRENCE leaf code, its route, and the unchanged state and empty plan. -/
theorem missing_occurrence_is_leaf_rejection (roots : Roots) (commits : Commitments)
    (pre : D.FullState) (action : Input) (source : SourceCandidate)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (absent : occurrenceId action.leaf = none) :
    transition roots commits pre action source = .rejected (missingOccurrenceCode action.leaf) ∧
      (missingOccurrenceCode action.leaf).route = routeOf action.leaf ∧
      (transition roots commits pre action source).postState = pre ∧
      (transition roots commits pre action source).effects = EffectPlan.empty := by
  have verdict := missing_occurrence_leaf_verdict roots.digest pre action.leaf absent
  obtain ⟨outcome, route⟩ := leaf_rejection_preserves_route_and_code roots commits pre
    action source (missingOccurrenceCode action.leaf) bindings verdict
  exact ⟨outcome, route, by rw [outcome]; rfl, by rw [outcome]; rfl⟩

/-- The exact stage order: source mismatch precedes the projection, the
aggregate resource decision and the late reprojection; the projection precedes
the resource decision; and the resource decision precedes the reprojection. -/
theorem staged_rejection_order {roots : Roots} {commits : Commitments} {pre : D.FullState}
    {action : Input} {source : SourceCandidate} {occurrence : RootId}
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (verdict : leafVerdict roots.digest pre action.leaf = none)
    (present : occurrenceId action.leaf = some occurrence) :
    (¬ SourceBindings roots commits pre action occurrence source →
        transition roots commits pre action source =
          .rejected (.coordinator .candidateBindingMismatch)) ∧
      (SourceBindings roots commits pre action occurrence source →
        ¬ Projection roots pre action source →
        transition roots commits pre action source =
          .rejected (.coordinator .projectionMismatch)) ∧
      (SourceBindings roots commits pre action occurrence source →
        Projection roots pre action source →
        ¬ D.Resources (D.step roots.digest pre action.leaf) →
        transition roots commits pre action source =
          .rejected (.coordinator .stateResourceLimit)) ∧
      (SourceBindings roots commits pre action occurrence source →
        Projection roots pre action source →
        D.Resources (D.step roots.digest pre action.leaf) →
        ¬ Reprojection roots.digest pre action.leaf →
        transition roots commits pre action source =
          .rejected (.coordinator .projectionMismatch)) := by
  have staged := transition_stages (source := source) bindings verdict present
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mismatch
    rw [staged]
    unfold stages
    rw [if_neg mismatch]
  · intro sourceOk mismatch
    rw [staged]
    unfold stages
    rw [if_pos sourceOk, if_neg mismatch]
  · intro sourceOk projectionOk limit
    rw [staged]
    unfold stages
    rw [if_pos sourceOk, if_pos projectionOk, if_neg limit]
  · intro sourceOk projectionOk fits mismatch
    rw [staged]
    unfold stages
    rw [if_pos sourceOk, if_pos projectionOk, if_pos fits, if_neg mismatch]

/-- Once every stage passes, the result is the internally derived post, effects,
journal and source roots. This is a construction equation, not authorization;
the accepted route theorems additionally require exact finite-plan refinement. -/
theorem accepted_outcome_is_internally_derived {roots : Roots} {commits : Commitments}
    {pre : D.FullState} {action : Input} {source : SourceCandidate} {occurrence : RootId}
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (verdict : leafVerdict roots.digest pre action.leaf = none)
    (present : occurrenceId action.leaf = some occurrence)
    (sourceOk : SourceBindings roots commits pre action occurrence source)
    (projectionOk : Projection roots pre action source)
    (fits : D.Resources (D.step roots.digest pre action.leaf))
    (reprojectionOk : Reprojection roots.digest pre action.leaf) :
    transition roots commits pre action source =
        .accepted (completed roots commits pre action source) ∧
      (completed roots commits pre action source).route = routeOf action.leaf ∧
      (completed roots commits pre action source).post = D.step roots.digest pre action.leaf ∧
      (completed roots commits pre action source).effects =
        completedEffects roots.digest pre action.leaf source ∧
      (completed roots commits pre action source).journal =
        completedJournal roots commits pre action.leaf source ∧
      (completed roots commits pre action source).sourceLeafJournalRoot =
        commits.journalRoot source.journal ∧
      (completed roots commits pre action source).sourceLeafReceiptRoot =
        source.journal.receiptRoot := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [transition_stages bindings verdict present]
  unfold stages
  rw [if_pos sourceOk, if_pos projectionOk, if_pos fits, if_pos reprojectionOk]

/-- Completion never mutates the retained source fields: rows, fees, occurrence
consumptions and the outbox are exactly the source ones, while the two physical
conservation totals and the single lane write are the complete-state ones.
This is Python/model behavior for arbitrary source plans. Rust clears outbox;
cross-runtime correspondence therefore requires the admitted empty outbox. -/
theorem completed_effects_retain_source_fields (digest : B.Bytes → RootId) (pre : D.FullState)
    (action : F.Action) (source : SourceCandidate) :
    (completedEffects digest pre action source).rows = source.effects.rows ∧
      (completedEffects digest pre action source).feeConservation =
        source.effects.feeConservation ∧
      (completedEffects digest pre action source).occurrenceConsumptions =
        source.effects.occurrenceConsumptions ∧
      (completedEffects digest pre action source).externalOutboxEnqueue =
        source.effects.externalOutboxEnqueue ∧
      (completedEffects digest pre action source).assetConservation =
        source.effects.assetConservation.map
          (E.completeConservationRow (D.erase pre) (D.erase (D.step digest pre action))) ∧
      (completedEffects digest pre action source).laneWrites =
        [⟨LaneId.assetTransfer, completeRoot digest pre,
          completeRoot digest (D.step digest pre action)⟩] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The receipt body distinguishes the two source leaf roots and distinguishes
the complete aggregate pre root from the leaf pre root, so a self-consistent
journal mutant that substitutes one for the other is not the actual body. -/
theorem receipt_body_binds_source_and_aggregate_frame (route : Route)
    (sourceLeafJournalRoot sourceLeafReceiptRoot leafRoot : RootId) (journal : Journal) :
    (sourceLeafJournalRoot ≠ sourceLeafReceiptRoot →
        receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot journal ≠
          receiptBody route sourceLeafReceiptRoot sourceLeafReceiptRoot journal) ∧
      (journal.preLaneRoot ≠ leafRoot →
        receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot journal ≠
          receiptBody route sourceLeafJournalRoot sourceLeafReceiptRoot
            { journal with preLaneRoot := leafRoot }) := by
  constructor
  · intro different equal
    exact different (congrArg ReceiptBody.sourceLeafJournalRoot equal)
  · intro different equal
    exact different (congrArg ReceiptBody.preLaneRoot equal)

/-! ## Accepted derivations from the actual finite leaves -/

private theorem transfer_erase_post {digest : B.Bytes → RootId} {pre : D.FullState}
    {ctx : T.Context} {command : T.Command}
    (accepted : (FT.transition digest ctx (E.transferSource (D.erase pre)) command).verdict =
      .accepted) :
    D.erase (D.step digest pre (.transfer ctx command)) =
      E.transferPostFromLeaf (D.erase pre)
        (FT.transition digest ctx (E.transferSource (D.erase pre)) command).post := by
  rw [D.erase_step]
  simp only [F.step, accepted]

private theorem managed_erase_post {digest : B.Bytes → RootId} {pre : D.FullState}
    {ctx : M.Context} {command : M.Command}
    (accepted : (FM.transition digest ctx (E.managedSource (D.erase pre)) command).verdict =
      .accepted) :
    D.erase (D.step digest pre (.managed ctx command)) =
      E.managedPostFromLeaf (D.erase pre)
        (FM.transition digest ctx (E.managedSource (D.erase pre)) command).post := by
  rw [D.erase_step]
  simp only [F.step, accepted]

private theorem transfer_completed_effects {roots : Roots} {pre : D.FullState} {ctx : T.Context}
    {command : T.Command} {policy : T.Policy} {source : SourceCandidate}
    (selected : FT.policyFor (E.transferSource (D.erase pre)) command.asset = some policy)
    (accepted : (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).verdict =
      .accepted)
    (refines : source.effects =
      TP.transferPlan roots.digest ctx (E.transferSource (D.erase pre)) command) :
    completedEffects roots.digest pre (.transfer ctx command) source =
      E.transferEffectPlan roots.digest ctx (D.erase pre) command (completeRoot roots.digest pre)
        (completeRoot roots.digest (D.step roots.digest pre (.transfer ctx command))) := by
  unfold completedEffects E.transferEffectPlan
  simp only [accepted, selected]
  rw [refines, transfer_erase_post accepted]

private theorem managed_completed_effects {roots : Roots} {pre : D.FullState} {ctx : M.Context}
    {command : M.Command} {source : SourceCandidate}
    (accepted : (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).verdict =
      .accepted)
    (refines : source.effects =
      MP.managedPlan roots.digest ctx (E.managedSource (D.erase pre)) command) :
    completedEffects roots.digest pre (.managed ctx command) source =
      E.managedEffectPlan roots.digest ctx (D.erase pre) command (completeRoot roots.digest pre)
        (completeRoot roots.digest (D.step roots.digest pre (.managed ctx command))) := by
  unfold completedEffects E.managedEffectPlan
  simp only [accepted]
  rw [refines, managed_erase_post accepted]

/-- Under initial constructor admission, policy binding, input shape, the actual
finite transfer acceptance, the source relation and complete post resource fit,
the coordinator accepts with the internally computed post; the leaf
authorization verdict, the derived source bindings, the exact one-row
projection, preserved constructor admission and policy binding, completed
effect-plan admission, the exact completed conservation row and lane write, and
the accepted journal and receipt fields all follow. No accepted outcome, post
state or success flag is assumed. -/
theorem accepted_transfer_outcome {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {roots : Roots} {commits : Commitments}
    {pre : D.FullState} {action : Input} {ctx : T.Context} {command : T.Command}
    {source : SourceCandidate}
    (admitted : A.ConstructorAdmission rootSyntax namespaceSyntax pre)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (input : X.ActionAdmission (.transfer ctx command))
    (shape : action.leaf = .transfer ctx command)
    (accepted : (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).verdict =
      .accepted)
    (relation : SourceRelation roots commits pre action source)
    (fits : D.Resources (D.step roots.digest pre action.leaf)) :
    ∃ policy occurrence,
      FT.policyFor (E.transferSource (D.erase pre)) command.asset = some policy ∧
        policy ∈ pre.transfer.policies ∧
        (AssetTransferRefinementV2.transition roots.transfer ctx
          (C.transferView (D.erase pre) policy) command).verdict = .accepted ∧
        occurrenceId action.leaf = some occurrence ∧
        SourceBindings roots commits pre action occurrence source ∧
        Projection roots pre action source ∧
        Reprojection roots.digest pre action.leaf ∧
        transition roots commits pre action source =
          .accepted (completed roots commits pre action source) ∧
        (completed roots commits pre action source).post = D.step roots.digest pre action.leaf ∧
        A.ConstructorAdmission rootSyntax namespaceSyntax (D.step roots.digest pre action.leaf) ∧
        A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
          (D.step roots.digest pre action.leaf) ∧
        EffectPlanAdmitted (completedEffects roots.digest pre action.leaf source) ∧
        (completedEffects roots.digest pre action.leaf source).assetConservation =
          [E.transferCompletedConservation (D.erase pre)
            (D.erase (D.step roots.digest pre action.leaf)) command] ∧
        AssetConservationAdmitted (E.transferCompletedConservation (D.erase pre)
          (D.erase (D.step roots.digest pre action.leaf)) command) ∧
        (completedEffects roots.digest pre action.leaf source).laneWrites =
          [⟨LaneId.assetTransfer, completeRoot roots.digest pre,
            completeRoot roots.digest (D.step roots.digest pre action.leaf)⟩] ∧
        AcceptedBindings roots commits (completed roots commits pre action source) := by
  obtain ⟨chainId, deploymentRoot, profileRoot, writerEpoch, leaf⟩ := action
  have leafShape : leaf = (show F.Action from .transfer ctx command) := shape
  subst leafShape
  have structural := X.transfer_source_structural admitted.1
  obtain ⟨planPolicy, planOccurrence, planSelected, planPresent, planEq⟩ :=
    TP.transfer_accepted_fields accepted
  obtain ⟨policy, selected, member, scalar, fields⟩ :=
    E.transfer_accepted_completion (completePreRoot := completeRoot roots.digest pre)
      (completePostRoot :=
        completeRoot roots.digest (D.step roots.digest pre (.transfer ctx command)))
      roots.transfer admitted.1.rows structural accepted
  have conservationFields :
      (E.transferEffectPlan roots.digest ctx (D.erase pre) command (completeRoot roots.digest pre)
          (completeRoot roots.digest
            (D.step roots.digest pre (.transfer ctx command)))).assetConservation =
        [E.transferCompletedConservation (D.erase pre)
          (E.transferPostFromLeaf (D.erase pre)
            (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post)
          command] := fields.2.1
  have conservationAdmitted :
      AssetConservationAdmitted (E.transferCompletedConservation (D.erase pre)
        (E.transferPostFromLeaf (D.erase pre)
          (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post)
        command) := fields.2.2.1
  have planAdmitted :
      EffectPlanAdmitted (E.transferEffectPlan roots.digest ctx (D.erase pre) command
        (completeRoot roots.digest pre)
        (completeRoot roots.digest (D.step roots.digest pre (.transfer ctx command)))) :=
    fields.2.2.2.1
  have effectsEq : source.effects =
      TP.transferPlan roots.digest ctx (E.transferSource (D.erase pre)) command := relation.refines
  have occurrences : source.effects.occurrenceConsumptions = [planOccurrence.occurrenceId] := by
    rw [effectsEq, planEq]
  have lanes : source.effects.laneWrites =
      [⟨LaneId.assetTransfer, FT.stateRoot roots.digest (E.transferSource (D.erase pre)),
        FT.stateRoot roots.digest
          (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post⟩] := by
    rw [effectsEq, planEq]
  have outbox : source.effects.externalOutboxEnqueue = [] := by
    rw [effectsEq, planEq]
  have conservation : source.effects.assetConservation =
      [TP.transferConservation (E.transferSource (D.erase pre))
        (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post command] := by
    rw [effectsEq, planEq]
  have present : occurrenceId ((show F.Action from .transfer ctx command)) = some planOccurrence.occurrenceId := by
    simp only [occurrenceId, planPresent]
  have policyAssets : command.asset ∈
      leafPolicyAssets roots.digest pre ((show F.Action from .transfer ctx command)) := by
    show command.asset ∈
      (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post.policies.map
        (fun leafPolicy => leafPolicy.asset)
    rw [(FT.accepted_post_effects accepted).1, (FT.candidate_immutable _ command).2.1]
    exact List.mem_map.mpr ⟨policy, member, (FT.policyFor_spec selected).2⟩
  have sourceOk : SourceBindings roots commits pre
      ⟨chainId, deploymentRoot, profileRoot, writerEpoch, .transfer ctx command⟩
      planOccurrence.occurrenceId source := by
    refine ⟨relation.laneId, relation.chainId, relation.deploymentRoot,
      relation.profileRoot, relation.writerEpoch, relation.release, relation.moduleReleaseId,
      relation.commandOccurrenceId _ present, relation.preLaneRoot, occurrences, ?_,
      relation.postLaneRoot, relation.effectPlanRoot, outbox, relation.privatePortRoot,
      relation.terminalObligationsRoot, relation.oracleOccurrencePlanRoot⟩
    exact lanes
  have projection : Projection roots pre
      ⟨chainId, deploymentRoot, profileRoot, writerEpoch, .transfer ctx command⟩ source := by
    unfold Projection AccountProjection
    refine ⟨TP.transferConservation (E.transferSource (D.erase pre))
        (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post command,
      ?_, conservation, rfl, policyAssets, rfl, rfl, rfl, rfl⟩
    rw [conservation]
    exact List.mem_singleton.mpr rfl
  have acceptedFull : (FT.transition roots.digest ctx pre.transfer command).verdict = .accepted := by
    rw [← D.erase_transfer_source pre]
    exact accepted
  have reprojection : Reprojection roots.digest pre ((show F.Action from .transfer ctx command)) := by
    refine ⟨?_, (D.step_transfer_metadata roots.digest pre (.transfer ctx command)).2⟩
    show (D.step roots.digest pre (.transfer ctx command)).transfer =
      (FT.transition roots.digest ctx (E.transferSource (D.erase pre)) command).post
    rw [D.erase_transfer_source pre]
    exact A.transfer_accepted_full_projection acceptedFull
  have verdictNone : leafVerdict roots.digest pre ((show F.Action from .transfer ctx command)) = none := by
    simp only [leafVerdict, accepted]
  have outcome := accepted_outcome_is_internally_derived (source := source) bindings verdictNone
    present sourceOk projection fits reprojection
  have postAdmitted := A.step_preserves_constructor_admission roots.digest admitted input fits
  have postBindings := A.policy_origin_bindings_preserved roots.digest pre
    (.transfer ctx command) bindings
  have completedEq := transfer_completed_effects selected accepted effectsEq
  have completedAdmitted : EffectPlanAdmitted
      (completedEffects roots.digest pre (.transfer ctx command) source) := by
    rw [completedEq]
    exact planAdmitted
  have completedConservation :
      (completedEffects roots.digest pre (.transfer ctx command) source).assetConservation =
        [E.transferCompletedConservation (D.erase pre)
          (D.erase (D.step roots.digest pre (.transfer ctx command))) command] := by
    rw [completedEq, conservationFields, transfer_erase_post accepted]
  have completedRowAdmitted : AssetConservationAdmitted
      (E.transferCompletedConservation (D.erase pre)
        (D.erase (D.step roots.digest pre (.transfer ctx command))) command) := by
    rw [transfer_erase_post accepted]
    exact conservationAdmitted
  refine ⟨policy, planOccurrence.occurrenceId, selected, member, scalar, present, sourceOk,
    projection, reprojection, outcome.1, rfl, postAdmitted, postBindings, completedAdmitted,
    completedConservation, completedRowAdmitted, rfl, ?_⟩
  exact completed_accepted_bindings sourceOk postBindings

/-- The managed route derives the same accepted outcome from the actual finite
managed acceptance. The accounts-only source totals are recovered from the
managed projection of the complete tables, so every managed sibling and dormant
zero-valued supply row is retained. -/
theorem accepted_managed_outcome {rootSyntax : String → Prop}
    {namespaceSyntax : String → T.AssetClass → Prop} {roots : Roots} {commits : Commitments}
    {pre : D.FullState} {action : Input} {ctx : M.Context} {command : M.Command}
    {source : SourceCandidate}
    (admitted : A.ConstructorAdmission rootSyntax namespaceSyntax pre)
    (bindings : A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy pre)
    (input : X.ActionAdmission (.managed ctx command))
    (shape : action.leaf = .managed ctx command)
    (accepted : (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).verdict =
      .accepted)
    (relation : SourceRelation roots commits pre action source)
    (fits : D.Resources (D.step roots.digest pre action.leaf)) :
    ∃ policy occurrence,
      FM.policyFor (E.managedSource (D.erase pre)) command.asset = some policy ∧
        policy ∈ pre.managedPolicies ∧
        (ManagedAssetLifecycleRefinementV2.transition roots.managed ctx
          (C.managedView (D.erase pre) policy) command).verdict = .accepted ∧
        occurrenceId action.leaf = some occurrence ∧
        SourceBindings roots commits pre action occurrence source ∧
        Projection roots pre action source ∧
        Reprojection roots.digest pre action.leaf ∧
        transition roots commits pre action source =
          .accepted (completed roots commits pre action source) ∧
        (completed roots commits pre action source).post = D.step roots.digest pre action.leaf ∧
        A.ConstructorAdmission rootSyntax namespaceSyntax (D.step roots.digest pre action.leaf) ∧
        A.PolicyOriginBindings commits.transferPolicy commits.managedPolicy
          (D.step roots.digest pre action.leaf) ∧
        EffectPlanAdmitted (completedEffects roots.digest pre action.leaf source) ∧
        (completedEffects roots.digest pre action.leaf source).assetConservation =
          [E.managedCompletedConservation (D.erase pre)
            (D.erase (D.step roots.digest pre action.leaf)) command] ∧
        AssetConservationAdmitted (E.managedCompletedConservation (D.erase pre)
          (D.erase (D.step roots.digest pre action.leaf)) command) ∧
        (completedEffects roots.digest pre action.leaf source).laneWrites =
          [⟨LaneId.assetTransfer, completeRoot roots.digest pre,
            completeRoot roots.digest (D.step roots.digest pre action.leaf)⟩] ∧
        AcceptedBindings roots commits (completed roots commits pre action source) := by
  obtain ⟨chainId, deploymentRoot, profileRoot, writerEpoch, leaf⟩ := action
  have leafShape : leaf = (show F.Action from .managed ctx command) := shape
  subst leafShape
  have structural : FM.Structural (E.managedSource (D.erase pre)) :=
    X.managed_source_structural admitted.1
  obtain ⟨planOccurrence, planPresent, planEq⟩ := MP.managed_accepted_fields structural accepted
  obtain ⟨policy, selected, member, scalar, fields⟩ :=
    E.managed_accepted_completion (completePreRoot := completeRoot roots.digest pre)
      (completePostRoot :=
        completeRoot roots.digest (D.step roots.digest pre (.managed ctx command)))
      roots.managed admitted.1.rows structural input.1 input.2 accepted
  have conservationFields :
      (E.managedEffectPlan roots.digest ctx (D.erase pre) command (completeRoot roots.digest pre)
          (completeRoot roots.digest
            (D.step roots.digest pre (.managed ctx command)))).assetConservation =
        [E.managedCompletedConservation (D.erase pre)
          (E.managedPostFromLeaf (D.erase pre)
            (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post)
          command] := fields.2.1
  have conservationAdmitted :
      AssetConservationAdmitted (E.managedCompletedConservation (D.erase pre)
        (E.managedPostFromLeaf (D.erase pre)
          (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post)
        command) := fields.2.2.1
  have planAdmitted :
      EffectPlanAdmitted (E.managedEffectPlan roots.digest ctx (D.erase pre) command
        (completeRoot roots.digest pre)
        (completeRoot roots.digest (D.step roots.digest pre (.managed ctx command)))) :=
    fields.2.2.2.1
  have effectsEq : source.effects =
      MP.managedPlan roots.digest ctx (E.managedSource (D.erase pre)) command := relation.refines
  have occurrences : source.effects.occurrenceConsumptions = [planOccurrence.occurrenceId] := by
    rw [effectsEq, planEq]
  have lanes : source.effects.laneWrites =
      [⟨LaneId.assetTransfer, FM.stateRoot roots.digest (E.managedSource (D.erase pre)),
        FM.stateRoot roots.digest
          (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post⟩] := by
    rw [effectsEq, planEq]
  have outbox : source.effects.externalOutboxEnqueue = [] := by
    rw [effectsEq, planEq]
  have conservation : source.effects.assetConservation =
      [MP.managedConservation (E.managedSource (D.erase pre))
        (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post command] := by
    rw [effectsEq, planEq]
  have present : occurrenceId ((show F.Action from .managed ctx command)) = some planOccurrence.occurrenceId := by
    simp only [occurrenceId, planPresent]
  have selectedAsset : command.asset ∈ R.managedAssets (D.erase pre) :=
    List.mem_map.mpr ⟨policy, member, (FM.policyFor_spec selected).2⟩
  have accountsPreEq :
      amountForAsset (E.managedSource (D.erase pre)).balances command.asset =
        amountForAsset pre.transfer.balances command.asset :=
    H.selectRows_total _ _ command.asset selectedAsset
  have supplyPreEq :
      supplyFor (numericRows (E.managedSource (D.erase pre)).supplies) command.asset =
        C.supplyAt (D.erase pre) command.asset := E.managed_source_supply selectedAsset
  have policyAssets : command.asset ∈
      leafPolicyAssets roots.digest pre ((show F.Action from .managed ctx command)) := by
    show command.asset ∈
      (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post.policies.map
        (fun leafPolicy => leafPolicy.asset)
    rw [(FM.accepted_post_effects accepted).1]
    exact List.mem_map.mpr ⟨policy, member, (FM.policyFor_spec selected).2⟩
  have sourceOk : SourceBindings roots commits pre
      ⟨chainId, deploymentRoot, profileRoot, writerEpoch, .managed ctx command⟩
      planOccurrence.occurrenceId source := by
    refine ⟨relation.laneId, relation.chainId, relation.deploymentRoot,
      relation.profileRoot, relation.writerEpoch, relation.release, relation.moduleReleaseId,
      relation.commandOccurrenceId _ present, relation.preLaneRoot, occurrences, ?_,
      relation.postLaneRoot, relation.effectPlanRoot, outbox, relation.privatePortRoot,
      relation.terminalObligationsRoot, relation.oracleOccurrencePlanRoot⟩
    exact lanes
  have projection : Projection roots pre
      ⟨chainId, deploymentRoot, profileRoot, writerEpoch, .managed ctx command⟩ source := by
    unfold Projection AccountProjection
    refine ⟨MP.managedConservation (E.managedSource (D.erase pre))
        (FM.transition roots.digest ctx (E.managedSource (D.erase pre)) command).post command,
      ?_, conservation, rfl, policyAssets, accountsPreEq, rfl, supplyPreEq, rfl⟩
    rw [conservation]
    exact List.mem_singleton.mpr rfl
  have reprojection : Reprojection roots.digest pre ((show F.Action from .managed ctx command)) :=
    ⟨A.managed_accepted_full_projection admitted.1 input accepted,
      (D.step_transfer_metadata roots.digest pre (.managed ctx command)).2⟩
  have verdictNone : leafVerdict roots.digest pre ((show F.Action from .managed ctx command)) = none := by
    simp only [leafVerdict, accepted]
  have outcome := accepted_outcome_is_internally_derived (source := source) bindings verdictNone
    present sourceOk projection fits reprojection
  have postAdmitted := A.step_preserves_constructor_admission roots.digest admitted input fits
  have postBindings := A.policy_origin_bindings_preserved roots.digest pre
    (.managed ctx command) bindings
  have completedEq := managed_completed_effects accepted effectsEq
  have completedAdmitted : EffectPlanAdmitted
      (completedEffects roots.digest pre (.managed ctx command) source) := by
    rw [completedEq]
    exact planAdmitted
  have completedConservation :
      (completedEffects roots.digest pre (.managed ctx command) source).assetConservation =
        [E.managedCompletedConservation (D.erase pre)
          (D.erase (D.step roots.digest pre (.managed ctx command))) command] := by
    rw [completedEq, conservationFields, managed_erase_post accepted]
  have completedRowAdmitted : AssetConservationAdmitted
      (E.managedCompletedConservation (D.erase pre)
        (D.erase (D.step roots.digest pre (.managed ctx command))) command) := by
    rw [managed_erase_post accepted]
    exact conservationAdmitted
  refine ⟨policy, planOccurrence.occurrenceId, selected, member, scalar, present, sourceOk,
    projection, reprojection, outcome.1, rfl, postAdmitted, postBindings, completedAdmitted,
    completedConservation, completedRowAdmitted, rfl, ?_⟩
  exact completed_accepted_bindings sourceOk postBindings

end Proofs.AssetLaneCustodyCoordinatorOutcomeV2
