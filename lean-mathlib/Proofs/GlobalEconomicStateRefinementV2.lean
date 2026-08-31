import Proofs.GlobalSettlementCoreV2

/-!
# GlobalSettlementABI V2 global state/effect refinement

This file defines a bounded mathematical relation for the live Python modules
`global_economic_state_v2.py`, `global_economic_refinement_checks_v2.py`, and
`global_economic_state_effect_refinement_v2.py`.  The `Verified` record is the
single construction boundary: producing it requires all state/effect,
conservation, lifecycle, replay, and pre-O-009 outbox obligations at once.
`Accepted` carries that record, while `Outcome.rejected` returns the input state
and empty plans by construction.

## Modeled runtime fields

`GlobalState` names `state_root`, `chain_id`, `deployment_root`, `writer_epoch`,
`height`, `profile_root`, `lane_roots`, `balances`, `supplies`, `custody`,
`liabilities`, `reserves`, `oracle_occurrences`, `replay_state`,
`terminal_obligations`, `history_root`, and `outbox`.  The relation covers exact,
order-independent changed-lane/write membership and roots on pre-enabled lanes;
the four state-bearing effect tables; separate issue and burn supply projections;
per-asset fee-allocation projection; per-asset owned-equals-supply; claimant
liability rows backed by accounting-location totals; terminal identity, status,
owning-lane, registry, liability effects, and running signed bounds; Oracle
identity, lookup-key identity, height, finality, same-height root, registry, and
lane writes; ordered unique replay with injective stored occurrence IDs, context
binding, one-step height; zero-occurrence static behavior; and an empty external
enqueue list before O-009.  State amount/supply tables are sparse and nonzero.
The model also bounds running state-bearing annotation totals, requires same-key
state-bearing fee credit, rejects zero fee rows, binds positive carried residue
to `protocol:fee-unallocated-reserve` at
`zenoledger:protocol-fee-residue`, bounds each Oracle observation by global
height, makes every open terminal amount positive, and covers open terminal
totals by their exact claimant/asset/accounting-location liability row.

## Omitted runtime fields and behaviours

Rows are finite lists, while registries and lane metadata use mathematical
functions.  This file omits canonical JSON and root computation, canonical
tuple ordering, collection and byte resource ceilings, private snapshot
ownership, exception classes and precedence, journal/receipt fields,
command-body decoding, lane command semantics, adapter execution, publisher
commit protocol, RISC0 verification, Tau admission, and host/runtime mounting.
The companion Python gate pins the exact modeled runtime source hashes; hashes
are not internalized in this Lean model.  Roots and IDs remain opaque values.
Equality of modeled states makes no claim about SHA-256 injectivity or collision
resistance.

## Claim boundary

The packet grants no verifier authority, publisher authority, settlement
authority, value-moving authority, release status, or production readiness.
It proves no Python/Rust refinement and no runtime reachability.  O-009 remains
required before any external outbox enqueue can be accepted.
-/

namespace Proofs
namespace GlobalEconomicStateRefinementV2

open GlobalSettlementCoreV2

/-! ## Global economic tables -/

structure AmountRow where
  owner : Principal
  asset : Asset
  custodyDomain : AccountingLocation
  amountAtoms : Int
  deriving DecidableEq, Repr

structure SupplyRow where
  asset : Asset
  amountAtoms : Int
  deriving DecidableEq, Repr

def amountAt (rows : List AmountRow) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) : Int :=
  (rows.map fun row =>
    if row.owner = owner ∧ row.asset = asset ∧ row.custodyDomain = domain then
      row.amountAtoms
    else
      0).sum

def amountForAsset (rows : List AmountRow) (asset : Asset) : Int :=
  (rows.map fun row => if row.asset = asset then row.amountAtoms else 0).sum

def amountForAssetDomain (rows : List AmountRow) (asset : Asset)
    (domain : AccountingLocation) : Int :=
  (rows.map fun row =>
    if row.asset = asset ∧ row.custodyDomain = domain then row.amountAtoms else 0).sum

def supplyFor (rows : List SupplyRow) (asset : Asset) : Int :=
  (rows.map fun row => if row.asset = asset then row.amountAtoms else 0).sum

def effectFor (kind : EffectKind) (plan : EffectPlan) (owner : Principal)
    (asset : Asset) (domain : AccountingLocation) : Int :=
  (plan.rows.map fun row =>
    if row.kind = kind ∧ row.principal = owner ∧ row.asset = asset ∧
        row.custodyDomain = domain then
      row.deltaAtoms
    else
      0).sum

def issueDeltaFor (plan : EffectPlan) (asset : Asset) : Int :=
  issuedFor asset plan.rows

def burnDeltaFor (plan : EffectPlan) (asset : Asset) : Int :=
  burnedFor asset plan.rows

/-- Every running aggregate is checked, matching the fail-closed Python/Rust
accumulators rather than checking only a possibly cancellation-masked final sum. -/
def RunningTotalsFitI128 {α : Type} (contribution : α → Int) :
    List α → Int → Prop
  | [], _ => True
  | row :: rows, total =>
      FitsI128 (total + contribution row) ∧
        RunningTotalsFitI128 contribution rows (total + contribution row)

/-! ## Terminal and Oracle registries -/

inductive TerminalStatus where
  | open
  | drained
  | tombstoned
  deriving DecidableEq, Repr

structure TerminalObligation where
  obligationId : Identifier
  laneId : LaneId
  claimant : Principal
  asset : Asset
  liabilityDomain : AccountingLocation
  amountAtoms : Int
  status : TerminalStatus
  deriving DecidableEq, Repr

def TerminalObligationAdmitted (obligation : TerminalObligation) : Prop :=
  FitsU128 obligation.amountAtoms ∧
  (obligation.status = .open → 0 < obligation.amountAtoms)

structure TerminalDelta where
  obligationId : Identifier
  preObligation : Option TerminalObligation
  postObligation : TerminalObligation
  deriving DecidableEq, Repr

structure TerminalPlan where
  deltas : List TerminalDelta
  deriving DecidableEq, Repr

inductive OracleFinality where
  | pending
  | finalized
  deriving DecidableEq, Repr

structure OracleOccurrence where
  oracleId : Identifier
  occurrenceRoot : RootId
  observedHeight : Nat
  finality : OracleFinality
  deriving DecidableEq, Repr

def OracleOccurrenceWithinHeight (globalHeight : Nat)
    (occurrence : OracleOccurrence) : Prop :=
  FitsU64 occurrence.observedHeight ∧ occurrence.observedHeight ≤ globalHeight

structure OracleDelta where
  oracleId : Identifier
  preOccurrence : Option OracleOccurrence
  postOccurrence : OracleOccurrence
  deriving DecidableEq, Repr

structure OraclePlan where
  deltas : List OracleDelta
  deriving DecidableEq, Repr

structure ReplayRecord where
  replayId : Identifier
  occurrenceId : RootId
  deriving DecidableEq, Repr

structure CommandOccurrence where
  occurrenceId : RootId
  replayId : Identifier
  chainId : Identifier
  deploymentRoot : RootId
  profileRoot : RootId
  preStateRoot : RootId
  height : Nat
  deriving DecidableEq, Repr

abbrev TerminalRegistry := List TerminalObligation
abbrev OracleRegistry := Identifier → Option OracleOccurrence
abbrev ReplayRegistry := Identifier → Option RootId

def terminalLookup (registry : TerminalRegistry) (obligationId : Identifier) :
    Option TerminalObligation :=
  registry.find? fun obligation => obligation.obligationId == obligationId

def openTerminalAmountFor (registry : TerminalRegistry) (owner : Principal)
    (asset : Asset) (domain : AccountingLocation) : Int :=
  (registry.map fun obligation =>
    if obligation.claimant = owner ∧ obligation.asset = asset ∧
        obligation.liabilityDomain = domain ∧ obligation.status = .open then
      obligation.amountAtoms
    else
      0).sum

/-! ## Full modeled state -/

structure GlobalState where
  stateRoot : RootId
  chainId : Identifier
  deploymentRoot : RootId
  writerEpoch : Nat
  height : Nat
  profileRoot : RootId
  laneRoots : LaneId → RootId
  laneReleaseIds : LaneId → RootId
  laneEnabled : LaneId → Bool
  balances : List AmountRow
  supplies : List SupplyRow
  custody : List AmountRow
  liabilities : List AmountRow
  reserves : List AmountRow
  oracleOccurrences : OracleRegistry
  replayState : ReplayRegistry
  terminalObligations : TerminalRegistry
  historyRoot : RootId
  outbox : List RootId

def ownedFor (state : GlobalState) (asset : Asset) : Int :=
  amountForAsset state.balances asset + amountForAsset state.custody asset +
    amountForAsset state.reserves asset

def liabilityFor (state : GlobalState) (asset : Asset) : Int :=
  amountForAsset state.liabilities asset

def OpenTerminalLiabilitiesCovered (state : GlobalState) : Prop :=
  ∀ owner asset domain,
    0 ≤ openTerminalAmountFor state.terminalObligations owner asset domain ∧
    openTerminalAmountFor state.terminalObligations owner asset domain ≤
      amountAt state.liabilities owner asset domain

def OracleRegistryWithinGlobalHeight (state : GlobalState) : Prop :=
  ∀ oracleId occurrence,
    state.oracleOccurrences oracleId = some occurrence →
      OracleOccurrenceWithinHeight state.height occurrence

def OracleRegistryKeysMatch (state : GlobalState) : Prop :=
  ∀ oracleId occurrence,
    state.oracleOccurrences oracleId = some occurrence → occurrence.oracleId = oracleId

def OracleRegistryAdmitted (state : GlobalState) : Prop :=
  OracleRegistryWithinGlobalHeight state ∧ OracleRegistryKeysMatch state

def ReplayOccurrenceIdsInjective (state : GlobalState) : Prop :=
  ∀ leftReplayId rightReplayId occurrenceId,
    state.replayState leftReplayId = some occurrenceId →
    state.replayState rightReplayId = some occurrenceId →
    leftReplayId = rightReplayId

def OwnedMatchesSupply (state : GlobalState) : Prop :=
  ∀ asset, ownedFor state asset = supplyFor state.supplies asset

/-- Claimant-addressed liability rows are aggregated by asset and accounting
domain and must fit inside custody in that same domain. -/
def ClaimantLiabilitiesBacked (state : GlobalState) : Prop :=
  (∀ asset domain,
    0 ≤ amountForAssetDomain state.liabilities asset domain ∧
    amountForAssetDomain state.liabilities asset domain ≤
      amountForAssetDomain state.custody asset domain) ∧
  OpenTerminalLiabilitiesCovered state

def SparseAmountRowsAdmitted (rows : List AmountRow) : Prop :=
  ∀ row ∈ rows, FitsU128 row.amountAtoms ∧ row.amountAtoms ≠ 0

def SparseSupplyRowsAdmitted (rows : List SupplyRow) : Prop :=
  ∀ row ∈ rows, FitsU128 row.amountAtoms ∧ row.amountAtoms ≠ 0

def StateQuantitiesAdmitted (state : GlobalState) : Prop :=
  FitsU64 state.writerEpoch ∧
  FitsU64 state.height ∧
  SparseAmountRowsAdmitted state.balances ∧
  SparseSupplyRowsAdmitted state.supplies ∧
  SparseAmountRowsAdmitted state.custody ∧
  SparseAmountRowsAdmitted state.liabilities ∧
  SparseAmountRowsAdmitted state.reserves ∧
  (state.balances.map fun row => (row.asset, row.owner, row.custodyDomain)).Nodup ∧
  (state.custody.map fun row => (row.asset, row.owner, row.custodyDomain)).Nodup ∧
  (state.liabilities.map fun row => (row.asset, row.owner, row.custodyDomain)).Nodup ∧
  (state.reserves.map fun row => (row.asset, row.owner, row.custodyDomain)).Nodup ∧
  (state.supplies.map fun row => row.asset).Nodup ∧
  (∀ asset,
    FitsU128 (ownedFor state asset) ∧
    FitsU128 (liabilityFor state asset) ∧
    FitsU128 (supplyFor state.supplies asset)) ∧
  (state.terminalObligations.map fun obligation => obligation.obligationId).Nodup ∧
  (∀ obligation ∈ state.terminalObligations,
    TerminalObligationAdmitted obligation) ∧
  ReplayOccurrenceIdsInjective state ∧
  OracleRegistryAdmitted state

/-! ## Exact lane and table refinement -/

def LaneWrittenBy (plan : EffectPlan) (lane : LaneId) : Prop :=
  ∃ write ∈ plan.laneWrites, write.laneId = lane

def ExactLaneWrites (pre post : GlobalState) (plan : EffectPlan) : Prop :=
  (∀ lane, LaneWrittenBy plan lane ↔ pre.laneRoots lane ≠ post.laneRoots lane) ∧
  (∀ lane, pre.laneRoots lane ≠ post.laneRoots lane → pre.laneEnabled lane = true) ∧
  ∀ write ∈ plan.laneWrites,
    pre.laneEnabled write.laneId = true ∧
      write.preRoot = pre.laneRoots write.laneId ∧
      write.postRoot = post.laneRoots write.laneId

def FixedContext (pre post : GlobalState) : Prop :=
  pre.chainId = post.chainId ∧
  pre.deploymentRoot = post.deploymentRoot ∧
  pre.writerEpoch = post.writerEpoch ∧
  pre.profileRoot = post.profileRoot ∧
  pre.historyRoot = post.historyRoot ∧
  pre.outbox = post.outbox ∧
  pre.laneReleaseIds = post.laneReleaseIds ∧
  pre.laneEnabled = post.laneEnabled

def ExactTableEffect (kind : EffectKind) (preRows postRows : List AmountRow)
    (plan : EffectPlan) : Prop :=
  ∀ owner asset domain,
    amountAt postRows owner asset domain - amountAt preRows owner asset domain =
      effectFor kind plan owner asset domain

def ExactEconomicTables (pre post : GlobalState) (plan : EffectPlan) : Prop :=
  ExactTableEffect .accountMovement pre.balances post.balances plan ∧
  ExactTableEffect .custody pre.custody post.custody plan ∧
  ExactTableEffect .liability pre.liabilities post.liabilities plan ∧
  ExactTableEffect .reserve pre.reserves post.reserves plan

def ExactSupplyEffects (pre post : GlobalState) (plan : EffectPlan) : Prop :=
  ∀ asset,
    supplyFor post.supplies asset - supplyFor pre.supplies asset =
      issueDeltaFor plan asset - burnDeltaFor plan asset

def EconomicAssetTouched (pre post : GlobalState) (plan : EffectPlan)
    (asset : Asset) : Prop :=
  (∃ row ∈ plan.rows, row.asset = asset) ∨
  (∃ row ∈ plan.feeConservation, row.asset = asset) ∨
  (∃ owner domain,
    amountAt pre.balances owner asset domain ≠ amountAt post.balances owner asset domain) ∨
  (∃ owner domain,
    amountAt pre.custody owner asset domain ≠ amountAt post.custody owner asset domain) ∨
  (∃ owner domain,
    amountAt pre.liabilities owner asset domain ≠
      amountAt post.liabilities owner asset domain) ∨
  (∃ owner domain,
    amountAt pre.reserves owner asset domain ≠ amountAt post.reserves owner asset domain) ∨
  supplyFor pre.supplies asset ≠ supplyFor post.supplies asset

def ExactConservationCoverage (pre post : GlobalState) (plan : EffectPlan) : Prop :=
  ∀ asset,
    (∃ row ∈ plan.assetConservation, row.asset = asset) ↔
      EconomicAssetTouched pre post plan asset

def ConservationRowsMatchState (pre post : GlobalState) (plan : EffectPlan) : Prop :=
  ∀ row ∈ plan.assetConservation,
    row.ownedAndCustodiedPreAtoms = ownedFor pre row.asset ∧
    row.ownedAndCustodiedPostAtoms = ownedFor post row.asset ∧
    row.supplyPreAtoms = supplyFor pre.supplies row.asset ∧
    row.supplyPostAtoms = supplyFor post.supplies row.asset

def stateBearingEffectFor (plan : EffectPlan) (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) : Int :=
  effectFor .accountMovement plan owner asset domain +
    effectFor .custody plan owner asset domain +
    effectFor .reserve plan owner asset domain

def stateBearingContribution (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (row : EconomicEffectRow) : Int :=
  if row.principal = owner ∧ row.asset = asset ∧ row.custodyDomain = domain ∧
      (row.kind = .accountMovement ∨ row.kind = .custody ∨ row.kind = .reserve) then
    row.deltaAtoms
  else
    0

def StateBearingAggregatesFitI128 (plan : EffectPlan) : Prop :=
  ∀ owner asset domain,
    RunningTotalsFitI128
      (stateBearingContribution owner asset domain) plan.rows 0

def feeResiduePrincipal : Principal := "protocol:fee-unallocated-reserve"

def feeResidueAccountingLocation : AccountingLocation :=
  "zenoledger:protocol-fee-residue"

def positiveDesignatedResidueFor (plan : EffectPlan) (asset : Asset) : Int :=
  (plan.rows.map fun row =>
    if row.kind = .reserve ∧ row.principal = feeResiduePrincipal ∧
        row.asset = asset ∧ row.custodyDomain = feeResidueAccountingLocation ∧
        0 < row.deltaAtoms then
      row.deltaAtoms
    else
      0).sum

def positiveCarriedResidueFor (plan : EffectPlan) (asset : Asset) : Int :=
  (plan.feeConservation.map fun row =>
    if row.asset = asset ∧ 0 < row.carriedResidueAtoms then
      row.carriedResidueAtoms
    else
      0).sum

def FeeRowsCanonical (plan : EffectPlan) : Prop :=
  ∀ row ∈ plan.feeConservation, 0 < row.feeChargedAtoms

def FeeResidueExact (plan : EffectPlan) : Prop :=
  ∀ asset,
    positiveDesignatedResidueFor plan asset = positiveCarriedResidueFor plan asset

def FeeAllocationCreditsMirrored (plan : EffectPlan) : Prop :=
  ∀ row ∈ plan.rows,
    row.kind = .feeAllocation →
      0 < row.deltaAtoms ∧
      row.deltaAtoms ≤
        stateBearingEffectFor plan row.principal row.asset row.custodyDomain

def RewardSlashMirrored (plan : EffectPlan) : Prop :=
  ∀ row ∈ plan.rows,
    row.kind = .reward ∨ row.kind = .slash →
      stateBearingEffectFor plan row.principal row.asset row.custodyDomain =
        row.deltaAtoms

def AnnotationMirrors (plan : EffectPlan) : Prop :=
  StateBearingAggregatesFitI128 plan ∧
  FeeAllocationCreditsMirrored plan ∧
  RewardSlashMirrored plan ∧
  FeeRowsCanonical plan ∧
  FeeResidueExact plan

/-! ## Terminal refinement -/

def TerminalIdentityPreserved (before after : TerminalObligation) : Prop :=
  before.obligationId = after.obligationId ∧
  before.laneId = after.laneId ∧
  before.claimant = after.claimant ∧
  before.asset = after.asset ∧
  before.liabilityDomain = after.liabilityDomain

def TerminalDeltaAdmitted (delta : TerminalDelta) : Prop :=
  delta.postObligation.obligationId = delta.obligationId ∧
  TerminalObligationAdmitted delta.postObligation ∧
  match delta.preObligation with
  | none => delta.postObligation.status = .open
  | some before =>
      TerminalObligationAdmitted before ∧
      before.obligationId = delta.obligationId ∧
      TerminalIdentityPreserved before delta.postObligation ∧
      before.status = .open ∧
      ((delta.postObligation.status = .open ∧
          delta.postObligation.amountAtoms ≠ before.amountAtoms) ∨
        ((delta.postObligation.status = .drained ∨
            delta.postObligation.status = .tombstoned) ∧
          delta.postObligation.amountAtoms = before.amountAtoms))

def TerminalRegistryRefines (pre post : TerminalRegistry) (plan : TerminalPlan) : Prop :=
  (plan.deltas.map (fun delta => delta.obligationId)).Nodup ∧
  (∀ delta ∈ plan.deltas,
    terminalLookup pre delta.obligationId = delta.preObligation ∧
    terminalLookup post delta.obligationId = some delta.postObligation ∧
    TerminalDeltaAdmitted delta) ∧
  (∀ obligationId,
    (∀ delta ∈ plan.deltas, delta.obligationId ≠ obligationId) →
      terminalLookup post obligationId = terminalLookup pre obligationId)

def terminalOpenContribution (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (obligation : TerminalObligation) : Int :=
  if obligation.claimant = owner ∧ obligation.asset = asset ∧
      obligation.liabilityDomain = domain ∧ obligation.status = .open then
    obligation.amountAtoms
  else
    0

def optionalTerminalOpenContribution (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) : Option TerminalObligation → Int
  | none => 0
  | some obligation => terminalOpenContribution owner asset domain obligation

def terminalLiabilityContribution (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (delta : TerminalDelta) : Int :=
  terminalOpenContribution owner asset domain delta.postObligation -
    optionalTerminalOpenContribution owner asset domain delta.preObligation

def terminalLiabilityDeltaFor (owner : Principal) (asset : Asset)
    (domain : AccountingLocation) (plan : TerminalPlan) : Int :=
  (plan.deltas.map (terminalLiabilityContribution owner asset domain)).sum

def TerminalLiabilityAggregatesFitI128 (terminalPlan : TerminalPlan) : Prop :=
  ∀ owner asset domain,
    RunningTotalsFitI128
      (terminalLiabilityContribution owner asset domain) terminalPlan.deltas 0

def TerminalLiabilityEffects (effects : EffectPlan) (terminalPlan : TerminalPlan) : Prop :=
  TerminalLiabilityAggregatesFitI128 terminalPlan ∧
    ∀ owner asset domain,
      terminalLiabilityDeltaFor owner asset domain terminalPlan =
        effectFor .liability effects owner asset domain

def TerminalOwningLaneWrites (effects : EffectPlan) (terminalPlan : TerminalPlan) : Prop :=
  ∀ delta ∈ terminalPlan.deltas,
    ∃ write ∈ effects.laneWrites, write.laneId = delta.postObligation.laneId

def ExactTerminalRefinement (pre post : GlobalState) (effects : EffectPlan)
    (terminalPlan : TerminalPlan) : Prop :=
  TerminalRegistryRefines pre.terminalObligations post.terminalObligations terminalPlan ∧
  TerminalOwningLaneWrites effects terminalPlan ∧
  TerminalLiabilityEffects effects terminalPlan

/-! ## Oracle refinement -/

def OracleDeltaAdmitted (delta : OracleDelta) : Prop :=
  delta.postOccurrence.oracleId = delta.oracleId ∧
  FitsU64 delta.postOccurrence.observedHeight ∧
  match delta.preOccurrence with
  | none => True
  | some before =>
      before.oracleId = delta.oracleId ∧
      before.oracleId = delta.postOccurrence.oracleId ∧
      before.observedHeight ≤ delta.postOccurrence.observedHeight ∧
      (before.finality = .finalized → delta.postOccurrence.finality = .finalized) ∧
      (before.observedHeight = delta.postOccurrence.observedHeight →
        before.occurrenceRoot = delta.postOccurrence.occurrenceRoot) ∧
      before ≠ delta.postOccurrence

def OracleRegistryRefines (pre post : OracleRegistry) (plan : OraclePlan) : Prop :=
  (plan.deltas.map (fun delta => delta.oracleId)).Nodup ∧
  (∀ delta ∈ plan.deltas,
    pre delta.oracleId = delta.preOccurrence ∧
    post delta.oracleId = some delta.postOccurrence ∧
    OracleDeltaAdmitted delta) ∧
  (∀ oracleId,
    (∀ delta ∈ plan.deltas, delta.oracleId ≠ oracleId) →
      post oracleId = pre oracleId)

def OracleLaneWrite (effects : EffectPlan) (oraclePlan : OraclePlan) : Prop :=
  oraclePlan.deltas = [] ∨
    ∃ write ∈ effects.laneWrites, write.laneId = .oracleMarket

def ExactOracleRefinement (pre post : GlobalState) (effects : EffectPlan)
    (oraclePlan : OraclePlan) : Prop :=
  OracleRegistryRefines pre.oracleOccurrences post.oracleOccurrences oraclePlan ∧
  OracleLaneWrite effects oraclePlan

/-! ## Replay and height refinement -/

def OccurrenceContextMatches (pre : GlobalState) (occurrence : CommandOccurrence) : Prop :=
  occurrence.chainId = pre.chainId ∧
  occurrence.deploymentRoot = pre.deploymentRoot ∧
  occurrence.profileRoot = pre.profileRoot ∧
  occurrence.preStateRoot = pre.stateRoot

def OrderedOccurrenceIds (occurrences : List CommandOccurrence) : Prop :=
  (occurrences.map (fun occurrence => occurrence.occurrenceId)).Pairwise (· < ·)

def ReplayRegistryRefines (pre post : ReplayRegistry)
    (occurrences : List CommandOccurrence) : Prop :=
  (occurrences.map (fun occurrence => occurrence.replayId)).Nodup ∧
  (∀ occurrence ∈ occurrences,
    pre occurrence.replayId = none ∧
    post occurrence.replayId = some occurrence.occurrenceId ∧
    (∀ replayId priorOccurrenceId,
      pre replayId = some priorOccurrenceId →
        priorOccurrenceId ≠ occurrence.occurrenceId)) ∧
  (∀ replayId,
    (∀ occurrence ∈ occurrences, occurrence.replayId ≠ replayId) →
      post replayId = pre replayId)

def ExactReplayRefinement (pre post : GlobalState) (effects : EffectPlan)
    (occurrences : List CommandOccurrence) : Prop :=
  OrderedOccurrenceIds occurrences ∧
  effects.occurrenceConsumptions =
    occurrences.map (fun occurrence => occurrence.occurrenceId) ∧
  (∀ occurrence ∈ occurrences, OccurrenceContextMatches pre occurrence) ∧
  ReplayRegistryRefines pre.replayState post.replayState occurrences ∧
  post.height = (if occurrences.isEmpty then pre.height else pre.height + 1) ∧
  FitsU64 post.height ∧
  (∀ occurrence ∈ occurrences, occurrence.height = post.height)

def ZeroOccurrenceStatic (pre post : GlobalState) (effects : EffectPlan)
    (terminalPlan : TerminalPlan) (oraclePlan : OraclePlan)
    (occurrences : List CommandOccurrence) : Prop :=
  occurrences = [] →
    effects.IsEmpty ∧ terminalPlan.deltas = [] ∧ oraclePlan.deltas = [] ∧ pre = post

def PreO009OutboxClosed (effects : EffectPlan) : Prop :=
  effects.externalOutboxEnqueue = []

/-! ## Combined witness and outcomes -/

structure Verified (pre : GlobalState) (effects : EffectPlan)
    (terminalPlan : TerminalPlan) (oraclePlan : OraclePlan)
    (occurrences : List CommandOccurrence) (post : GlobalState) : Prop where
  fixedContext : FixedContext pre post
  preQuantities : StateQuantitiesAdmitted pre
  postQuantities : StateQuantitiesAdmitted post
  effectPlan : EffectPlanAdmitted effects
  laneWrites : ExactLaneWrites pre post effects
  economicTables : ExactEconomicTables pre post effects
  supplyEffects : ExactSupplyEffects pre post effects
  conservationCoverage : ExactConservationCoverage pre post effects
  conservationRows : ConservationRowsMatchState pre post effects
  annotations : AnnotationMirrors effects
  ownedSupplyPre : OwnedMatchesSupply pre
  ownedSupplyPost : OwnedMatchesSupply post
  liabilitiesPre : ClaimantLiabilitiesBacked pre
  liabilitiesPost : ClaimantLiabilitiesBacked post
  terminal : ExactTerminalRefinement pre post effects terminalPlan
  oracle : ExactOracleRefinement pre post effects oraclePlan
  replay : ExactReplayRefinement pre post effects occurrences
  outboxClosed : PreO009OutboxClosed effects
  zeroOccurrence : ZeroOccurrenceStatic pre post effects terminalPlan oraclePlan occurrences

structure Accepted (pre : GlobalState) where
  effects : EffectPlan
  terminalPlan : TerminalPlan
  oraclePlan : OraclePlan
  occurrences : List CommandOccurrence
  post : GlobalState
  verified : Verified pre effects terminalPlan oraclePlan occurrences post

inductive RejectCode where
  | malformed
  | contextMismatch
  | conservationMismatch
  | lifecycleMismatch
  | replayMismatch
  | outboxPublisherMissing
  deriving DecidableEq, Repr

inductive Outcome (pre : GlobalState) where
  | accepted (value : Accepted pre)
  | rejected (code : RejectCode)

def Outcome.postState {pre : GlobalState} : Outcome pre → GlobalState
  | .accepted value => value.post
  | .rejected _ => pre

def Outcome.effectPlan {pre : GlobalState} : Outcome pre → EffectPlan
  | .accepted value => value.effects
  | .rejected _ => EffectPlan.empty

def Outcome.terminalPlan {pre : GlobalState} : Outcome pre → TerminalPlan
  | .accepted value => value.terminalPlan
  | .rejected _ => ⟨[]⟩

def Outcome.oraclePlan {pre : GlobalState} : Outcome pre → OraclePlan
  | .accepted value => value.oraclePlan
  | .rejected _ => ⟨[]⟩

def Outcome.occurrences {pre : GlobalState} : Outcome pre → List CommandOccurrence
  | .accepted value => value.occurrences
  | .rejected _ => []

theorem accepted_extracts_combined_witness {pre : GlobalState}
    (accepted : Accepted pre) :
    Verified pre accepted.effects accepted.terminalPlan accepted.oraclePlan
      accepted.occurrences accepted.post :=
  accepted.verified

theorem accepted_preserves_owned_supply {pre : GlobalState}
    (accepted : Accepted pre) : OwnedMatchesSupply accepted.post :=
  accepted.verified.ownedSupplyPost

theorem accepted_preserves_liability_backing {pre : GlobalState}
    (accepted : Accepted pre) : ClaimantLiabilitiesBacked accepted.post :=
  accepted.verified.liabilitiesPost

theorem accepted_liabilities_use_same_domain_backing {pre : GlobalState}
    (accepted : Accepted pre) :
    ∀ asset domain,
      0 ≤ amountForAssetDomain accepted.post.liabilities asset domain ∧
      amountForAssetDomain accepted.post.liabilities asset domain ≤
        amountForAssetDomain accepted.post.custody asset domain :=
  accepted.verified.liabilitiesPost.1

theorem accepted_open_terminal_totals_fit_exact_liability_rows {pre : GlobalState}
    (accepted : Accepted pre) : OpenTerminalLiabilitiesCovered accepted.post :=
  accepted.verified.liabilitiesPost.2

theorem accepted_fee_credit_and_residue_are_exact {pre : GlobalState}
    (accepted : Accepted pre) :
    FeeAllocationCreditsMirrored accepted.effects ∧
      FeeProjectionMatches accepted.effects ∧
      FeeRowsCanonical accepted.effects ∧ FeeResidueExact accepted.effects :=
  ⟨accepted.verified.annotations.2.1,
    accepted.verified.effectPlan.2.2.2.2.1,
    accepted.verified.annotations.2.2.2.1,
    accepted.verified.annotations.2.2.2.2⟩

theorem accepted_oracles_do_not_exceed_global_height {pre : GlobalState}
    (accepted : Accepted pre) : OracleRegistryWithinGlobalHeight accepted.post := by
  rcases accepted.verified.postQuantities with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, oracleAdmitted⟩
  exact oracleAdmitted.1

theorem accepted_has_independent_issue_burn_projections {pre : GlobalState}
    (accepted : Accepted pre) : ProjectionMatches accepted.effects :=
  accepted.verified.effectPlan.2.2.2.1

theorem accepted_has_exact_table_and_supply_effects {pre : GlobalState}
    (accepted : Accepted pre) :
    ExactEconomicTables pre accepted.post accepted.effects ∧
      ExactSupplyEffects pre accepted.post accepted.effects :=
  ⟨accepted.verified.economicTables, accepted.verified.supplyEffects⟩

theorem accepted_has_exact_lane_write_coverage {pre : GlobalState}
    (accepted : Accepted pre) : ExactLaneWrites pre accepted.post accepted.effects :=
  accepted.verified.laneWrites

theorem accepted_has_exact_terminal_refinement {pre : GlobalState}
    (accepted : Accepted pre) :
    ExactTerminalRefinement pre accepted.post accepted.effects accepted.terminalPlan :=
  accepted.verified.terminal

theorem accepted_has_exact_oracle_refinement {pre : GlobalState}
    (accepted : Accepted pre) :
    ExactOracleRefinement pre accepted.post accepted.effects accepted.oraclePlan :=
  accepted.verified.oracle

theorem accepted_has_exact_replay_refinement {pre : GlobalState}
    (accepted : Accepted pre) :
    ExactReplayRefinement pre accepted.post accepted.effects accepted.occurrences :=
  accepted.verified.replay

theorem accepted_replay_is_ordered_and_one_step {pre : GlobalState}
    (accepted : Accepted pre) :
    OrderedOccurrenceIds accepted.occurrences ∧
      accepted.post.height =
        (if accepted.occurrences.isEmpty then pre.height else pre.height + 1) :=
  ⟨accepted.verified.replay.1, accepted.verified.replay.2.2.2.2.1⟩

theorem accepted_outbox_is_closed_before_o009 {pre : GlobalState}
    (accepted : Accepted pre) : accepted.effects.externalOutboxEnqueue = [] :=
  accepted.verified.outboxClosed

theorem accepted_zero_occurrence_is_static {pre : GlobalState}
    (accepted : Accepted pre) (zero : accepted.occurrences = []) :
    accepted.effects.IsEmpty ∧
      accepted.terminalPlan.deltas = [] ∧
      accepted.oraclePlan.deltas = [] ∧
      pre = accepted.post :=
  accepted.verified.zeroOccurrence zero

theorem rejected_post_state_is_pre_state (pre : GlobalState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).postState = pre := rfl

theorem rejected_effect_plan_is_empty (pre : GlobalState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).effectPlan.IsEmpty :=
  effectPlan_empty_has_six_empty_fields

theorem rejected_terminal_and_oracle_plans_are_empty
    (pre : GlobalState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).terminalPlan.deltas = [] ∧
      (Outcome.rejected code : Outcome pre).oraclePlan.deltas = [] :=
  ⟨rfl, rfl⟩

theorem rejected_consumes_no_occurrence (pre : GlobalState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).occurrences = [] := rfl

theorem rejected_is_no_op_bundle (pre : GlobalState) (code : RejectCode) :
    (Outcome.rejected code : Outcome pre).postState = pre ∧
      (Outcome.rejected code : Outcome pre).effectPlan.IsEmpty ∧
      (Outcome.rejected code : Outcome pre).terminalPlan.deltas = [] ∧
      (Outcome.rejected code : Outcome pre).oraclePlan.deltas = [] ∧
      (Outcome.rejected code : Outcome pre).occurrences = [] :=
  ⟨rfl, effectPlan_empty_has_six_empty_fields, rfl, rfl, rfl⟩

/-! ## Concrete non-vacuity witness for the combined relation -/

def staticGlobalState : GlobalState where
  stateRoot := "state-root"
  chainId := "chain"
  deploymentRoot := "deployment-root"
  writerEpoch := 0
  height := 0
  profileRoot := "profile-root"
  laneRoots := fun _ => "lane-root"
  laneReleaseIds := fun _ => "lane-release"
  laneEnabled := fun _ => true
  balances := []
  supplies := []
  custody := []
  liabilities := []
  reserves := []
  oracleOccurrences := fun _ => none
  replayState := fun _ => none
  terminalObligations := []
  historyRoot := "history-root"
  outbox := []

def staticTerminalPlan : TerminalPlan := ⟨[]⟩
def staticOraclePlan : OraclePlan := ⟨[]⟩

theorem static_global_state_quantities_admitted :
    StateQuantitiesAdmitted staticGlobalState := by
  simp [StateQuantitiesAdmitted, staticGlobalState, ownedFor, liabilityFor,
    amountForAsset, supplyFor, SparseAmountRowsAdmitted, SparseSupplyRowsAdmitted,
    TerminalObligationAdmitted, ReplayOccurrenceIdsInjective,
    OracleRegistryAdmitted, OracleRegistryWithinGlobalHeight,
    OracleRegistryKeysMatch, zero_fits_u128, zero_fits_u64]

theorem static_global_state_verified :
    Verified staticGlobalState EffectPlan.empty staticTerminalPlan staticOraclePlan
      [] staticGlobalState := by
  refine {
    fixedContext := ?_,
    preQuantities := static_global_state_quantities_admitted,
    postQuantities := static_global_state_quantities_admitted,
    effectPlan := empty_effectPlan_admitted,
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
  · simp [FixedContext]
  · simp [ExactLaneWrites, LaneWrittenBy, EffectPlan.empty]
  · simp [ExactEconomicTables, ExactTableEffect, amountAt, effectFor,
      staticGlobalState, EffectPlan.empty]
  · simp [ExactSupplyEffects, supplyFor, issueDeltaFor, burnDeltaFor,
      issuedFor, burnedFor, staticGlobalState, EffectPlan.empty]
  · simp [ExactConservationCoverage, EconomicAssetTouched, amountAt, supplyFor,
      staticGlobalState, EffectPlan.empty]
  · simp [ConservationRowsMatchState, EffectPlan.empty]
  · simp [AnnotationMirrors, StateBearingAggregatesFitI128,
      RunningTotalsFitI128, FeeAllocationCreditsMirrored, RewardSlashMirrored,
      FeeRowsCanonical, FeeResidueExact, positiveDesignatedResidueFor,
      positiveCarriedResidueFor, EffectPlan.empty]
  · simp [OwnedMatchesSupply, ownedFor, amountForAsset, supplyFor,
      staticGlobalState]
  · simp [OwnedMatchesSupply, ownedFor, amountForAsset, supplyFor,
      staticGlobalState]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      amountForAssetDomain, openTerminalAmountFor, amountAt,
      staticGlobalState]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      amountForAssetDomain, openTerminalAmountFor, amountAt,
      staticGlobalState]
  · simp [ExactTerminalRefinement, TerminalRegistryRefines, terminalLookup,
      TerminalOwningLaneWrites, TerminalLiabilityEffects,
      TerminalLiabilityAggregatesFitI128, RunningTotalsFitI128,
      terminalLiabilityDeltaFor, effectFor, staticGlobalState,
      staticTerminalPlan, EffectPlan.empty]
  · simp [ExactOracleRefinement, OracleRegistryRefines, OracleLaneWrite,
      staticGlobalState, staticOraclePlan, EffectPlan.empty]
  · simp [ExactReplayRefinement, OrderedOccurrenceIds, ReplayRegistryRefines,
      staticGlobalState, EffectPlan.empty, zero_fits_u64]
  · rfl
  · intro _
    exact ⟨effectPlan_empty_has_six_empty_fields, rfl, rfl, rfl⟩

def staticAccepted : Accepted staticGlobalState where
  effects := EffectPlan.empty
  terminalPlan := staticTerminalPlan
  oraclePlan := staticOraclePlan
  occurrences := []
  post := staticGlobalState
  verified := static_global_state_verified

theorem combined_verified_relation_is_inhabited :
    ∃ accepted : Accepted staticGlobalState,
      accepted.post = staticGlobalState ∧ accepted.occurrences = [] :=
  ⟨staticAccepted, rfl, rfl⟩

/-! ## Generic extraction lemmas for mutation testing -/

theorem exact_lane_writes_ignore_list_order {pre post : GlobalState}
    {left right : EffectPlan}
    (sameMembers : ∀ write, write ∈ left.laneWrites ↔ write ∈ right.laneWrites)
    (exactLeft : ExactLaneWrites pre post left) :
    ExactLaneWrites pre post right := by
  refine ⟨?_, exactLeft.2.1, ?_⟩
  · intro lane
    constructor
    · rintro ⟨write, member, laneEqual⟩
      exact (exactLeft.1 lane).1 ⟨write, (sameMembers write).2 member, laneEqual⟩
    · intro changed
      obtain ⟨write, member, laneEqual⟩ := (exactLeft.1 lane).2 changed
      exact ⟨write, (sameMembers write).1 member, laneEqual⟩
  · intro write member
    exact exactLeft.2.2 write ((sameMembers write).2 member)

theorem changed_lane_requires_exact_write {pre post : GlobalState}
    {effects : EffectPlan} (exactWrites : ExactLaneWrites pre post effects)
    {lane : LaneId} (changed : pre.laneRoots lane ≠ post.laneRoots lane) :
    ∃ write ∈ effects.laneWrites,
      write.laneId = lane ∧
      write.preRoot = pre.laneRoots lane ∧
      write.postRoot = post.laneRoots lane := by
  obtain ⟨write, writeMember, laneEqual⟩ := (exactWrites.1 lane).2 changed
  refine ⟨write, writeMember, laneEqual, ?_, ?_⟩
  · simpa [laneEqual] using (exactWrites.2.2 write writeMember).2.1
  · simpa [laneEqual] using (exactWrites.2.2 write writeMember).2.2

theorem terminal_delta_requires_owning_lane_write {pre post : GlobalState}
    {effects : EffectPlan} {terminalPlan : TerminalPlan}
    (exactTerminal : ExactTerminalRefinement pre post effects terminalPlan)
    {delta : TerminalDelta} (member : delta ∈ terminalPlan.deltas) :
    ∃ write ∈ effects.laneWrites, write.laneId = delta.postObligation.laneId :=
  exactTerminal.2.1 delta member

theorem terminal_member_preserves_identity_and_status_progression
    {pre post : GlobalState} {effects : EffectPlan} {terminalPlan : TerminalPlan}
    (exactTerminal : ExactTerminalRefinement pre post effects terminalPlan)
    {delta : TerminalDelta} (member : delta ∈ terminalPlan.deltas) :
    TerminalDeltaAdmitted delta :=
  (exactTerminal.1.2.1 delta member).2.2

theorem oracle_delta_requires_oracle_lane_write {pre post : GlobalState}
    {effects : EffectPlan} {oraclePlan : OraclePlan}
    (exactOracle : ExactOracleRefinement pre post effects oraclePlan)
    (nonempty : oraclePlan.deltas ≠ []) :
    ∃ write ∈ effects.laneWrites, write.laneId = .oracleMarket := by
  rcases exactOracle.2 with empty | write
  · exact absurd empty nonempty
  · exact write

theorem oracle_member_preserves_height_finality_and_same_height_root
    {pre post : GlobalState} {effects : EffectPlan} {oraclePlan : OraclePlan}
    (exactOracle : ExactOracleRefinement pre post effects oraclePlan)
    {delta : OracleDelta} (member : delta ∈ oraclePlan.deltas) :
    OracleDeltaAdmitted delta :=
  (exactOracle.1.2.1 delta member).2.2

/-! ## Minimized semantic mutations -/

def demoPreLaneRoots (_ : LaneId) : RootId := "same-root"

def demoPostLaneRoots : LaneId → RootId
  | .assetTransfer => "changed-root"
  | _ => "same-root"

def demoDisabledLaneEnabled : LaneId → Bool
  | .assetTransfer => false
  | _ => true

def disabledLanePreState : GlobalState :=
  { staticGlobalState with
    laneRoots := demoPreLaneRoots
    laneEnabled := demoDisabledLaneEnabled }

def disabledLanePostState : GlobalState :=
  { disabledLanePreState with laneRoots := demoPostLaneRoots }

def disabledLaneWritePlan : EffectPlan :=
  { EffectPlan.empty with
    laneWrites := [⟨.assetTransfer, "same-root", "changed-root"⟩] }

theorem disabled_lane_write_rejected :
    ¬ ExactLaneWrites disabledLanePreState disabledLanePostState
      disabledLaneWritePlan := by
  intro exactWrites
  have changed :
      disabledLanePreState.laneRoots .assetTransfer ≠
        disabledLanePostState.laneRoots .assetTransfer := by
    decide
  have enabled := exactWrites.2.1 .assetTransfer changed
  change false = true at enabled
  contradiction

theorem empty_write_set_rejects_changed_lane
    (pre post : GlobalState)
    (preRoots : pre.laneRoots = demoPreLaneRoots)
    (postRoots : post.laneRoots = demoPostLaneRoots) :
    ¬ ExactLaneWrites pre post EffectPlan.empty := by
  intro exactWrites
  have changed : pre.laneRoots .assetTransfer ≠ post.laneRoots .assetTransfer := by
    rw [preRoots, postRoots]
    decide
  obtain ⟨write, member, _⟩ :=
    changed_lane_requires_exact_write exactWrites changed
  simp [EffectPlan.empty] at member

def zeroSparseAmountRows : List AmountRow :=
  [⟨"alice", "ZUSD", "accounts", 0⟩]

theorem zero_sparse_amount_row_rejected :
    ¬ SparseAmountRowsAdmitted zeroSparseAmountRows := by
  intro admitted
  have nonzero := (admitted ⟨"alice", "ZUSD", "accounts", 0⟩
    (by simp [zeroSparseAmountRows])).2
  exact nonzero rfl

def zeroSparseSupplyRows : List SupplyRow :=
  [⟨"ZUSD", 0⟩]

theorem zero_sparse_supply_row_rejected :
    ¬ SparseSupplyRowsAdmitted zeroSparseSupplyRows := by
  intro admitted
  have nonzero := (admitted ⟨"ZUSD", 0⟩
    (by simp [zeroSparseSupplyRows])).2
  exact nonzero rfl

def replayAliasRegistry (replayId : Identifier) : Option RootId :=
  if replayId = "replay-a" ∨ replayId = "replay-b" then
    some "shared-occurrence"
  else
    none

def replayAliasState : GlobalState :=
  { staticGlobalState with replayState := replayAliasRegistry }

theorem replay_occurrence_alias_rejected :
    ¬ ReplayOccurrenceIdsInjective replayAliasState := by
  intro injective
  have aliases := injective "replay-a" "replay-b" "shared-occurrence"
    (by simp [replayAliasState, replayAliasRegistry])
    (by simp [replayAliasState, replayAliasRegistry])
  exact (by decide : "replay-a" ≠ "replay-b") aliases

def oracleKeyMismatchOccurrence : OracleOccurrence :=
  ⟨"payload-oracle", "oracle-root", 0, .pending⟩

def oracleKeyMismatchRegistry (oracleId : Identifier) : Option OracleOccurrence :=
  if oracleId = "registry-oracle" then some oracleKeyMismatchOccurrence else none

def oracleKeyMismatchState : GlobalState :=
  { staticGlobalState with oracleOccurrences := oracleKeyMismatchRegistry }

theorem oracle_lookup_key_mismatch_rejected :
    ¬ OracleRegistryKeysMatch oracleKeyMismatchState := by
  intro keysMatch
  have mismatch := keysMatch "registry-oracle" oracleKeyMismatchOccurrence
    (by simp [oracleKeyMismatchState, oracleKeyMismatchRegistry])
  exact (by decide : "payload-oracle" ≠ "registry-oracle") mismatch

def maximumStateBearingRow : EconomicEffectRow :=
  ⟨.accountMovement, "alice", "ZUSD", "accounts", maxI128⟩

def oneStateBearingRow : EconomicEffectRow :=
  ⟨.custody, "alice", "ZUSD", "accounts", 1⟩

def stateBearingOverflowPlan : EffectPlan :=
  { EffectPlan.empty with rows := [maximumStateBearingRow, oneStateBearingRow] }

theorem state_bearing_annotation_overflow_rejected :
    ¬ StateBearingAggregatesFitI128 stateBearingOverflowPlan := by
  intro admitted
  have overflow := (admitted "alice" "ZUSD" "accounts").2.1
  have impossible := overflow.2
  change maxI128 + 1 ≤ maxI128 at impossible
  omega

def underbackedLiability : List AmountRow :=
  [⟨"alice", "ZUSD", "zenoledger:claims", 5⟩]

def insufficientCustody : List AmountRow :=
  [⟨"reserve", "ZUSD", "zenoledger:claims", 4⟩]

theorem underbacked_claimant_liability_rejected :
    ¬ (∀ asset domain,
      0 ≤ amountForAssetDomain underbackedLiability asset domain ∧
      amountForAssetDomain underbackedLiability asset domain ≤
        amountForAssetDomain insufficientCustody asset domain) := by
  intro backed
  have bound := (backed "ZUSD" "zenoledger:claims").2
  change (5 : Int) ≤ 4 at bound
  omega

def crossDomainLiability : List AmountRow :=
  [⟨"alice", "ZUSD", "zenoledger:claims", 4⟩]

def unrelatedDomainCustody : List AmountRow :=
  [⟨"reserve", "ZUSD", "zenoledger:reserve", 4⟩]

theorem cross_domain_custody_cannot_back_liability :
    ¬ (∀ asset domain,
      0 ≤ amountForAssetDomain crossDomainLiability asset domain ∧
      amountForAssetDomain crossDomainLiability asset domain ≤
        amountForAssetDomain unrelatedDomainCustody asset domain) := by
  intro backed
  have bound := (backed "ZUSD" "zenoledger:claims").2
  change (4 : Int) ≤ 0 at bound
  omega

def undercreditedFeePlan : EffectPlan :=
  { EffectPlan.empty with
    rows :=
      [ ⟨.accountMovement, "fee-owner", "ZUSD", "accounts", 1⟩,
        ⟨.feeAllocation, "fee-owner", "ZUSD", "accounts", 2⟩ ]
    feeConservation := [⟨"ZUSD", 2, 2, 0⟩] }

theorem undercredited_fee_allocation_rejected :
    ¬ AnnotationMirrors undercreditedFeePlan := by
  intro mirrors
  have allocation := mirrors.2.1
    ⟨.feeAllocation, "fee-owner", "ZUSD", "accounts", 2⟩
    (by simp [undercreditedFeePlan, EffectPlan.empty]) rfl
  have impossible := allocation.2
  change (2 : Int) ≤ 1 at impossible
  omega

def zeroFeeConservationPlan : EffectPlan :=
  { EffectPlan.empty with feeConservation := [⟨"ZUSD", 0, 0, 0⟩] }

theorem zero_fee_conservation_row_rejected :
    ¬ AnnotationMirrors zeroFeeConservationPlan := by
  intro mirrors
  have canonical := mirrors.2.2.2.1
    ⟨"ZUSD", 0, 0, 0⟩
    (by simp [zeroFeeConservationPlan, EffectPlan.empty])
  change (0 : Int) < 0 at canonical
  omega

def wrongFeeResiduePlan : EffectPlan :=
  { EffectPlan.empty with
    rows := [⟨.reserve, "reserve:wrong", "ZUSD", "wrong-domain", 2⟩]
    feeConservation := [⟨"ZUSD", 2, 0, 2⟩] }

theorem wrong_fee_residue_location_rejected :
    ¬ AnnotationMirrors wrongFeeResiduePlan := by
  intro mirrors
  have residue := mirrors.2.2.2.2 "ZUSD"
  change (0 : Int) = 2 at residue
  omega

def exactFeeResiduePlan : EffectPlan :=
  { EffectPlan.empty with
    rows :=
      [⟨.reserve, feeResiduePrincipal, "ZUSD", feeResidueAccountingLocation, 2⟩]
    feeConservation := [⟨"ZUSD", 2, 0, 2⟩] }

theorem exact_fee_residue_location_is_admitted :
    AnnotationMirrors exactFeeResiduePlan := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro owner asset domain
    by_cases sameCoordinates : feeResiduePrincipal = owner ∧ "ZUSD" = asset ∧
        feeResidueAccountingLocation = domain
    · simp [RunningTotalsFitI128,
        stateBearingContribution, exactFeeResiduePlan, EffectPlan.empty,
        sameCoordinates, FitsI128, minI128, maxI128]
    · simp [RunningTotalsFitI128,
        stateBearingContribution, exactFeeResiduePlan, EffectPlan.empty,
        sameCoordinates, FitsI128, minI128, maxI128]
  · simp [FeeAllocationCreditsMirrored, exactFeeResiduePlan, EffectPlan.empty]
  · simp [RewardSlashMirrored, exactFeeResiduePlan, EffectPlan.empty]
  · simp [FeeRowsCanonical, exactFeeResiduePlan, EffectPlan.empty]
  · intro asset
    by_cases isZusd : asset = "ZUSD"
    · subst isZusd
      simp [positiveDesignatedResidueFor,
        positiveCarriedResidueFor, exactFeeResiduePlan, EffectPlan.empty,
        feeResiduePrincipal, feeResidueAccountingLocation]
    · simp [positiveDesignatedResidueFor,
        positiveCarriedResidueFor, exactFeeResiduePlan, EffectPlan.empty,
        feeResiduePrincipal, feeResidueAccountingLocation]

def zeroOpenTerminal : TerminalObligation :=
  ⟨"obligation-zero", .perpsMarket, "alice", "ZUSD", "claims", 0, .open⟩

theorem zero_open_terminal_amount_rejected :
    ¬ TerminalObligationAdmitted zeroOpenTerminal := by
  intro admitted
  have positive := admitted.2 rfl
  change (0 : Int) < 0 at positive
  omega

def futureOracleOccurrence : OracleOccurrence :=
  ⟨"oracle-future", "root-future", 8, .pending⟩

theorem future_oracle_observation_rejected :
    ¬ OracleOccurrenceWithinHeight 7 futureOracleOccurrence := by
  intro admitted
  have impossible := admitted.2
  change 8 ≤ 7 at impossible
  omega

def uncoveredOpenTerminals : TerminalRegistry :=
  [⟨"obligation-3", .perpsMarket, "alice", "ZUSD", "claims", 3, .open⟩]

def insufficientExactLiability : List AmountRow :=
  [⟨"alice", "ZUSD", "claims", 2⟩]

theorem open_terminal_total_above_exact_liability_rejected :
    ¬ (∀ owner asset domain,
      0 ≤ openTerminalAmountFor uncoveredOpenTerminals owner asset domain ∧
      openTerminalAmountFor uncoveredOpenTerminals owner asset domain ≤
        amountAt insufficientExactLiability owner asset domain) := by
  intro covered
  have impossible := (covered "alice" "ZUSD" "claims").2
  change (3 : Int) ≤ 2 at impossible
  omega

def maximumTerminalLiabilityDelta : TerminalDelta where
  obligationId := "obligation-maximum"
  preObligation := none
  postObligation :=
    ⟨"obligation-maximum", .perpsMarket, "alice", "ZUSD", "claims", maxI128, .open⟩

def oneTerminalLiabilityDelta : TerminalDelta where
  obligationId := "obligation-one"
  preObligation := none
  postObligation :=
    ⟨"obligation-one", .perpsMarket, "alice", "ZUSD", "claims", 1, .open⟩

def terminalLiabilityOverflowPlan : TerminalPlan :=
  ⟨[maximumTerminalLiabilityDelta, oneTerminalLiabilityDelta]⟩

theorem terminal_liability_aggregate_overflow_rejected :
    ¬ TerminalLiabilityAggregatesFitI128 terminalLiabilityOverflowPlan := by
  intro admitted
  have overflow := (admitted "alice" "ZUSD" "claims").2.1
  have impossible := overflow.2
  change maxI128 + 1 ≤ maxI128 at impossible
  omega

def terminalIdentityMutation : TerminalDelta where
  obligationId := "obligation-1"
  preObligation := some
    ⟨"obligation-1", .assetTransfer, "alice", "ZUSD", "claims", 5, .open⟩
  postObligation :=
    ⟨"obligation-1", .assetTransfer, "mallory", "ZUSD", "claims", 5, .drained⟩

theorem terminal_claimant_mutation_rejected :
    ¬ TerminalDeltaAdmitted terminalIdentityMutation := by
  intro admitted
  simp [TerminalDeltaAdmitted, TerminalObligationAdmitted,
    terminalIdentityMutation, TerminalIdentityPreserved] at admitted

def oracleSameHeightRootMutation : OracleDelta where
  oracleId := "oracle-1"
  preOccurrence := some ⟨"oracle-1", "root-a", 9, .finalized⟩
  postOccurrence := ⟨"oracle-1", "root-b", 9, .finalized⟩

theorem oracle_same_height_root_mutation_rejected :
    ¬ OracleDeltaAdmitted oracleSameHeightRootMutation := by
  intro admitted
  simp [OracleDeltaAdmitted, oracleSameHeightRootMutation] at admitted

def duplicateOccurrences : List CommandOccurrence :=
  [ ⟨"occurrence-a", "replay-a", "chain", "deploy", "profile", "pre", 1⟩,
    ⟨"occurrence-a", "replay-b", "chain", "deploy", "profile", "pre", 1⟩ ]

theorem duplicate_occurrence_order_rejected :
    ¬ OrderedOccurrenceIds duplicateOccurrences := by
  intro ordered
  simp [OrderedOccurrenceIds, duplicateOccurrences] at ordered

def oneExternalEnqueue : ExternalOutboxEnqueue :=
  ⟨"effect", "external:destination", "payload", "adapter"⟩

def externalEnqueueMutation : EffectPlan :=
  { EffectPlan.empty with externalOutboxEnqueue := [oneExternalEnqueue] }

theorem external_enqueue_rejected_before_o009 :
    ¬ PreO009OutboxClosed externalEnqueueMutation := by
  intro closed
  simp [PreO009OutboxClosed, externalEnqueueMutation, EffectPlan.empty] at closed

theorem zero_occurrence_changed_state_rejected {pre post : GlobalState}
    {effects : EffectPlan} {terminalPlan : TerminalPlan} {oraclePlan : OraclePlan}
    (changed : pre ≠ post) :
    ¬ ZeroOccurrenceStatic pre post effects terminalPlan oraclePlan [] := by
  intro static
  have bundle := static rfl
  exact changed bundle.2.2.2

end GlobalEconomicStateRefinementV2
end Proofs
