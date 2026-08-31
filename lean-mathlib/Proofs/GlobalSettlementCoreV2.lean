import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# GlobalSettlementABI V2 bounded structural core

This file gives a machine-checked, source-scoped model of the shared V2
settlement vocabulary.  Roots and identifiers are opaque `String` values.
No theorem assumes collision resistance, digest injectivity, canonical SHA-256
encoding, or equality between a root and the state it names.

## Modeled runtime fields

The model fixes the exact twelve lane wire values, the exact nine economic
effect wire values, and the six fields of `GlobalEconomicEffectPlanV2`:
`rows`, `asset_conservation`, `fee_conservation`, `lane_writes`,
`occurrence_consumptions`, and `external_outbox_enqueue`.  Economic rows carry
`kind`, `principal`, `asset`, `custody_domain`, and `delta_atoms`.  Asset
conservation rows carry all seven live Python fields.  Issue and burn are
projected independently, so an equal issue/burn mutation cannot disappear in
a net delta.

`FitsU128`, `FitsI128`, and `FitsU64` state the integer-width obligations
explicitly.  Lean integer arithmetic is mathematical arithmetic; this model
does not model machine wraparound.

## Omitted runtime fields and behaviours

The model omits UTF-8/ASCII token syntax, root syntax, canonical JSON bytes,
hash-domain bytes, the 1 MiB canonical-byte ceiling, terminal/Oracle/global-state
collection ceilings, tuple snapshot ownership, Python exception precedence,
dataclass implementation details, state-bearing fee/reward/slash annotation
mirroring, external adapter execution, and every lane-specific command schema.
Canonical tuple sorting is tested by Python and is not proved by this file.

## Claim boundary

These theorems confer no verifier authority, publisher authority, settlement
authority, value-moving authority, release status, or production readiness.
They do not establish Python/Rust refinement, runtime reachability, economic
policy correctness, legal custody, hash collision resistance, or root
injectivity.  `custody_domain` is an accounting-location label only.
-/

namespace Proofs
namespace GlobalSettlementCoreV2

abbrev RootId := String
abbrev Identifier := String
abbrev Principal := String
abbrev Asset := String
abbrev AccountingLocation := String

/-! ## Integer-width predicates -/

def maxU128 : Int := 2 ^ 128 - 1
def minI128 : Int := -(2 ^ 127)
def maxI128 : Int := 2 ^ 127 - 1
def maxU64 : Nat := 2 ^ 64 - 1

def FitsU128 (value : Int) : Prop := 0 ≤ value ∧ value ≤ maxU128
def FitsI128 (value : Int) : Prop := minI128 ≤ value ∧ value ≤ maxI128
def FitsU64 (value : Nat) : Prop := value ≤ maxU64

theorem zero_fits_u128 : FitsU128 0 := by
  unfold FitsU128 maxU128
  omega

theorem zero_fits_i128 : FitsI128 0 := by
  unfold FitsI128 minI128 maxI128
  omega

theorem zero_fits_u64 : FitsU64 0 := by
  unfold FitsU64 maxU64
  omega

/-! ## Closed lane registry -/

inductive LaneId where
  | assetTransfer
  | spotLiquidity
  | farmIncentives
  | zdexTokenomics
  | zusdMonetary
  | perpsMarket
  | oracleMarket
  | sealedAuction
  | strategyEscrow
  | proofRewards
  | externalCustody
  | governanceMigration
  deriving DecidableEq, Repr

def LaneId.code : LaneId → String
  | .assetTransfer => "ASSET_TRANSFER"
  | .spotLiquidity => "SPOT_LIQUIDITY"
  | .farmIncentives => "FARM_INCENTIVES"
  | .zdexTokenomics => "ZDEX_TOKENOMICS"
  | .zusdMonetary => "ZUSD_MONETARY"
  | .perpsMarket => "PERPS_MARKET"
  | .oracleMarket => "ORACLE_MARKET"
  | .sealedAuction => "SEALED_AUCTION"
  | .strategyEscrow => "STRATEGY_ESCROW"
  | .proofRewards => "PROOF_REWARDS"
  | .externalCustody => "EXTERNAL_CUSTODY"
  | .governanceMigration => "GOVERNANCE_MIGRATION"

def LaneId.index : LaneId → Nat
  | .assetTransfer => 0
  | .spotLiquidity => 1
  | .farmIncentives => 2
  | .zdexTokenomics => 3
  | .zusdMonetary => 4
  | .perpsMarket => 5
  | .oracleMarket => 6
  | .sealedAuction => 7
  | .strategyEscrow => 8
  | .proofRewards => 9
  | .externalCustody => 10
  | .governanceMigration => 11

def allLaneIds : List LaneId :=
  [ .assetTransfer, .spotLiquidity, .farmIncentives, .zdexTokenomics,
    .zusdMonetary, .perpsMarket, .oracleMarket, .sealedAuction,
    .strategyEscrow, .proofRewards, .externalCustody, .governanceMigration ]

theorem allLaneIds_length : allLaneIds.length = 12 := rfl

theorem allLaneIds_codes :
    allLaneIds.map LaneId.code =
      [ "ASSET_TRANSFER", "SPOT_LIQUIDITY", "FARM_INCENTIVES",
        "ZDEX_TOKENOMICS", "ZUSD_MONETARY", "PERPS_MARKET",
        "ORACLE_MARKET", "SEALED_AUCTION", "STRATEGY_ESCROW",
        "PROOF_REWARDS", "EXTERNAL_CUSTODY", "GOVERNANCE_MIGRATION" ] := rfl

theorem allLaneIds_indices :
    allLaneIds.map LaneId.index = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := rfl

theorem allLaneIds_complete (lane : LaneId) : lane ∈ allLaneIds := by
  cases lane <;> decide

theorem allLaneIds_noDuplicates : allLaneIds.Nodup := by
  decide

theorem LaneId.index_injective {left right : LaneId}
    (equalIndex : left.index = right.index) : left = right := by
  cases left <;> cases right <;> simp_all [LaneId.index]

/-! ## Closed economic-effect registry -/

inductive EffectKind where
  | accountMovement
  | issue
  | burn
  | custody
  | liability
  | reserve
  | feeAllocation
  | reward
  | slash
  deriving DecidableEq, Repr

def EffectKind.code : EffectKind → String
  | .accountMovement => "ACCOUNT_MOVEMENT"
  | .issue => "ISSUE"
  | .burn => "BURN"
  | .custody => "CUSTODY"
  | .liability => "LIABILITY"
  | .reserve => "RESERVE"
  | .feeAllocation => "FEE_ALLOCATION"
  | .reward => "REWARD"
  | .slash => "SLASH"

def allEffectKinds : List EffectKind :=
  [ .accountMovement, .issue, .burn, .custody, .liability, .reserve,
    .feeAllocation, .reward, .slash ]

theorem allEffectKinds_length : allEffectKinds.length = 9 := rfl

theorem allEffectKinds_codes :
    allEffectKinds.map EffectKind.code =
      [ "ACCOUNT_MOVEMENT", "ISSUE", "BURN", "CUSTODY", "LIABILITY",
        "RESERVE", "FEE_ALLOCATION", "REWARD", "SLASH" ] := rfl

theorem allEffectKinds_complete (kind : EffectKind) : kind ∈ allEffectKinds := by
  cases kind <;> decide

theorem allEffectKinds_noDuplicates : allEffectKinds.Nodup := by
  decide

/-! ## Exact effect-plan value shapes -/

structure EconomicEffectRow where
  kind : EffectKind
  principal : Principal
  asset : Asset
  custodyDomain : AccountingLocation
  deltaAtoms : Int
  deriving DecidableEq, Repr

def EconomicEffectRow.key (row : EconomicEffectRow) :
    EffectKind × Asset × Principal × AccountingLocation :=
  (row.kind, row.asset, row.principal, row.custodyDomain)

structure AssetConservationRow where
  asset : Asset
  ownedAndCustodiedPreAtoms : Int
  ownedAndCustodiedPostAtoms : Int
  supplyPreAtoms : Int
  supplyPostAtoms : Int
  authorizedIssueAtoms : Int
  authorizedBurnAtoms : Int
  deriving DecidableEq, Repr

structure FeeConservationRow where
  asset : Asset
  feeChargedAtoms : Int
  currentAllocationsAtoms : Int
  carriedResidueAtoms : Int
  deriving DecidableEq, Repr

structure LaneWrite where
  laneId : LaneId
  preRoot : RootId
  postRoot : RootId
  deriving DecidableEq, Repr

structure ExternalOutboxEnqueue where
  effectId : RootId
  destinationId : Identifier
  payloadHash : RootId
  adapterProfileRoot : RootId
  deriving DecidableEq, Repr

/-- The field order mirrors `GlobalEconomicEffectPlanV2.to_canonical`. -/
structure EffectPlan where
  rows : List EconomicEffectRow
  assetConservation : List AssetConservationRow
  feeConservation : List FeeConservationRow
  laneWrites : List LaneWrite
  occurrenceConsumptions : List RootId
  externalOutboxEnqueue : List ExternalOutboxEnqueue
  deriving DecidableEq, Repr

def EffectPlan.empty : EffectPlan where
  rows := []
  assetConservation := []
  feeConservation := []
  laneWrites := []
  occurrenceConsumptions := []
  externalOutboxEnqueue := []

def EffectPlan.IsEmpty (plan : EffectPlan) : Prop :=
  plan.rows = [] ∧
  plan.assetConservation = [] ∧
  plan.feeConservation = [] ∧
  plan.laneWrites = [] ∧
  plan.occurrenceConsumptions = [] ∧
  plan.externalOutboxEnqueue = []

theorem effectPlan_empty_has_six_empty_fields : EffectPlan.empty.IsEmpty := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EffectPlan.ext_six_fields {left right : EffectPlan}
    (rows : left.rows = right.rows)
    (assets : left.assetConservation = right.assetConservation)
    (fees : left.feeConservation = right.feeConservation)
    (lanes : left.laneWrites = right.laneWrites)
    (occurrences : left.occurrenceConsumptions = right.occurrenceConsumptions)
    (outbox : left.externalOutboxEnqueue = right.externalOutboxEnqueue) :
    left = right := by
  cases left
  cases right
  simp_all

/-! ## Independent per-asset issue and burn projections -/

def issueContribution (asset : Asset) (row : EconomicEffectRow) : Int :=
  if row.kind = .issue ∧ row.asset = asset then row.deltaAtoms else 0

def burnContribution (asset : Asset) (row : EconomicEffectRow) : Int :=
  if row.kind = .burn ∧ row.asset = asset then -row.deltaAtoms else 0

def issuedFor (asset : Asset) (rows : List EconomicEffectRow) : Int :=
  (rows.map (issueContribution asset)).sum

def burnedFor (asset : Asset) (rows : List EconomicEffectRow) : Int :=
  (rows.map (burnContribution asset)).sum

def declaredIssueFor (asset : Asset) (rows : List AssetConservationRow) : Int :=
  (rows.map fun row => if row.asset = asset then row.authorizedIssueAtoms else 0).sum

def declaredBurnFor (asset : Asset) (rows : List AssetConservationRow) : Int :=
  (rows.map fun row => if row.asset = asset then row.authorizedBurnAtoms else 0).sum

def feeAllocationContribution (asset : Asset) (row : EconomicEffectRow) : Int :=
  if row.kind = .feeAllocation ∧ row.asset = asset then row.deltaAtoms else 0

def allocatedFeeFor (asset : Asset) (rows : List EconomicEffectRow) : Int :=
  (rows.map (feeAllocationContribution asset)).sum

def declaredCurrentAllocationsFor (asset : Asset)
    (rows : List FeeConservationRow) : Int :=
  (rows.map fun row => if row.asset = asset then row.currentAllocationsAtoms else 0).sum

def ProjectionMatches (plan : EffectPlan) : Prop :=
  ∀ asset,
    declaredIssueFor asset plan.assetConservation = issuedFor asset plan.rows ∧
    declaredBurnFor asset plan.assetConservation = burnedFor asset plan.rows

def FeeProjectionMatches (plan : EffectPlan) : Prop :=
  ∀ asset,
    declaredCurrentAllocationsFor asset plan.feeConservation =
      allocatedFeeFor asset plan.rows

def NetProjectionMatches (plan : EffectPlan) : Prop :=
  ∀ asset,
    declaredIssueFor asset plan.assetConservation -
        declaredBurnFor asset plan.assetConservation =
      issuedFor asset plan.rows - burnedFor asset plan.rows

theorem projectionMatches_implies_net {plan : EffectPlan}
    (projection : ProjectionMatches plan) : NetProjectionMatches plan := by
  intro asset
  rw [(projection asset).1, (projection asset).2]

theorem issuedFor_append (asset : Asset) (left right : List EconomicEffectRow) :
    issuedFor asset (left ++ right) = issuedFor asset left + issuedFor asset right := by
  unfold issuedFor
  induction left with
  | nil => simp
  | cons row rest inductionHypothesis =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [inductionHypothesis]
      omega

theorem burnedFor_append (asset : Asset) (left right : List EconomicEffectRow) :
    burnedFor asset (left ++ right) = burnedFor asset left + burnedFor asset right := by
  unfold burnedFor
  induction left with
  | nil => simp
  | cons row rest inductionHypothesis =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [inductionHypothesis]
      omega

theorem issue_ignores_other_asset {wanted : Asset} {row : EconomicEffectRow}
    (different : row.asset ≠ wanted) : issueContribution wanted row = 0 := by
  simp [issueContribution, different]

theorem burn_ignores_other_asset {wanted : Asset} {row : EconomicEffectRow}
    (different : row.asset ≠ wanted) : burnContribution wanted row = 0 := by
  simp [burnContribution, different]

/-! ## Row admission and finite plan bounds -/

def EffectRowAdmitted (row : EconomicEffectRow) : Prop :=
  FitsI128 row.deltaAtoms ∧
  row.deltaAtoms ≠ 0 ∧
  (row.kind = .issue → 0 < row.deltaAtoms) ∧
  (row.kind = .burn → row.deltaAtoms < 0) ∧
  (row.kind = .feeAllocation → 0 < row.deltaAtoms)

def AssetConservationAdmitted (row : AssetConservationRow) : Prop :=
  FitsU128 row.ownedAndCustodiedPreAtoms ∧
  FitsU128 row.ownedAndCustodiedPostAtoms ∧
  FitsU128 row.supplyPreAtoms ∧
  FitsU128 row.supplyPostAtoms ∧
  FitsU128 row.authorizedIssueAtoms ∧
  FitsU128 row.authorizedBurnAtoms ∧
  row.ownedAndCustodiedPostAtoms =
    row.ownedAndCustodiedPreAtoms + row.authorizedIssueAtoms - row.authorizedBurnAtoms ∧
  row.supplyPostAtoms =
    row.supplyPreAtoms + row.authorizedIssueAtoms - row.authorizedBurnAtoms

def FeeConservationAdmitted (row : FeeConservationRow) : Prop :=
  FitsU128 row.feeChargedAtoms ∧
  FitsU128 row.currentAllocationsAtoms ∧
  FitsU128 row.carriedResidueAtoms ∧
  row.feeChargedAtoms = row.currentAllocationsAtoms + row.carriedResidueAtoms

def PlanWithinItemBounds (plan : EffectPlan) : Prop :=
  plan.rows.length ≤ 4096 ∧
  plan.assetConservation.length ≤ 256 ∧
  plan.feeConservation.length ≤ 256 ∧
  plan.laneWrites.length ≤ 12 ∧
  plan.occurrenceConsumptions.length ≤ 64 ∧
  plan.externalOutboxEnqueue.length ≤ 4096 ∧
  plan.rows.length + plan.assetConservation.length + plan.feeConservation.length +
      plan.laneWrites.length + plan.occurrenceConsumptions.length +
      plan.externalOutboxEnqueue.length ≤ 8192

def PlanKeysUnique (plan : EffectPlan) : Prop :=
  (plan.rows.map EconomicEffectRow.key).Nodup ∧
  (plan.assetConservation.map (fun row => row.asset)).Nodup ∧
  (plan.feeConservation.map (fun row => row.asset)).Nodup ∧
  (plan.laneWrites.map (fun row => row.laneId)).Nodup ∧
  plan.occurrenceConsumptions.Nodup ∧
  (plan.externalOutboxEnqueue.map (fun row => row.effectId)).Nodup

def EffectPlanAdmitted (plan : EffectPlan) : Prop :=
  (∀ row ∈ plan.rows, EffectRowAdmitted row) ∧
  (∀ row ∈ plan.assetConservation, AssetConservationAdmitted row) ∧
  (∀ row ∈ plan.feeConservation, FeeConservationAdmitted row) ∧
  ProjectionMatches plan ∧
  FeeProjectionMatches plan ∧
  PlanWithinItemBounds plan ∧
  PlanKeysUnique plan

theorem empty_effectPlan_admitted : EffectPlanAdmitted EffectPlan.empty := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [EffectPlan.empty]
  · simp [EffectPlan.empty]
  · simp [EffectPlan.empty]
  · intro asset
    simp [EffectPlan.empty, declaredIssueFor, declaredBurnFor, issuedFor, burnedFor]
  · intro asset
    simp [EffectPlan.empty, declaredCurrentAllocationsFor, allocatedFeeFor]
  · simp [PlanWithinItemBounds, EffectPlan.empty]
  · simp [PlanKeysUnique, EffectPlan.empty]

/-! ## Fee-allocation projection mutations -/

def negativeFeeAllocationRow : EconomicEffectRow :=
  ⟨.feeAllocation, "fee-recipient", "ZUSD", "zenoledger:fees", -1⟩

theorem negative_fee_allocation_rejected :
    ¬ EffectRowAdmitted negativeFeeAllocationRow := by
  intro admitted
  have positive := admitted.2.2.2.2 rfl
  change (0 : Int) < -1 at positive
  omega

def mismatchedFeeAllocationRow : EconomicEffectRow :=
  ⟨.feeAllocation, "fee-recipient", "ZUSD", "zenoledger:fees", 2⟩

def mismatchedFeeConservationRow : FeeConservationRow :=
  ⟨"ZUSD", 1, 1, 0⟩

def feeProjectionMismatchPlan : EffectPlan :=
  { EffectPlan.empty with
    rows := [mismatchedFeeAllocationRow]
    feeConservation := [mismatchedFeeConservationRow] }

theorem fee_projection_mismatch_rejected :
    ¬ FeeProjectionMatches feeProjectionMismatchPlan := by
  intro projection
  have mismatch := projection "ZUSD"
  change (1 : Int) = 2 at mismatch
  omega

/-! ## A minimized net-preserving mutation -/

def demoIssueRow : EconomicEffectRow :=
  ⟨.issue, "issuer", "ZUSD", "zenoledger:core", 5⟩

def demoBurnRow : EconomicEffectRow :=
  ⟨.burn, "burner", "ZUSD", "zenoledger:core", -5⟩

def netOnlyMutationPlan : EffectPlan :=
  { EffectPlan.empty with rows := [demoIssueRow, demoBurnRow] }

theorem netOnlyMutation_has_zero_net : NetProjectionMatches netOnlyMutationPlan := by
  intro asset
  by_cases isZusd : asset = "ZUSD"
  · subst isZusd
    simp [netOnlyMutationPlan, EffectPlan.empty, demoIssueRow, demoBurnRow,
      declaredIssueFor, declaredBurnFor, issuedFor, burnedFor,
      issueContribution, burnContribution]
  · simp [netOnlyMutationPlan, EffectPlan.empty, demoIssueRow, demoBurnRow,
      declaredIssueFor, declaredBurnFor, issuedFor, burnedFor,
      issueContribution, burnContribution]

theorem netOnlyMutation_projection_rejected : ¬ ProjectionMatches netOnlyMutationPlan := by
  intro projection
  have issueMismatch := (projection "ZUSD").1
  change (0 : Int) = 5 at issueMismatch
  omega

end GlobalSettlementCoreV2
end Proofs
