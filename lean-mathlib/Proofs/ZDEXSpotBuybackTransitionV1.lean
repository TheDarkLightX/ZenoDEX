import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Proofs.ZDEXBuybackPriceSafetyV1

/-!
Formal functional core for the Spot-owned part of one governed,
same-occurrence ZDEX buy-and-burn route.

The command carries an occurrence-bound quote input port. Purchased ZDEX is
derived from the selected pool and cannot be supplied by a caller. The
transition owns only Spot pool state and Spot custody effects. Tokenomics
reserve spending, supply burn, Oracle finality, global replay consumption, and
atomic publication remain separate state-machine obligations.

This file models a canonical sorted pool registry and exact semantic values.
It does not establish collision resistance of runtime hashes, canonical-byte
refinement, Python/Rust parity, RISC0 receipt validity, route composition, or
durable publication. Those remain release-blocking refinement obligations.
-/

namespace Proofs
namespace ZDEXSpotBuybackTransitionV1

abbrev Root := Nat
abbrev AssetId := Nat
abbrev PrincipalId := Nat
abbrev ReleaseId := Nat
abbrev OccurrenceId := Nat
abbrev PoolId := Nat
abbrev PricePolicy := Proofs.ZDEXBuybackPriceSafetyV1.Policy
abbrev PriceObservation := Proofs.ZDEXBuybackPriceSafetyV1.Observation

def encodeNats : List Nat -> Nat
  | [] => 0
  | value :: rest => Nat.pair value (encodeNats rest) + 1

theorem encodeNats_injective : Function.Injective encodeNats := by
  intro left
  induction left with
  | nil =>
      intro right hEqual
      cases right with
      | nil => rfl
      | cons value rest => simp [encodeNats] at hEqual
  | cons value rest ih =>
      intro right hEqual
      cases right with
      | nil => simp [encodeNats] at hEqual
      | cons otherValue otherRest =>
          simp only [encodeNats] at hEqual
          have hPairEqual :
              Nat.pair value (encodeNats rest) =
                Nat.pair otherValue (encodeNats otherRest) := by omega
          have hPair := Nat.pair_eq_pair.mp hPairEqual
          have hRest : rest = otherRest := ih hPair.2
          simp [hPair.1, hRest]

def maxReserveAtoms : Nat := 3_000_000_000
def maxSwapAtoms : Nat := 3_000_000_000
def maxPoolCount : Nat := 64
def maxU64 : Nat := 2 ^ 64 - 1
def maxU128 : Nat := 2 ^ 128 - 1
def maxI127 : Nat := 2 ^ 127 - 1

def approvedSpotModuleReleaseId : ReleaseId := 1_001
def approvedTokenomicsModuleReleaseId : ReleaseId := 1_002
def approvedRouteReleaseId : ReleaseId := 2_001

inductive CurveRelease where
  | cpmmV8ExactIn
  | registeredOther (releaseId : ReleaseId)
  deriving DecidableEq, Repr

inductive CurveReleaseStatus where
  | activeNew
  | drainOnly
  | verifyOnly
  | retired
  | revoked
  deriving DecidableEq, Repr

structure RegisteredCurveRelease where
  releaseId : ReleaseId
  status : CurveReleaseStatus
  deriving DecidableEq, Repr

inductive PoolStatus where
  | active
  | frozen
  | disabled
  deriving DecidableEq, Repr

def poolStatusCode : PoolStatus -> Nat
  | .active => 1
  | .frozen => 2
  | .disabled => 3

theorem poolStatusCode_injective : Function.Injective poolStatusCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [poolStatusCode]

inductive LaneId where
  | spotLiquidity
  deriving DecidableEq, Repr

def laneIdCode : LaneId -> Nat
  | .spotLiquidity => 1

def curveReleaseCode : CurveRelease -> Nat
  | .cpmmV8ExactIn => 1
  | .registeredOther releaseId => releaseId + 2

theorem curveReleaseCode_injective : Function.Injective curveReleaseCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [curveReleaseCode]

def curveReleaseStatusCode : CurveReleaseStatus -> Nat
  | .activeNew => 1
  | .drainOnly => 2
  | .verifyOnly => 3
  | .retired => 4
  | .revoked => 5

theorem curveReleaseStatusCode_injective :
    Function.Injective curveReleaseStatusCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [curveReleaseStatusCode]

def registeredCurveReleaseCommitment (release : RegisteredCurveRelease) : Nat :=
  encodeNats [release.releaseId, curveReleaseStatusCode release.status]

theorem registeredCurveReleaseCommitment_injective :
    Function.Injective registeredCurveReleaseCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  cases left
  cases right
  simp_all [curveReleaseStatusCode_injective.eq_iff]

def registeredSiblingCurveAvailable
    (registry : List RegisteredCurveRelease) (releaseId : ReleaseId) : Bool :=
  registry.any fun registered =>
    decide (registered.releaseId = releaseId ∧
      (registered.status = .activeNew ∨ registered.status = .drainOnly))

/-- Immutable pool definition. A zero parameter root is the canonical empty
parameter set for CPMM v8. -/
structure PoolDefinition where
  asset0 : AssetId
  asset1 : AssetId
  feeBps : Nat
  curveRelease : CurveRelease
  curveParamsRoot : Root
  reserve0Principal : PrincipalId
  reserve1Principal : PrincipalId
  deriving DecidableEq, Repr

/-- Injective mathematical encoding used as the formal pool identifier.
Runtime cryptographic identifiers still require an exact-byte refinement and
collision-resistance premise. -/
def derivePoolId (definition : PoolDefinition) : PoolId :=
  Nat.pair definition.asset0 <|
    Nat.pair definition.asset1 <|
      Nat.pair definition.feeBps <|
        Nat.pair (curveReleaseCode definition.curveRelease) <|
          Nat.pair definition.curveParamsRoot <|
            Nat.pair definition.reserve0Principal definition.reserve1Principal

theorem derivePoolId_injective : Function.Injective derivePoolId := by
  intro left right hEqual
  rcases left with ⟨leftAsset0, leftAsset1, leftFee, leftCurve, leftParams,
    leftReserve0, leftReserve1⟩
  rcases right with ⟨rightAsset0, rightAsset1, rightFee, rightCurve, rightParams,
    rightReserve0, rightReserve1⟩
  cases leftCurve <;> cases rightCurve <;>
    simp [derivePoolId, curveReleaseCode, Nat.pair_eq_pair] at hEqual <;>
    simp_all

structure Pool where
  poolId : PoolId
  definition : PoolDefinition
  reserve0Atoms : Nat
  reserve1Atoms : Nat
  lpSupplyAtoms : Nat
  status : PoolStatus
  creationReleaseId : ReleaseId
  createdHeight : Nat
  deriving DecidableEq, Repr

structure SpotLaneState where
  pools : List Pool
  lpOwnershipRoot : Root
  routeBatchRoot : Root
  feeResidueRoot : Root
  poolTerminalObligationsRoot : Root
  deriving DecidableEq, Repr

def poolCommitment (pool : Pool) : Nat :=
  encodeNats [
    pool.poolId,
    derivePoolId pool.definition,
    pool.reserve0Atoms,
    pool.reserve1Atoms,
    pool.lpSupplyAtoms,
    poolStatusCode pool.status,
    pool.creationReleaseId,
    pool.createdHeight
  ]

def poolRegistryCommitment (pools : List Pool) : Nat :=
  encodeNats (pools.map poolCommitment)

def spotLaneStateCommitment (state : SpotLaneState) : Root :=
  encodeNats [
    poolRegistryCommitment state.pools,
    state.lpOwnershipRoot,
    state.routeBatchRoot,
    state.feeResidueRoot,
    state.poolTerminalObligationsRoot
  ]

theorem poolCommitment_injective : Function.Injective poolCommitment := by
  rintro ⟨leftId, leftDefinition, leftReserve0, leftReserve1, leftLP,
    leftStatus, leftRelease, leftHeight⟩
    ⟨rightId, rightDefinition, rightReserve0, rightReserve1, rightLP,
      rightStatus, rightRelease, rightHeight⟩ hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with
    ⟨hId, hDefinitionCode, hReserve0, hReserve1, hLP, hStatusCode,
      hRelease, hHeight⟩
  have hDefinition := derivePoolId_injective hDefinitionCode
  have hStatus := poolStatusCode_injective hStatusCode
  subst rightId
  subst rightDefinition
  subst rightReserve0
  subst rightReserve1
  subst rightLP
  subst rightStatus
  subst rightRelease
  subst rightHeight
  rfl

theorem poolRegistryCommitment_injective :
    Function.Injective poolRegistryCommitment := by
  intro left right hEqual
  have hMapped := encodeNats_injective hEqual
  exact (List.map_injective_iff.mpr poolCommitment_injective) hMapped

theorem spotLaneStateCommitment_injective :
    Function.Injective spotLaneStateCommitment := by
  rintro ⟨leftPools, leftLP, leftRoutes, leftFees, leftTerminal⟩
    ⟨rightPools, rightLP, rightRoutes, rightFees, rightTerminal⟩ hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hPoolsCode, hLP, hRoutes, hFees, hTerminal⟩
  have hPools := poolRegistryCommitment_injective hPoolsCode
  subst rightPools
  subst rightLP
  subst rightRoutes
  subst rightFees
  subst rightTerminal
  rfl

/-- Exact release envelope for this bounded formal checkpoint. Supporting a
nonzero protocol fee share requires another typed output port and receiver. -/
structure SpotBuybackRelease where
  moduleReleaseId : ReleaseId
  routeReleaseId : ReleaseId
  curveRelease : CurveRelease
  protocolFeeShareBps : Nat
  reserveCapAtoms : Nat
  swapCapAtoms : Nat
  poolCountCap : Nat
  registeredSiblingCurveReleases : List RegisteredCurveRelease
  deriving DecidableEq, Repr

def approvedRelease : SpotBuybackRelease where
  moduleReleaseId := approvedSpotModuleReleaseId
  routeReleaseId := approvedRouteReleaseId
  curveRelease := .cpmmV8ExactIn
  protocolFeeShareBps := 0
  reserveCapAtoms := maxReserveAtoms
  swapCapAtoms := maxSwapAtoms
  poolCountCap := maxPoolCount
  registeredSiblingCurveReleases := [⟨8_001, .drainOnly⟩]

theorem approved_protocol_fee_share_is_zero :
    approvedRelease.protocolFeeShareBps = 0 := rfl

structure ExecutionPolicy where
  selectedPoolId : PoolId
  expectedDefinition : PoolDefinition
  quoteAsset : AssetId
  zdexAsset : AssetId
  quoteSourcePrincipal : PrincipalId
  zdexDestinationPrincipal : PrincipalId
  deriving DecidableEq, Repr

def executionPolicyCommitment (policy : ExecutionPolicy) : Root :=
  encodeNats [
    policy.selectedPoolId,
    derivePoolId policy.expectedDefinition,
    policy.quoteAsset,
    policy.zdexAsset,
    policy.quoteSourcePrincipal,
    policy.zdexDestinationPrincipal
  ]

theorem executionPolicyCommitment_injective :
    Function.Injective executionPolicyCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  cases left
  cases right
  simp_all [derivePoolId_injective.eq_iff]

def pricePolicyCommitment (authorizedOracleProviderId : Nat) (policy : PricePolicy) : Root :=
  encodeNats [
    authorizedOracleProviderId,
    policy.maximumOracleAgeBlocks,
    policy.minimumQuoteReserve,
    policy.minimumZdexReserve,
    policy.maximumPoolOracleDeviationBps,
    policy.maximumExecutionImpactBps,
    policy.maximumOracleExecutionDeviationBps,
    policy.maximumQuoteReserveSpendBps
  ]

theorem pricePolicyCommitment_no_alias
    {leftProvider rightProvider : Nat} {leftPolicy rightPolicy : PricePolicy}
    (hEqual : pricePolicyCommitment leftProvider leftPolicy =
      pricePolicyCommitment rightProvider rightPolicy) :
    leftProvider = rightProvider ∧ leftPolicy = rightPolicy := by
  have hFields := encodeNats_injective hEqual
  cases leftPolicy
  cases rightPolicy
  simp_all

def releaseCommitment (release : SpotBuybackRelease) : Root :=
  encodeNats [
    release.moduleReleaseId,
    release.routeReleaseId,
    curveReleaseCode release.curveRelease,
    release.protocolFeeShareBps,
    release.reserveCapAtoms,
    release.swapCapAtoms,
    release.poolCountCap,
    encodeNats (release.registeredSiblingCurveReleases.map
      registeredCurveReleaseCommitment)
  ]

theorem releaseCommitment_injective : Function.Injective releaseCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with
    ⟨hModule, hRoute, hCurve, hProtocolFee, hReserveCap, hSwapCap,
      hPoolCap, hRegistryCode⟩
  have hCurveRelease := curveReleaseCode_injective hCurve
  have hRegistryMap := encodeNats_injective hRegistryCode
  have hRegistry :=
    (List.map_injective_iff.mpr registeredCurveReleaseCommitment_injective)
      hRegistryMap
  cases left
  cases right
  simp_all

structure ProfileAuthorization where
  profileId : Root
  chainId : Nat
  deploymentId : Nat
  routeReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  authorizedOracleProviderId : Nat
  spotReleaseCommitment : Root
  executionPolicyCommitment : Root
  pricePolicyCommitment : Root
  deriving DecidableEq, Repr

def deriveProfileId (authorization : ProfileAuthorization) : Root :=
  encodeNats [
    authorization.chainId,
    authorization.deploymentId,
    authorization.routeReleaseId,
    authorization.spotModuleReleaseId,
    authorization.tokenomicsModuleReleaseId,
    authorization.authorizedOracleProviderId,
    authorization.spotReleaseCommitment,
    authorization.executionPolicyCommitment,
    authorization.pricePolicyCommitment
  ]

def ProfileAuthorizationSelfConsistent (authorization : ProfileAuthorization) : Prop :=
  authorization.profileId = deriveProfileId authorization

theorem self_consistent_profile_id_no_alias
    {left right : ProfileAuthorization}
    (hLeft : ProfileAuthorizationSelfConsistent left)
    (hRight : ProfileAuthorizationSelfConsistent right)
    (hProfileId : left.profileId = right.profileId) :
    left = right := by
  have hDerived : deriveProfileId left = deriveProfileId right := by
    exact hLeft.symm.trans (hProfileId.trans hRight)
  have hFields := encodeNats_injective hDerived
  simp only [List.cons.injEq, and_true] at hFields
  rcases left with
    ⟨leftProfile, leftChain, leftDeployment, leftRoute, leftSpot,
      leftTokenomics, leftOracle, leftRelease, leftExecution, leftPrice⟩
  rcases right with
    ⟨rightProfile, rightChain, rightDeployment, rightRoute, rightSpot,
      rightTokenomics, rightOracle, rightRelease, rightExecution, rightPrice⟩
  rcases hFields with
    ⟨hChain, hDeployment, hRoute, hSpot, hTokenomics, hOracle,
      hRelease, hExecution, hPrice⟩
  change leftProfile = rightProfile at hProfileId
  change leftChain = rightChain at hChain
  change leftDeployment = rightDeployment at hDeployment
  change leftRoute = rightRoute at hRoute
  change leftSpot = rightSpot at hSpot
  change leftTokenomics = rightTokenomics at hTokenomics
  change leftOracle = rightOracle at hOracle
  change leftRelease = rightRelease at hRelease
  change leftExecution = rightExecution at hExecution
  change leftPrice = rightPrice at hPrice
  subst rightProfile
  subst rightChain
  subst rightDeployment
  subst rightRoute
  subst rightSpot
  subst rightTokenomics
  subst rightOracle
  subst rightRelease
  subst rightExecution
  subst rightPrice
  rfl

def makeProfileAuthorization
    (chainId deploymentId : Nat)
    (routeReleaseId spotModuleReleaseId tokenomicsModuleReleaseId : ReleaseId)
    (authorizedOracleProviderId : Nat)
    (release : SpotBuybackRelease)
    (policy : ExecutionPolicy)
    (pricePolicy : PricePolicy) : ProfileAuthorization :=
  let unsigned : ProfileAuthorization := {
    profileId := 0
    chainId := chainId
    deploymentId := deploymentId
    routeReleaseId := routeReleaseId
    spotModuleReleaseId := spotModuleReleaseId
    tokenomicsModuleReleaseId := tokenomicsModuleReleaseId
    authorizedOracleProviderId := authorizedOracleProviderId
    spotReleaseCommitment := releaseCommitment release
    executionPolicyCommitment := executionPolicyCommitment policy
    pricePolicyCommitment := pricePolicyCommitment authorizedOracleProviderId pricePolicy
  }
  { unsigned with profileId := deriveProfileId unsigned }

inductive OracleStatus where
  | pending
  | final
  | disputed
  deriving DecidableEq, Repr

structure OracleOccurrence where
  oracleProviderId : Nat
  quoteAsset : AssetId
  zdexAsset : AssetId
  quoteNumerator : Nat
  zdexDenominator : Nat
  observedHeight : Nat
  finalityRoot : Root
  status : OracleStatus
  deriving DecidableEq, Repr

def oracleStatusCode : OracleStatus -> Nat
  | .pending => 1
  | .final => 2
  | .disputed => 3

theorem oracleStatusCode_injective : Function.Injective oracleStatusCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [oracleStatusCode]

def deriveOracleOccurrenceId
    (chainId deploymentId : Nat) (occurrence : OracleOccurrence) : OccurrenceId :=
  encodeNats [
    chainId,
    deploymentId,
    occurrence.oracleProviderId,
    occurrence.quoteAsset,
    occurrence.zdexAsset,
    occurrence.quoteNumerator,
    occurrence.zdexDenominator,
    occurrence.observedHeight,
    occurrence.finalityRoot,
    oracleStatusCode occurrence.status
  ]

theorem deriveOracleOccurrenceId_injective (chainId deploymentId : Nat) :
    Function.Injective (deriveOracleOccurrenceId chainId deploymentId) := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  cases left
  cases right
  simp_all [oracleStatusCode_injective.eq_iff]

structure OracleRegistrySnapshot where
  occurrences : List OracleOccurrence
  deriving DecidableEq, Repr

def oracleOccurrenceIds
    (chainId deploymentId : Nat) (snapshot : OracleRegistrySnapshot) : List OccurrenceId :=
  snapshot.occurrences.map (deriveOracleOccurrenceId chainId deploymentId)

def oracleRegistryCommitment
    (chainId deploymentId : Nat) (snapshot : OracleRegistrySnapshot) : Root :=
  encodeNats [chainId, deploymentId,
    encodeNats (oracleOccurrenceIds chainId deploymentId snapshot)]

theorem oracleRegistryCommitment_injective (chainId deploymentId : Nat) :
    Function.Injective (oracleRegistryCommitment chainId deploymentId) := by
  intro left right hEqual
  have hOuter := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hOuter
  have hIds := encodeNats_injective hOuter.2.2
  have hOccurrences :=
    (List.map_injective_iff.mpr
      (deriveOracleOccurrenceId_injective chainId deploymentId)) hIds
  cases left
  cases right
  simp_all

def OracleRegistryCanonical
    (chainId deploymentId authorizedOracleProviderId : Nat)
    (snapshot : OracleRegistrySnapshot) : Prop :=
  (oracleOccurrenceIds chainId deploymentId snapshot).SortedLT ∧
    0 < snapshot.occurrences.length ∧
    ∀ occurrence ∈ snapshot.occurrences,
      occurrence.oracleProviderId = authorizedOracleProviderId ∧
        occurrence.status = .final

/-- Values supplied by the release-aware verifier. Exact runtime authority
requires an opaque verifier witness refining this explicit formal context. -/
structure AuthorityContext where
  chainId : Nat
  deploymentId : Nat
  currentProfileRoot : Root
  currentRouteReleaseId : ReleaseId
  occurrenceId : OccurrenceId
  currentPreStateRoot : Root
  writerEpoch : Nat
  currentHeight : Nat
  currentSpotModuleReleaseId : ReleaseId
  currentTokenomicsModuleReleaseId : ReleaseId
  authorizedOracleProviderId : Nat
  oracleOccurrenceId : OccurrenceId
  oracleFinalityRoot : Root
  currentOracleRegistryRoot : Root
  oracleRegistry : OracleRegistrySnapshot
  release : SpotBuybackRelease
  policy : ExecutionPolicy
  pricePolicy : PricePolicy
  profileAuthorization : ProfileAuthorization
  oracleOccurrence : OracleOccurrence
  deriving DecidableEq, Repr

/-- The quote amount is selected by the tokenomics leaf and paired by the
route. It is not caller-provided balance authority. -/
structure QuoteInputPort where
  profileRoot : Root
  routeReleaseId : ReleaseId
  occurrenceId : OccurrenceId
  preStateRoot : Root
  sourceModuleReleaseId : ReleaseId
  destinationModuleReleaseId : ReleaseId
  sourcePreStateRoot : Root
  sourcePostStateRoot : Root
  sourceEffectPlanRoot : Root
  sourceJournalRoot : Root
  sourceReceiptBindingRoot : Root
  amountAtoms : Nat
  deriving DecidableEq, Repr

/-- Subject-bound Oracle evidence. The envelope does not carry purchased ZDEX;
the Spot transition derives it. -/
structure PriceEnvelope where
  profileRoot : Root
  routeReleaseId : ReleaseId
  occurrenceId : OccurrenceId
  preStateRoot : Root
  selectedPoolId : PoolId
  oracleOccurrenceId : OccurrenceId
  oracleFinalityRoot : Root
  quoteAmountAtoms : Nat
  currentHeight : Nat
  oracleObservedHeight : Nat
  oracleQuoteNumerator : Nat
  oracleQuoteDenominator : Nat
  claimedRouteSafeQuoteLimitAtoms : Nat
  minimumOutputAtoms : Nat
  deriving DecidableEq, Repr

/-- Untrusted selection witness. Admission checks reconstruct the exact
canonical pre-state registry around the selected row. -/
structure PoolSelection where
  before : List Pool
  selected : Pool
  after : List Pool
  deriving DecidableEq, Repr

structure Input where
  authority : AuthorityContext
  preState : SpotLaneState
  quotePort : QuoteInputPort
  priceEnvelope : PriceEnvelope
  selection : PoolSelection
  deriving DecidableEq, Repr

def withExecutionPolicy (input : Input) (policy : ExecutionPolicy) : Input :=
  let authorization := makeProfileAuthorization
    input.authority.chainId
    input.authority.deploymentId
    input.authority.currentRouteReleaseId
    input.authority.currentSpotModuleReleaseId
    input.authority.currentTokenomicsModuleReleaseId
    input.authority.authorizedOracleProviderId
    input.authority.release
    policy
    input.authority.pricePolicy
  { input with
    authority :=
      { input.authority with
        currentProfileRoot := authorization.profileId
        policy := policy
        profileAuthorization := authorization }
    quotePort := { input.quotePort with profileRoot := authorization.profileId }
    priceEnvelope :=
      { input.priceEnvelope with profileRoot := authorization.profileId } }

def withPreStateAndSelection
    (input : Input) (preState : SpotLaneState) (selection : PoolSelection) : Input :=
  let preStateRoot := spotLaneStateCommitment preState
  { input with
    authority := { input.authority with currentPreStateRoot := preStateRoot }
    preState := preState
    quotePort := { input.quotePort with preStateRoot := preStateRoot }
    priceEnvelope := { input.priceEnvelope with preStateRoot := preStateRoot }
    selection := selection }

def withOracleOccurrence
    (input : Input) (occurrence : OracleOccurrence) : Input :=
  let occurrenceId := deriveOracleOccurrenceId
    input.authority.chainId input.authority.deploymentId occurrence
  let oracleRegistry : OracleRegistrySnapshot := { occurrences := [occurrence] }
  { input with
    authority :=
      { input.authority with
        oracleOccurrenceId := occurrenceId
        oracleFinalityRoot := occurrence.finalityRoot
        currentOracleRegistryRoot := oracleRegistryCommitment
          input.authority.chainId input.authority.deploymentId oracleRegistry
        oracleRegistry := oracleRegistry
        oracleOccurrence := occurrence }
    priceEnvelope :=
      { input.priceEnvelope with
        oracleOccurrenceId := occurrenceId
        oracleFinalityRoot := occurrence.finalityRoot
        oracleObservedHeight := occurrence.observedHeight
        oracleQuoteNumerator := occurrence.quoteNumerator
        oracleQuoteDenominator := occurrence.zdexDenominator } }

def withPricePolicy (input : Input) (pricePolicy : PricePolicy) : Input :=
  let authorization := makeProfileAuthorization
    input.authority.chainId
    input.authority.deploymentId
    input.authority.currentRouteReleaseId
    input.authority.currentSpotModuleReleaseId
    input.authority.currentTokenomicsModuleReleaseId
    input.authority.authorizedOracleProviderId
    input.authority.release
    input.authority.policy
    pricePolicy
  { input with
    authority :=
      { input.authority with
        currentProfileRoot := authorization.profileId
        pricePolicy := pricePolicy
        profileAuthorization := authorization }
    quotePort := { input.quotePort with profileRoot := authorization.profileId }
    priceEnvelope :=
      { input.priceEnvelope with profileRoot := authorization.profileId } }

def ceilDiv (numerator denominator : Nat) : Nat :=
  (numerator + denominator - 1) / denominator

def computeFee (gross feeBps : Nat) : Nat :=
  ceilDiv (gross * feeBps) 10_000

def feeTotal (input : Input) : Nat :=
  computeFee input.quotePort.amountAtoms input.selection.selected.definition.feeBps

def netIn (input : Input) : Nat :=
  input.quotePort.amountAtoms - feeTotal input

def swapOutput (reserveIn reserveOut net : Nat) : Nat :=
  reserveOut * net / (reserveIn + net)

def purchasedZDEX (input : Input) : Nat :=
  swapOutput input.selection.selected.reserve0Atoms
    input.selection.selected.reserve1Atoms (netIn input)

def priceObservation (input : Input) : PriceObservation where
  currentHeight := input.priceEnvelope.currentHeight
  oracleObservedHeight := input.priceEnvelope.oracleObservedHeight
  oracleQuoteNumerator := input.priceEnvelope.oracleQuoteNumerator
  oracleZdexDenominator := input.priceEnvelope.oracleQuoteDenominator
  quoteReserve := input.selection.selected.reserve0Atoms
  zdexReserve := input.selection.selected.reserve1Atoms
  quoteAmountIn := input.quotePort.amountAtoms
  purchasedZdex := purchasedZDEX input
  claimedRouteSafeQuoteLimit := input.priceEnvelope.claimedRouteSafeQuoteLimitAtoms
  claimedMinimumOutput := input.priceEnvelope.minimumOutputAtoms

def governedMinimumOutput (input : Input) : Nat :=
  Proofs.ZDEXBuybackPriceSafetyV1.oracleMinimumOutput
    input.authority.pricePolicy (priceObservation input)

def PriceSafe (input : Input) : Prop :=
  let policy := input.authority.pricePolicy
  let observation := priceObservation input
  (policy.maximumPoolOracleDeviationBps <
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints ∧
    policy.maximumExecutionImpactBps <
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints ∧
    policy.maximumOracleExecutionDeviationBps <
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints) ∧
  (0 < policy.maximumQuoteReserveSpendBps ∧
    policy.maximumQuoteReserveSpendBps ≤
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints) ∧
  (0 < observation.oracleQuoteNumerator ∧
    0 < observation.oracleZdexDenominator) ∧
  observation.oracleObservedHeight ≤ observation.currentHeight ∧
  observation.currentHeight - observation.oracleObservedHeight ≤
    policy.maximumOracleAgeBlocks ∧
  (policy.minimumQuoteReserve ≤ observation.quoteReserve ∧
    policy.minimumZdexReserve ≤ observation.zdexReserve) ∧
  observation.purchasedZdex ≤ observation.zdexReserve ∧
  observation.claimedRouteSafeQuoteLimit =
    Proofs.ZDEXBuybackPriceSafetyV1.routeSafeQuoteLimit policy observation ∧
  0 < observation.claimedRouteSafeQuoteLimit ∧
  observation.quoteAmountIn ≤ observation.claimedRouteSafeQuoteLimit ∧
  observation.claimedMinimumOutput =
    Proofs.ZDEXBuybackPriceSafetyV1.oracleMinimumOutput policy observation ∧
  observation.claimedMinimumOutput ≤ observation.purchasedZdex ∧
  Proofs.ZDEXBuybackPriceSafetyV1.absoluteDifference
        (observation.quoteReserve * observation.oracleZdexDenominator)
        (observation.zdexReserve * observation.oracleQuoteNumerator) *
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints ≤
    observation.zdexReserve * observation.oracleQuoteNumerator *
      policy.maximumPoolOracleDeviationBps ∧
  observation.quoteAmountIn * observation.zdexReserve *
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints ≤
    observation.purchasedZdex * observation.quoteReserve *
      (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
        policy.maximumExecutionImpactBps) ∧
  observation.quoteAmountIn * observation.oracleZdexDenominator *
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints ≤
    observation.purchasedZdex * observation.oracleQuoteNumerator *
      (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
        policy.maximumOracleExecutionDeviationBps)

def FitsU64 (value : Nat) : Prop := value ≤ maxU64
def FitsU128 (value : Nat) : Prop := value ≤ maxU128
def FitsI127Magnitude (value : Nat) : Prop := value ≤ maxI127

/-- Every intermediate used by the executable CPMM, fee, route-limit, and
price-envelope arithmetic must fit the declared machine domain. The formal
model still calculates in `Nat`; this predicate is the refinement boundary
that prevents an unbounded proof from authorizing an overflowing runtime. -/
def PriceArithmeticFits (input : Input) : Prop :=
  let policy := input.authority.pricePolicy
  let observation := priceObservation input
  FitsU64 input.authority.writerEpoch ∧
  FitsU64 input.authority.currentHeight ∧
  FitsU64 input.authority.oracleOccurrence.observedHeight ∧
  FitsU128 observation.oracleQuoteNumerator ∧
  FitsU128 observation.oracleZdexDenominator ∧
  FitsI127Magnitude input.quotePort.amountAtoms ∧
  FitsI127Magnitude (purchasedZDEX input) ∧
  FitsU128 (input.quotePort.amountAtoms *
    input.selection.selected.definition.feeBps) ∧
  FitsU128 (input.quotePort.amountAtoms *
    input.selection.selected.definition.feeBps + 9_999) ∧
  FitsU128 (input.selection.selected.reserve0Atoms + netIn input) ∧
  FitsU128 (input.selection.selected.reserve1Atoms * netIn input) ∧
  FitsU128 (observation.quoteReserve * policy.maximumQuoteReserveSpendBps) ∧
  FitsU128 (observation.quoteAmountIn * observation.oracleZdexDenominator) ∧
  FitsU128 (observation.quoteAmountIn * observation.oracleZdexDenominator *
    Proofs.ZDEXBuybackPriceSafetyV1.basisPoints) ∧
  FitsU128 (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
    policy.maximumExecutionImpactBps) ∧
  FitsU128 (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
    policy.maximumOracleExecutionDeviationBps) ∧
  FitsU128 (observation.oracleQuoteNumerator *
    (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
      policy.maximumOracleExecutionDeviationBps)) ∧
  FitsU128 (observation.quoteReserve * observation.oracleZdexDenominator) ∧
  FitsU128 (observation.zdexReserve * observation.oracleQuoteNumerator) ∧
  FitsU128 (Proofs.ZDEXBuybackPriceSafetyV1.absoluteDifference
    (observation.quoteReserve * observation.oracleZdexDenominator)
    (observation.zdexReserve * observation.oracleQuoteNumerator) *
      Proofs.ZDEXBuybackPriceSafetyV1.basisPoints) ∧
  FitsU128 (observation.zdexReserve * observation.oracleQuoteNumerator *
    policy.maximumPoolOracleDeviationBps) ∧
  FitsU128 (observation.quoteAmountIn * observation.zdexReserve *
    Proofs.ZDEXBuybackPriceSafetyV1.basisPoints) ∧
  FitsU128 (observation.purchasedZdex * observation.quoteReserve *
    (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
      policy.maximumExecutionImpactBps)) ∧
  FitsU128 (observation.purchasedZdex * observation.oracleQuoteNumerator *
    (Proofs.ZDEXBuybackPriceSafetyV1.basisPoints +
      policy.maximumOracleExecutionDeviationBps))

theorem priceSafe_iff_existing_contract (input : Input) :
    PriceSafe input ↔
      Proofs.ZDEXBuybackPriceSafetyV1.Accepted
        input.authority.pricePolicy (priceObservation input) := by
  constructor
  · rintro ⟨hPolicyDeviation, hPolicySpend, hRatios, hHeight, hFresh,
      hDepth, hReserve, hRoute, hPositiveRoute, hSpend, hMinimum,
      hRealized, hPoolOracle, hImpact, hOracleExecution⟩
    exact {
      policyDeviationBounds := hPolicyDeviation
      policySpendBounds := hPolicySpend
      positiveRatios := hRatios
      heightMonotone := hHeight
      oracleFresh := hFresh
      sufficientDepth := hDepth
      outputWithinReserve := hReserve
      exactRouteLimit := hRoute
      positiveRouteLimit := hPositiveRoute
      spendWithinRouteLimit := hSpend
      exactMinimumOutput := hMinimum
      realizedMinimumOutput := hRealized
      poolOracleEnvelope := hPoolOracle
      executionImpactEnvelope := hImpact
      oracleExecutionEnvelope := hOracleExecution
    }
  · intro hAccepted
    exact ⟨hAccepted.policyDeviationBounds, hAccepted.policySpendBounds,
      hAccepted.positiveRatios, hAccepted.heightMonotone, hAccepted.oracleFresh,
      hAccepted.sufficientDepth, hAccepted.outputWithinReserve,
      hAccepted.exactRouteLimit, hAccepted.positiveRouteLimit,
      hAccepted.spendWithinRouteLimit, hAccepted.exactMinimumOutput,
      hAccepted.realizedMinimumOutput, hAccepted.poolOracleEnvelope,
      hAccepted.executionImpactEnvelope, hAccepted.oracleExecutionEnvelope⟩

def PoolStaticWellFormed (release : SpotBuybackRelease) (pool : Pool) : Prop :=
  pool.poolId = derivePoolId pool.definition ∧
    pool.definition.asset0 < pool.definition.asset1 ∧
    pool.definition.feeBps ≤ 10_000 ∧
    0 < pool.definition.reserve0Principal ∧
    0 < pool.definition.reserve1Principal ∧
    pool.definition.reserve0Principal ≠ pool.definition.reserve1Principal ∧
    0 < pool.creationReleaseId ∧
    match pool.definition.curveRelease with
    | .cpmmV8ExactIn => pool.definition.curveParamsRoot = 0
    | .registeredOther releaseId =>
        0 < releaseId ∧
          0 < pool.definition.curveParamsRoot ∧
          registeredSiblingCurveAvailable
            release.registeredSiblingCurveReleases releaseId = true

instance poolStaticWellFormedDecidable
    (release : SpotBuybackRelease) (pool : Pool) :
    Decidable (PoolStaticWellFormed release pool) := by
  unfold PoolStaticWellFormed
  cases pool.definition.curveRelease <;> infer_instance

def PoolBounded (release : SpotBuybackRelease) (pool : Pool) : Prop :=
  pool.reserve0Atoms ≤ release.reserveCapAtoms ∧
    pool.reserve1Atoms ≤ release.reserveCapAtoms ∧
    pool.lpSupplyAtoms ≤ release.reserveCapAtoms ∧
    (pool.status = .active →
      0 < pool.reserve0Atoms ∧ 0 < pool.reserve1Atoms ∧ 0 < pool.lpSupplyAtoms)

def PoolWellFormed (release : SpotBuybackRelease) (pool : Pool) : Prop :=
  PoolStaticWellFormed release pool ∧ PoolBounded release pool

def poolIds (pools : List Pool) : List PoolId := pools.map Pool.poolId

def RegistryCanonical (release : SpotBuybackRelease) (pools : List Pool) : Prop :=
  (poolIds pools).SortedLT ∧
    0 < pools.length ∧
    pools.length ≤ release.poolCountCap ∧
    ∀ pool ∈ pools, PoolWellFormed release pool

def SpotLaneStateWellFormed (release : SpotBuybackRelease) (state : SpotLaneState) : Prop :=
  RegistryCanonical release state.pools ∧
    0 < state.lpOwnershipRoot ∧
    0 < state.routeBatchRoot ∧
    0 < state.feeResidueRoot ∧
    0 < state.poolTerminalObligationsRoot

def lookupPool (poolId : PoolId) : List Pool -> Option Pool
  | [] => none
  | pool :: rest =>
      if pool.poolId = poolId then some pool else lookupPool poolId rest

def updatedSelectedPool (input : Input) : Pool :=
  { input.selection.selected with
    reserve0Atoms := input.selection.selected.reserve0Atoms + input.quotePort.amountAtoms
    reserve1Atoms := input.selection.selected.reserve1Atoms - purchasedZDEX input }

def acceptedPostState (input : Input) : SpotLaneState where
  pools := input.selection.before ++ updatedSelectedPool input :: input.selection.after
  lpOwnershipRoot := input.preState.lpOwnershipRoot
  routeBatchRoot := input.preState.routeBatchRoot
  feeResidueRoot := input.preState.feeResidueRoot
  poolTerminalObligationsRoot := input.preState.poolTerminalObligationsRoot

inductive EffectKind where
  | accountMovement
  deriving DecidableEq, Repr

inductive AccountingDomain where
  | spotPoolReserve
  deriving DecidableEq, Repr

structure CustodyDelta where
  kind : EffectKind
  accountingDomain : AccountingDomain
  asset : AssetId
  principal : PrincipalId
  deltaAtoms : Int
  deriving DecidableEq, Repr

structure LaneWrite where
  lane : LaneId
  preStateRoot : Root
  postStateRoot : Root
  deriving DecidableEq, Repr

structure SpotEffects where
  custodyDeltas : List CustodyDelta
  laneWrites : List LaneWrite
  consumedObjectIds : List Nat
  deriving DecidableEq, Repr

def SpotEffects.empty : SpotEffects where
  custodyDeltas := []
  laneWrites := []
  consumedObjectIds := []

def intCommitment : Int -> Nat
  | .ofNat value => 2 * value
  | .negSucc value => 2 * value + 1

def custodyDeltaCommitment (delta : CustodyDelta) : Nat :=
  encodeNats [
    1,
    1,
    delta.asset,
    delta.principal,
    intCommitment delta.deltaAtoms
  ]

def laneWriteCommitment (write : LaneWrite) : Nat :=
  encodeNats [laneIdCode write.lane, write.preStateRoot, write.postStateRoot]

def spotEffectsCommitment (effects : SpotEffects) : Root :=
  encodeNats [
    encodeNats (effects.custodyDeltas.map custodyDeltaCommitment),
    encodeNats (effects.laneWrites.map laneWriteCommitment),
    encodeNats effects.consumedObjectIds
  ]

def acceptedEffects (input : Input) : SpotEffects where
  custodyDeltas := [
    { kind := .accountMovement
      accountingDomain := .spotPoolReserve
      asset := input.authority.policy.quoteAsset
      principal := input.selection.selected.definition.reserve0Principal
      deltaAtoms := Int.ofNat input.quotePort.amountAtoms },
    { kind := .accountMovement
      accountingDomain := .spotPoolReserve
      asset := input.authority.policy.zdexAsset
      principal := input.selection.selected.definition.reserve1Principal
      deltaAtoms := -Int.ofNat (purchasedZDEX input) }
  ]
  laneWrites := [
    { lane := .spotLiquidity
      preStateRoot := input.authority.currentPreStateRoot
      postStateRoot := spotLaneStateCommitment (acceptedPostState input) }
  ]
  consumedObjectIds := []

inductive PortRole where
  | quoteInput
  | purchasedZDEXOutput
  deriving DecidableEq, Repr

def portRoleCode : PortRole -> Nat
  | .quoteInput => 1
  | .purchasedZDEXOutput => 2

theorem portRoleCode_injective : Function.Injective portRoleCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [portRoleCode]

/-- Exact formal flow subject. Both roles bind the command occurrence, the
Tokenomics source transition, and the derived Spot poststate. -/
structure FlowIdentity where
  role : PortRole
  chainId : Nat
  deploymentId : Nat
  profileId : Root
  writerEpoch : Nat
  commandOccurrenceId : OccurrenceId
  preStateRoot : Root
  postStateRoot : Root
  routeReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotReleaseCommitment : Root
  executionPolicyCommitment : Root
  pricePolicyCommitment : Root
  oracleRegistryRoot : Root
  oracleOccurrenceId : OccurrenceId
  tokenomicsSourcePreStateRoot : Root
  tokenomicsSourcePostStateRoot : Root
  tokenomicsSourceEffectPlanRoot : Root
  tokenomicsSourceJournalRoot : Root
  tokenomicsSourceReceiptBindingRoot : Root
  selectedPoolId : PoolId
  asset : AssetId
  sourcePrincipal : PrincipalId
  destinationPrincipal : PrincipalId
  amountAtoms : Nat
  deriving DecidableEq, Repr

def flowIdentityCommitment (flow : FlowIdentity) : Nat :=
  encodeNats [
    portRoleCode flow.role,
    flow.chainId,
    flow.deploymentId,
    flow.profileId,
    flow.writerEpoch,
    flow.commandOccurrenceId,
    flow.preStateRoot,
    flow.postStateRoot,
    flow.routeReleaseId,
    flow.spotModuleReleaseId,
    flow.tokenomicsModuleReleaseId,
    flow.spotReleaseCommitment,
    flow.executionPolicyCommitment,
    flow.pricePolicyCommitment,
    flow.oracleRegistryRoot,
    flow.oracleOccurrenceId,
    flow.tokenomicsSourcePreStateRoot,
    flow.tokenomicsSourcePostStateRoot,
    flow.tokenomicsSourceEffectPlanRoot,
    flow.tokenomicsSourceJournalRoot,
    flow.tokenomicsSourceReceiptBindingRoot,
    flow.selectedPoolId,
    flow.asset,
    flow.sourcePrincipal,
    flow.destinationPrincipal,
    flow.amountAtoms
  ]

theorem flowIdentityCommitment_injective :
    Function.Injective flowIdentityCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  cases left
  cases right
  simp_all [portRoleCode_injective.eq_iff]

def acceptedQuoteInputFlow (input : Input) : FlowIdentity where
  role := .quoteInput
  chainId := input.authority.chainId
  deploymentId := input.authority.deploymentId
  profileId := input.authority.currentProfileRoot
  writerEpoch := input.authority.writerEpoch
  commandOccurrenceId := input.authority.occurrenceId
  preStateRoot := input.authority.currentPreStateRoot
  postStateRoot := spotLaneStateCommitment (acceptedPostState input)
  routeReleaseId := input.authority.currentRouteReleaseId
  spotModuleReleaseId := input.authority.currentSpotModuleReleaseId
  tokenomicsModuleReleaseId := input.authority.currentTokenomicsModuleReleaseId
  spotReleaseCommitment := releaseCommitment input.authority.release
  executionPolicyCommitment := executionPolicyCommitment input.authority.policy
  pricePolicyCommitment := pricePolicyCommitment
    input.authority.authorizedOracleProviderId input.authority.pricePolicy
  oracleRegistryRoot := input.authority.currentOracleRegistryRoot
  oracleOccurrenceId := input.authority.oracleOccurrenceId
  tokenomicsSourcePreStateRoot := input.quotePort.sourcePreStateRoot
  tokenomicsSourcePostStateRoot := input.quotePort.sourcePostStateRoot
  tokenomicsSourceEffectPlanRoot := input.quotePort.sourceEffectPlanRoot
  tokenomicsSourceJournalRoot := input.quotePort.sourceJournalRoot
  tokenomicsSourceReceiptBindingRoot := input.quotePort.sourceReceiptBindingRoot
  selectedPoolId := input.authority.policy.selectedPoolId
  asset := input.authority.policy.quoteAsset
  sourcePrincipal := input.authority.policy.quoteSourcePrincipal
  destinationPrincipal := input.selection.selected.definition.reserve0Principal
  amountAtoms := input.quotePort.amountAtoms

def acceptedPurchasedOutputFlow (input : Input) : FlowIdentity where
  role := .purchasedZDEXOutput
  chainId := input.authority.chainId
  deploymentId := input.authority.deploymentId
  profileId := input.authority.currentProfileRoot
  writerEpoch := input.authority.writerEpoch
  commandOccurrenceId := input.authority.occurrenceId
  preStateRoot := input.authority.currentPreStateRoot
  postStateRoot := spotLaneStateCommitment (acceptedPostState input)
  routeReleaseId := input.authority.currentRouteReleaseId
  spotModuleReleaseId := input.authority.currentSpotModuleReleaseId
  tokenomicsModuleReleaseId := input.authority.currentTokenomicsModuleReleaseId
  spotReleaseCommitment := releaseCommitment input.authority.release
  executionPolicyCommitment := executionPolicyCommitment input.authority.policy
  pricePolicyCommitment := pricePolicyCommitment
    input.authority.authorizedOracleProviderId input.authority.pricePolicy
  oracleRegistryRoot := input.authority.currentOracleRegistryRoot
  oracleOccurrenceId := input.authority.oracleOccurrenceId
  tokenomicsSourcePreStateRoot := input.quotePort.sourcePreStateRoot
  tokenomicsSourcePostStateRoot := input.quotePort.sourcePostStateRoot
  tokenomicsSourceEffectPlanRoot := input.quotePort.sourceEffectPlanRoot
  tokenomicsSourceJournalRoot := input.quotePort.sourceJournalRoot
  tokenomicsSourceReceiptBindingRoot := input.quotePort.sourceReceiptBindingRoot
  selectedPoolId := input.authority.policy.selectedPoolId
  asset := input.authority.policy.zdexAsset
  sourcePrincipal := input.selection.selected.definition.reserve1Principal
  destinationPrincipal := input.authority.policy.zdexDestinationPrincipal
  amountAtoms := purchasedZDEX input

structure PrivatePorts where
  quoteInput : FlowIdentity
  purchasedOutput : FlowIdentity
  quoteInputFlowId : Nat
  purchasedOutputFlowId : Nat
  deriving DecidableEq, Repr

def FlowIdentity.empty : FlowIdentity where
  role := .quoteInput
  chainId := 0
  deploymentId := 0
  profileId := 0
  writerEpoch := 0
  commandOccurrenceId := 0
  preStateRoot := 0
  postStateRoot := 0
  routeReleaseId := 0
  spotModuleReleaseId := 0
  tokenomicsModuleReleaseId := 0
  spotReleaseCommitment := 0
  executionPolicyCommitment := 0
  pricePolicyCommitment := 0
  oracleRegistryRoot := 0
  oracleOccurrenceId := 0
  tokenomicsSourcePreStateRoot := 0
  tokenomicsSourcePostStateRoot := 0
  tokenomicsSourceEffectPlanRoot := 0
  tokenomicsSourceJournalRoot := 0
  tokenomicsSourceReceiptBindingRoot := 0
  selectedPoolId := 0
  asset := 0
  sourcePrincipal := 0
  destinationPrincipal := 0
  amountAtoms := 0

def PrivatePorts.empty : PrivatePorts where
  quoteInput := FlowIdentity.empty
  purchasedOutput := FlowIdentity.empty
  quoteInputFlowId := 0
  purchasedOutputFlowId := 0

def quoteInputFlowId (input : Input) : Nat :=
  flowIdentityCommitment (acceptedQuoteInputFlow input)

def purchasedOutputFlowId (input : Input) : Nat :=
  flowIdentityCommitment (acceptedPurchasedOutputFlow input)

def acceptedPorts (input : Input) : PrivatePorts where
  quoteInput := acceptedQuoteInputFlow input
  purchasedOutput := acceptedPurchasedOutputFlow input
  quoteInputFlowId := quoteInputFlowId input
  purchasedOutputFlowId := purchasedOutputFlowId input

def privatePortsCommitment (ports : PrivatePorts) : Root :=
  encodeNats [
    flowIdentityCommitment ports.quoteInput,
    flowIdentityCommitment ports.purchasedOutput,
    ports.quoteInputFlowId,
    ports.purchasedOutputFlowId
  ]

inductive TerminalObligationKind where
  | mustBurnPurchasedZDEX
  deriving DecidableEq, Repr

inductive BurnDomain where
  | zdexTokenSupply
  deriving DecidableEq, Repr

def terminalObligationKindCode : TerminalObligationKind -> Nat
  | .mustBurnPurchasedZDEX => 1

def burnDomainCode : BurnDomain -> Nat
  | .zdexTokenSupply => 1

structure TerminalObligation where
  obligationId : Nat
  kind : TerminalObligationKind
  burnDomain : BurnDomain
  chainId : Nat
  deploymentId : Nat
  profileId : Root
  writerEpoch : Nat
  occurrenceId : OccurrenceId
  preStateRoot : Root
  postStateRoot : Root
  routeReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotReleaseCommitment : Root
  executionPolicyCommitment : Root
  pricePolicyCommitment : Root
  oracleRegistryRoot : Root
  oracleOccurrenceId : OccurrenceId
  lane : LaneId
  consumerModuleReleaseId : ReleaseId
  burnAsset : AssetId
  burnPrincipal : PrincipalId
  selectedPoolId : PoolId
  quoteInputFlowId : Nat
  purchasedOutputFlowId : Nat
  purchasedAtoms : Nat
  deriving DecidableEq, Repr

def terminalObligationCommitment (input : Input) : Nat :=
  encodeNats [
    terminalObligationKindCode .mustBurnPurchasedZDEX,
    burnDomainCode .zdexTokenSupply,
    input.authority.chainId,
    input.authority.deploymentId,
    input.authority.currentProfileRoot,
    input.authority.writerEpoch,
    input.authority.occurrenceId,
    input.authority.currentPreStateRoot,
    spotLaneStateCommitment (acceptedPostState input),
    input.authority.currentRouteReleaseId,
    input.authority.currentSpotModuleReleaseId,
    input.authority.currentTokenomicsModuleReleaseId,
    releaseCommitment input.authority.release,
    executionPolicyCommitment input.authority.policy,
    pricePolicyCommitment input.authority.authorizedOracleProviderId
      input.authority.pricePolicy,
    input.authority.currentOracleRegistryRoot,
    input.authority.oracleOccurrenceId,
    laneIdCode .spotLiquidity,
    input.authority.currentTokenomicsModuleReleaseId,
    input.authority.policy.zdexAsset,
    input.authority.policy.zdexDestinationPrincipal,
    input.authority.policy.selectedPoolId,
    quoteInputFlowId input,
    purchasedOutputFlowId input,
    purchasedZDEX input
  ]

def acceptedTerminalObligation (input : Input) : TerminalObligation where
  obligationId := terminalObligationCommitment input + 1
  kind := .mustBurnPurchasedZDEX
  burnDomain := .zdexTokenSupply
  chainId := input.authority.chainId
  deploymentId := input.authority.deploymentId
  profileId := input.authority.currentProfileRoot
  writerEpoch := input.authority.writerEpoch
  occurrenceId := input.authority.occurrenceId
  preStateRoot := input.authority.currentPreStateRoot
  postStateRoot := spotLaneStateCommitment (acceptedPostState input)
  routeReleaseId := input.authority.currentRouteReleaseId
  spotModuleReleaseId := input.authority.currentSpotModuleReleaseId
  tokenomicsModuleReleaseId := input.authority.currentTokenomicsModuleReleaseId
  spotReleaseCommitment := releaseCommitment input.authority.release
  executionPolicyCommitment := executionPolicyCommitment input.authority.policy
  pricePolicyCommitment := pricePolicyCommitment
    input.authority.authorizedOracleProviderId input.authority.pricePolicy
  oracleRegistryRoot := input.authority.currentOracleRegistryRoot
  oracleOccurrenceId := input.authority.oracleOccurrenceId
  lane := .spotLiquidity
  consumerModuleReleaseId := input.authority.currentTokenomicsModuleReleaseId
  burnAsset := input.authority.policy.zdexAsset
  burnPrincipal := input.authority.policy.zdexDestinationPrincipal
  selectedPoolId := input.authority.policy.selectedPoolId
  quoteInputFlowId := quoteInputFlowId input
  purchasedOutputFlowId := purchasedOutputFlowId input
  purchasedAtoms := purchasedZDEX input

def terminalObligationFullCommitment (obligation : TerminalObligation) : Root :=
  encodeNats [
    obligation.obligationId,
    terminalObligationKindCode obligation.kind,
    burnDomainCode obligation.burnDomain,
    obligation.chainId,
    obligation.deploymentId,
    obligation.profileId,
    obligation.writerEpoch,
    obligation.occurrenceId,
    obligation.preStateRoot,
    obligation.postStateRoot,
    obligation.routeReleaseId,
    obligation.spotModuleReleaseId,
    obligation.tokenomicsModuleReleaseId,
    obligation.spotReleaseCommitment,
    obligation.executionPolicyCommitment,
    obligation.pricePolicyCommitment,
    obligation.oracleRegistryRoot,
    obligation.oracleOccurrenceId,
    laneIdCode obligation.lane,
    obligation.consumerModuleReleaseId,
    obligation.burnAsset,
    obligation.burnPrincipal,
    obligation.selectedPoolId,
    obligation.quoteInputFlowId,
    obligation.purchasedOutputFlowId,
    obligation.purchasedAtoms
  ]

theorem terminalObligationFullCommitment_injective :
    Function.Injective terminalObligationFullCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  cases left
  cases right
  simp_all [terminalObligationKindCode, burnDomainCode, laneIdCode]

structure Journal where
  chainId : Nat
  deploymentId : Nat
  profileRoot : Root
  routeReleaseId : ReleaseId
  occurrenceId : OccurrenceId
  writerEpoch : Nat
  preStateRoot : Root
  postStateRoot : Root
  effectPlanRoot : Root
  privatePortsRoot : Root
  spotModuleReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotReleaseCommitment : Root
  executionPolicyCommitment : Root
  pricePolicyCommitment : Root
  oracleRegistryRoot : Root
  oracleOccurrenceId : OccurrenceId
  oracleFinalityRoot : Root
  currentHeight : Nat
  oracleObservedHeight : Nat
  selectedPoolId : PoolId
  poolDefinitionId : PoolId
  poolStatusCode : Nat
  curveReleaseCode : Nat
  curveParamsRoot : Root
  feeBps : Nat
  protocolFeeShareBps : Nat
  quoteAsset : AssetId
  zdexAsset : AssetId
  quoteSourcePrincipal : PrincipalId
  quotePoolPrincipal : PrincipalId
  zdexPoolPrincipal : PrincipalId
  zdexDestinationPrincipal : PrincipalId
  quoteInputAtoms : Nat
  feeAtoms : Nat
  netInputAtoms : Nat
  purchasedZDEXAtoms : Nat
  routeSafeQuoteLimitAtoms : Nat
  minimumOutputAtoms : Nat
  preQuoteReserveAtoms : Nat
  postQuoteReserveAtoms : Nat
  preZDEXReserveAtoms : Nat
  postZDEXReserveAtoms : Nat
  quoteInputFlowId : Nat
  purchasedOutputFlowId : Nat
  terminalObligationCommitment : Root
  terminalObligationId : Nat
  deriving DecidableEq, Repr

def acceptedJournal (input : Input) : Journal where
  chainId := input.authority.chainId
  deploymentId := input.authority.deploymentId
  profileRoot := input.authority.currentProfileRoot
  routeReleaseId := input.authority.currentRouteReleaseId
  occurrenceId := input.authority.occurrenceId
  writerEpoch := input.authority.writerEpoch
  preStateRoot := input.authority.currentPreStateRoot
  postStateRoot := spotLaneStateCommitment (acceptedPostState input)
  effectPlanRoot := spotEffectsCommitment (acceptedEffects input)
  privatePortsRoot := privatePortsCommitment (acceptedPorts input)
  spotModuleReleaseId := input.authority.currentSpotModuleReleaseId
  tokenomicsModuleReleaseId := input.authority.currentTokenomicsModuleReleaseId
  spotReleaseCommitment := releaseCommitment input.authority.release
  executionPolicyCommitment := executionPolicyCommitment input.authority.policy
  pricePolicyCommitment := pricePolicyCommitment
    input.authority.authorizedOracleProviderId input.authority.pricePolicy
  oracleRegistryRoot := input.authority.currentOracleRegistryRoot
  oracleOccurrenceId := input.authority.oracleOccurrenceId
  oracleFinalityRoot := input.authority.oracleFinalityRoot
  currentHeight := input.priceEnvelope.currentHeight
  oracleObservedHeight := input.priceEnvelope.oracleObservedHeight
  selectedPoolId := input.authority.policy.selectedPoolId
  poolDefinitionId := derivePoolId input.selection.selected.definition
  poolStatusCode := poolStatusCode input.selection.selected.status
  curveReleaseCode := curveReleaseCode input.selection.selected.definition.curveRelease
  curveParamsRoot := input.selection.selected.definition.curveParamsRoot
  feeBps := input.selection.selected.definition.feeBps
  protocolFeeShareBps := input.authority.release.protocolFeeShareBps
  quoteAsset := input.authority.policy.quoteAsset
  zdexAsset := input.authority.policy.zdexAsset
  quoteSourcePrincipal := input.authority.policy.quoteSourcePrincipal
  quotePoolPrincipal := input.selection.selected.definition.reserve0Principal
  zdexPoolPrincipal := input.selection.selected.definition.reserve1Principal
  zdexDestinationPrincipal := input.authority.policy.zdexDestinationPrincipal
  quoteInputAtoms := input.quotePort.amountAtoms
  feeAtoms := feeTotal input
  netInputAtoms := netIn input
  purchasedZDEXAtoms := purchasedZDEX input
  routeSafeQuoteLimitAtoms := input.priceEnvelope.claimedRouteSafeQuoteLimitAtoms
  minimumOutputAtoms := input.priceEnvelope.minimumOutputAtoms
  preQuoteReserveAtoms := input.selection.selected.reserve0Atoms
  postQuoteReserveAtoms := (updatedSelectedPool input).reserve0Atoms
  preZDEXReserveAtoms := input.selection.selected.reserve1Atoms
  postZDEXReserveAtoms := (updatedSelectedPool input).reserve1Atoms
  quoteInputFlowId := quoteInputFlowId input
  purchasedOutputFlowId := purchasedOutputFlowId input
  terminalObligationCommitment :=
    terminalObligationFullCommitment (acceptedTerminalObligation input)
  terminalObligationId := (acceptedTerminalObligation input).obligationId

inductive RejectCode where
  | authorityMalformed
  | profileMismatch
  | stateCommitmentMismatch
  | releaseMismatch
  | quotePortMismatch
  | oracleMismatch
  | priceSubjectMismatch
  | policyMismatch
  | laneMalformed
  | selectionMismatch
  | poolInactive
  | amountOutOfRange
  | arithmeticOutOfRange
  | feeConsumesInput
  | zeroOutput
  | minimumOutputMismatch
  | priceUnsafe
  deriving DecidableEq, Repr

def rejectOrder : List RejectCode := [
  .authorityMalformed,
  .releaseMismatch,
  .profileMismatch,
  .stateCommitmentMismatch,
  .quotePortMismatch,
  .oracleMismatch,
  .priceSubjectMismatch,
  .policyMismatch,
  .laneMalformed,
  .selectionMismatch,
  .poolInactive,
  .amountOutOfRange,
  .arithmeticOutOfRange,
  .feeConsumesInput,
  .zeroOutput,
  .minimumOutputMismatch,
  .priceUnsafe
]

def GuardHolds (input : Input) : RejectCode -> Prop
  | .authorityMalformed =>
      0 < input.authority.chainId ∧
        0 < input.authority.deploymentId ∧
        0 < input.authority.currentProfileRoot ∧
        0 < input.authority.currentRouteReleaseId ∧
        0 < input.authority.occurrenceId ∧
        0 < input.authority.currentPreStateRoot ∧
        0 < input.authority.authorizedOracleProviderId ∧
        0 < input.authority.oracleOccurrenceId ∧
        0 < input.authority.oracleFinalityRoot ∧
        0 < input.authority.currentOracleRegistryRoot
  | .profileMismatch =>
      input.authority.profileAuthorization.profileId =
          input.authority.currentProfileRoot ∧
        input.authority.profileAuthorization.profileId =
          deriveProfileId input.authority.profileAuthorization ∧
        input.authority.profileAuthorization.chainId = input.authority.chainId ∧
        input.authority.profileAuthorization.deploymentId = input.authority.deploymentId ∧
        input.authority.profileAuthorization.routeReleaseId =
          input.authority.currentRouteReleaseId ∧
        input.authority.profileAuthorization.spotModuleReleaseId =
          input.authority.currentSpotModuleReleaseId ∧
        input.authority.profileAuthorization.tokenomicsModuleReleaseId =
          input.authority.currentTokenomicsModuleReleaseId ∧
        input.authority.profileAuthorization.authorizedOracleProviderId =
          input.authority.authorizedOracleProviderId ∧
        input.authority.profileAuthorization.spotReleaseCommitment =
          releaseCommitment input.authority.release ∧
        input.authority.profileAuthorization.executionPolicyCommitment =
          executionPolicyCommitment input.authority.policy ∧
        input.authority.profileAuthorization.pricePolicyCommitment =
          pricePolicyCommitment input.authority.authorizedOracleProviderId
            input.authority.pricePolicy
  | .stateCommitmentMismatch =>
      input.authority.currentPreStateRoot = spotLaneStateCommitment input.preState
  | .releaseMismatch =>
      input.authority.release = approvedRelease ∧
        input.authority.currentRouteReleaseId = approvedRouteReleaseId ∧
        input.authority.currentSpotModuleReleaseId = approvedSpotModuleReleaseId ∧
        input.authority.currentTokenomicsModuleReleaseId = approvedTokenomicsModuleReleaseId
  | .quotePortMismatch =>
      input.quotePort.profileRoot = input.authority.currentProfileRoot ∧
        input.quotePort.routeReleaseId = input.authority.currentRouteReleaseId ∧
        input.quotePort.occurrenceId = input.authority.occurrenceId ∧
        input.quotePort.preStateRoot = input.authority.currentPreStateRoot ∧
        input.quotePort.sourceModuleReleaseId = input.authority.currentTokenomicsModuleReleaseId ∧
        input.quotePort.destinationModuleReleaseId = input.authority.currentSpotModuleReleaseId ∧
        0 < input.quotePort.sourcePreStateRoot ∧
        0 < input.quotePort.sourcePostStateRoot ∧
        input.quotePort.sourcePreStateRoot ≠ input.quotePort.sourcePostStateRoot ∧
        0 < input.quotePort.sourceEffectPlanRoot ∧
        0 < input.quotePort.sourceJournalRoot ∧
        0 < input.quotePort.sourceReceiptBindingRoot
  | .oracleMismatch =>
      input.authority.oracleOccurrenceId =
          deriveOracleOccurrenceId input.authority.chainId input.authority.deploymentId
            input.authority.oracleOccurrence ∧
        input.authority.currentOracleRegistryRoot =
          oracleRegistryCommitment input.authority.chainId input.authority.deploymentId
            input.authority.oracleRegistry ∧
        OracleRegistryCanonical input.authority.chainId input.authority.deploymentId
          input.authority.authorizedOracleProviderId input.authority.oracleRegistry ∧
        input.authority.oracleOccurrence ∈ input.authority.oracleRegistry.occurrences ∧
        input.authority.oracleOccurrence.oracleProviderId =
          input.authority.authorizedOracleProviderId ∧
        input.authority.oracleOccurrence.finalityRoot = input.authority.oracleFinalityRoot ∧
        input.authority.oracleOccurrence.status = .final ∧
        input.authority.oracleOccurrence.quoteAsset = input.authority.policy.quoteAsset ∧
        input.authority.oracleOccurrence.zdexAsset = input.authority.policy.zdexAsset
  | .priceSubjectMismatch =>
      input.priceEnvelope.profileRoot = input.authority.currentProfileRoot ∧
        input.priceEnvelope.routeReleaseId = input.authority.currentRouteReleaseId ∧
        input.priceEnvelope.occurrenceId = input.authority.occurrenceId ∧
        input.priceEnvelope.preStateRoot = input.authority.currentPreStateRoot ∧
        input.priceEnvelope.selectedPoolId = input.authority.policy.selectedPoolId ∧
        input.priceEnvelope.oracleOccurrenceId = input.authority.oracleOccurrenceId ∧
        input.priceEnvelope.oracleFinalityRoot = input.authority.oracleFinalityRoot ∧
        input.priceEnvelope.quoteAmountAtoms = input.quotePort.amountAtoms ∧
        input.priceEnvelope.currentHeight = input.authority.currentHeight ∧
        input.priceEnvelope.oracleObservedHeight =
          input.authority.oracleOccurrence.observedHeight ∧
        input.priceEnvelope.oracleQuoteNumerator =
          input.authority.oracleOccurrence.quoteNumerator ∧
        input.priceEnvelope.oracleQuoteDenominator =
          input.authority.oracleOccurrence.zdexDenominator
  | .policyMismatch =>
      input.authority.policy.selectedPoolId =
          derivePoolId input.authority.policy.expectedDefinition ∧
        input.authority.policy.expectedDefinition.asset0 = input.authority.policy.quoteAsset ∧
        input.authority.policy.expectedDefinition.asset1 = input.authority.policy.zdexAsset ∧
        input.authority.policy.quoteAsset < input.authority.policy.zdexAsset ∧
        input.authority.policy.expectedDefinition.curveRelease = .cpmmV8ExactIn ∧
        input.authority.policy.expectedDefinition.curveParamsRoot = 0 ∧
        0 < input.authority.policy.quoteSourcePrincipal ∧
        0 < input.authority.policy.zdexDestinationPrincipal
  | .laneMalformed =>
      SpotLaneStateWellFormed input.authority.release input.preState
  | .selectionMismatch =>
      input.preState.pools =
          input.selection.before ++ input.selection.selected :: input.selection.after ∧
        input.selection.selected.poolId = input.authority.policy.selectedPoolId
  | .poolInactive =>
      input.selection.selected.status = .active
  | .amountOutOfRange =>
      0 < input.quotePort.amountAtoms ∧
        input.quotePort.amountAtoms ≤ input.authority.release.swapCapAtoms ∧
        input.selection.selected.reserve0Atoms + input.quotePort.amountAtoms ≤
          input.authority.release.reserveCapAtoms
  | .arithmeticOutOfRange => PriceArithmeticFits input
  | .feeConsumesInput =>
      feeTotal input < input.quotePort.amountAtoms
  | .zeroOutput =>
      0 < purchasedZDEX input
  | .minimumOutputMismatch =>
      input.priceEnvelope.minimumOutputAtoms = governedMinimumOutput input ∧
        0 < input.priceEnvelope.minimumOutputAtoms ∧
        input.priceEnvelope.minimumOutputAtoms ≤ purchasedZDEX input
  | .priceUnsafe => PriceSafe input

instance guardHoldsDecidable (input : Input) (code : RejectCode) :
    Decidable (GuardHolds input code) := by
  cases code <;>
    simp only [GuardHolds, PriceSafe, PriceArithmeticFits, FitsU64, FitsU128,
      FitsI127Magnitude, OracleRegistryCanonical, SpotLaneStateWellFormed, RegistryCanonical,
      PoolWellFormed, PoolBounded] <;>
    infer_instance

def firstFailing (input : Input) : List RejectCode -> Option RejectCode
  | [] => none
  | code :: rest =>
      if GuardHolds input code then firstFailing input rest else some code

def firstReject (input : Input) : Option RejectCode :=
  firstFailing input rejectOrder

def Valid (input : Input) : Prop :=
  ∀ code ∈ rejectOrder, GuardHolds input code

theorem firstFailing_none_iff (input : Input) :
    ∀ codes, firstFailing input codes = none ↔
      ∀ code ∈ codes, GuardHolds input code
  | [] => by simp [firstFailing]
  | code :: rest => by
      by_cases hGuard : GuardHolds input code
      · simp [firstFailing, hGuard, firstFailing_none_iff input rest]
      · simp [firstFailing, hGuard]

/-- A reported code is the first failed guard in the declared order. -/
theorem firstFailing_some_spec (input : Input) :
    ∀ {codes failed}, firstFailing input codes = some failed →
      ∃ before after,
        codes = before ++ failed :: after ∧
        (∀ code ∈ before, GuardHolds input code) ∧
        ¬GuardHolds input failed
  | [], failed, hFailure => by simp [firstFailing] at hFailure
  | code :: rest, failed, hFailure => by
      by_cases hGuard : GuardHolds input code
      · simp [firstFailing, hGuard] at hFailure
        obtain ⟨before, after, hCodes, hBefore, hFailed⟩ :=
          firstFailing_some_spec input hFailure
        refine ⟨code :: before, after, ?_, ?_, hFailed⟩
        · simp [hCodes]
        · intro candidate hMember
          simp only [List.mem_cons] at hMember
          rcases hMember with rfl | hMember
          · exact hGuard
          · exact hBefore candidate hMember
      · simp [firstFailing, hGuard] at hFailure
        subst failed
        exact ⟨[], rest, rfl, by simp, hGuard⟩

theorem firstReject_none_iff (input : Input) :
    firstReject input = none ↔ Valid input := by
  exact firstFailing_none_iff input rejectOrder

theorem firstReject_some_is_first_failure
    {input : Input} {failed : RejectCode}
    (hFailure : firstReject input = some failed) :
    ∃ before after,
      rejectOrder = before ++ failed :: after ∧
      (∀ code ∈ before, GuardHolds input code) ∧
      ¬GuardHolds input failed :=
  firstFailing_some_spec input hFailure

theorem valid_guard {input : Input} (hValid : Valid input) (code : RejectCode)
    (hMember : code ∈ rejectOrder := by decide) : GuardHolds input code :=
  hValid code hMember

inductive Result where
  | accepted
      (postState : SpotLaneState)
      (effects : SpotEffects)
      (ports : PrivatePorts)
      (journal : Journal)
      (terminalObligation : TerminalObligation)
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

def Result.postState (preState : SpotLaneState) : Result -> SpotLaneState
  | .accepted postState _ _ _ _ => postState
  | .rejected _ => preState

def Result.effects : Result -> SpotEffects
  | .accepted _ effects _ _ _ => effects
  | .rejected _ => SpotEffects.empty

def Result.ports : Result -> PrivatePorts
  | .accepted _ _ ports _ _ => ports
  | .rejected _ => PrivatePorts.empty

def Result.terminalObligation : Result -> Option TerminalObligation
  | .accepted _ _ _ _ obligation => some obligation
  | .rejected _ => none

def transition (input : Input) : Result :=
  match firstReject input with
  | some code => .rejected code
  | none => .accepted
      (acceptedPostState input)
      (acceptedEffects input)
      (acceptedPorts input)
      (acceptedJournal input)
      (acceptedTerminalObligation input)

theorem transition_is_total (input : Input) :
    (∃ post effects ports journal obligation,
      transition input = .accepted post effects ports journal obligation) ∨
      (∃ code, transition input = .rejected code) := by
  unfold transition
  cases hReject : firstReject input with
  | none => exact Or.inl ⟨_, _, _, _, _, rfl⟩
  | some code => exact Or.inr ⟨code, rfl⟩

theorem rejected_is_exact_noop
    (input : Input) (code : RejectCode)
    (hRejected : transition input = .rejected code) :
    (transition input).postState input.preState = input.preState ∧
      (transition input).effects = SpotEffects.empty ∧
      (transition input).ports = PrivatePorts.empty ∧
      (transition input).terminalObligation = none := by
  rw [hRejected]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem accepted_iff
    (input : Input) (post : SpotLaneState) (effects : SpotEffects)
    (ports : PrivatePorts) (journal : Journal) (obligation : TerminalObligation) :
    transition input = .accepted post effects ports journal obligation ↔
      firstReject input = none ∧
      post = acceptedPostState input ∧
      effects = acceptedEffects input ∧
      ports = acceptedPorts input ∧
      journal = acceptedJournal input ∧
      obligation = acceptedTerminalObligation input := by
  unfold transition
  cases hReject : firstReject input with
  | none => simp [eq_comm]
  | some code => simp

theorem accepted_implies_valid
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    Valid input := by
  rw [accepted_iff] at hAccepted
  exact (firstReject_none_iff input).mp hAccepted.1

theorem fee_plus_net_eq_gross {input : Input}
    (hFee : feeTotal input ≤ input.quotePort.amountAtoms) :
    feeTotal input + netIn input = input.quotePort.amountAtoms := by
  unfold netIn
  omega

theorem purchased_zdex_lt_reserve {input : Input}
    (hQuoteReserve : 0 < input.selection.selected.reserve0Atoms)
    (hZDEXReserve : 0 < input.selection.selected.reserve1Atoms)
    (_hNet : 0 < netIn input) :
    purchasedZDEX input < input.selection.selected.reserve1Atoms := by
  simp [purchasedZDEX, swapOutput]
  apply Nat.div_lt_of_lt_mul
  nlinarith

theorem valid_selected_pool_well_formed {input : Input} (hValid : Valid input) :
    PoolWellFormed input.authority.release input.selection.selected := by
  have hRegistry := valid_guard hValid .laneMalformed
  have hSelection := valid_guard hValid .selectionMismatch
  exact hRegistry.1.2.2.2 input.selection.selected <| by
    rw [hSelection.1]
    simp

theorem valid_selected_definition_matches_policy
    {input : Input} (hValid : Valid input) :
    input.selection.selected.definition = input.authority.policy.expectedDefinition := by
  have hPool := valid_selected_pool_well_formed hValid
  have hSelection := valid_guard hValid .selectionMismatch
  have hPolicy := valid_guard hValid .policyMismatch
  apply derivePoolId_injective
  calc
    derivePoolId input.selection.selected.definition = input.selection.selected.poolId :=
      hPool.1.1.symm
    _ = input.authority.policy.selectedPoolId := hSelection.2
    _ = derivePoolId input.authority.policy.expectedDefinition := hPolicy.1

theorem valid_purchased_zdex_lt_reserve
    {input : Input} (hValid : Valid input) :
    purchasedZDEX input < input.selection.selected.reserve1Atoms := by
  have hPool := valid_selected_pool_well_formed hValid
  have hActive := valid_guard hValid .poolInactive
  have hFee := valid_guard hValid .feeConsumesInput
  simp only [GuardHolds] at hActive hFee
  rcases hPool.2 with ⟨_hReserve0Cap, _hReserve1Cap, _hLPSupplyCap, hActivePositive⟩
  have hPositive := hActivePositive hActive
  have hNet : 0 < netIn input := by
    unfold netIn
    omega
  exact purchased_zdex_lt_reserve hPositive.1 hPositive.2.1 hNet

theorem valid_updated_selected_pool_well_formed
    {input : Input} (hValid : Valid input) :
    PoolWellFormed input.authority.release (updatedSelectedPool input) := by
  have hPool := valid_selected_pool_well_formed hValid
  have hActive := valid_guard hValid .poolInactive
  have hAmount := valid_guard hValid .amountOutOfRange
  simp only [GuardHolds] at hActive hAmount
  have hDrain := valid_purchased_zdex_lt_reserve hValid
  rcases hPool with ⟨hStatic, hReserve0Cap, hReserve1Cap, hLPSupplyCap,
    hActivePositive⟩
  have hPositive := hActivePositive hActive
  constructor
  · simpa [updatedSelectedPool] using hStatic
  · refine ⟨hAmount.2.2, ?_, hLPSupplyCap, ?_⟩
    · simp [updatedSelectedPool]
      omega
    · intro _hUpdatedActive
      simp [updatedSelectedPool]
      exact ⟨by omega, by omega, hPositive.2.2⟩

theorem cpmm_k_nondecreasing
    {reserveIn reserveOut gross feeBps : Nat} :
    reserveIn * reserveOut ≤
      (reserveIn + gross) *
        (reserveOut - swapOutput reserveIn reserveOut
          (gross - computeFee gross feeBps)) := by
  let fee := computeFee gross feeBps
  let net := gross - fee
  let denominator := reserveIn + net
  let output := reserveOut * net / denominator
  have hNetLe : net ≤ gross := Nat.sub_le gross fee
  have hDenominatorLe : denominator ≤ reserveIn + gross := by
    dsimp [denominator]
    omega
  have hOutputLe : output ≤ reserveOut := by
    dsimp [output]
    apply Nat.div_le_of_le_mul
    calc
      reserveOut * net ≤ reserveOut * (reserveIn + net) := by
        exact Nat.mul_le_mul_left reserveOut (Nat.le_add_left net reserveIn)
      _ = denominator * reserveOut := by simp [denominator, Nat.mul_comm]
  have hFloor : denominator * output ≤ reserveOut * net := by
    have h := Nat.div_mul_le_self (reserveOut * net) denominator
    simpa [output, Nat.mul_comm] using h
  have hCore : reserveIn * reserveOut ≤ denominator * (reserveOut - output) := by
    have hSubtract :
        denominator * reserveOut - reserveOut * net = reserveIn * reserveOut := by
      dsimp [denominator]
      ring_nf
      simp
    calc
      reserveIn * reserveOut = denominator * reserveOut - reserveOut * net := hSubtract.symm
      _ ≤ denominator * reserveOut - denominator * output :=
        Nat.sub_le_sub_left hFloor (denominator * reserveOut)
      _ = denominator * (reserveOut - output) := by rw [Nat.mul_sub]
  calc
    reserveIn * reserveOut ≤ denominator * (reserveOut - output) := hCore
    _ ≤ (reserveIn + gross) * (reserveOut - output) :=
      Nat.mul_le_mul_right (reserveOut - output) hDenominatorLe
    _ = (reserveIn + gross) *
        (reserveOut - swapOutput reserveIn reserveOut
          (gross - computeFee gross feeBps)) := by rfl

theorem lookup_replace_other
    (before after : List Pool) (oldPool newPool : Pool)
    (hPoolId : newPool.poolId = oldPool.poolId)
    (otherPoolId : PoolId) (hOther : otherPoolId ≠ oldPool.poolId) :
    lookupPool otherPoolId (before ++ newPool :: after) =
      lookupPool otherPoolId (before ++ oldPool :: after) := by
  induction before with
  | nil =>
      have hOther' : oldPool.poolId ≠ otherPoolId := Ne.symm hOther
      simp [lookupPool, hPoolId, hOther']
  | cons pool rest ih =>
      simp only [List.cons_append, lookupPool]
      split
      · rfl
      · exact ih

theorem lookup_selected_after_prefix
    (before after : List Pool) (selected updated : Pool)
    (hUpdatedId : updated.poolId = selected.poolId)
    (hSelectedAbsent : selected.poolId ∉ poolIds before) :
    lookupPool selected.poolId (before ++ updated :: after) = some updated := by
  induction before with
  | nil => simp [lookupPool, hUpdatedId]
  | cons pool rest ih =>
      have hPoolId : pool.poolId ≠ selected.poolId := by
        intro hEqual
        apply hSelectedAbsent
        simp [poolIds, hEqual]
      have hRest : selected.poolId ∉ poolIds rest := by
        intro hMember
        apply hSelectedAbsent
        simp only [poolIds, List.map_cons, List.mem_cons]
        exact Or.inr hMember
      simp [lookupPool, hPoolId, ih hRest]

theorem valid_selected_pool_absent_from_prefix
    {input : Input} (hValid : Valid input) :
    input.selection.selected.poolId ∉ poolIds input.selection.before := by
  have hRegistry := valid_guard hValid .laneMalformed
  have hSelection := valid_guard hValid .selectionMismatch
  have hNodup : (poolIds input.preState.pools).Nodup := hRegistry.1.1.nodup
  rw [hSelection.1] at hNodup
  simp only [poolIds, List.map_append, List.map_cons] at hNodup
  have hMiddle := (List.nodup_middle.mp hNodup)
  have hNotAll :
      input.selection.selected.poolId ∉
        poolIds input.selection.before ++ poolIds input.selection.after :=
    (List.nodup_cons.mp hMiddle).1
  intro hMember
  apply hNotAll
  simp [hMember]

theorem accepted_selected_pool_lookup_exact
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    lookupPool input.selection.selected.poolId post.pools =
      some (updatedSelectedPool input) := by
  have hValid := accepted_implies_valid hAccepted
  have hAbsent := valid_selected_pool_absent_from_prefix hValid
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨_hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  exact lookup_selected_after_prefix input.selection.before input.selection.after
    input.selection.selected (updatedSelectedPool input) rfl hAbsent

theorem accepted_preserves_every_sibling_pool
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation)
    (otherPoolId : PoolId)
    (hOther : otherPoolId ≠ input.selection.selected.poolId) :
    lookupPool otherPoolId post.pools =
      lookupPool otherPoolId input.preState.pools := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  have hValid := (firstReject_none_iff input).mp hNoReject
  have hSelection := valid_guard hValid .selectionMismatch
  rw [hSelection.1]
  exact lookup_replace_other input.selection.before input.selection.after
    input.selection.selected (updatedSelectedPool input) rfl otherPoolId hOther

theorem accepted_preserves_unrelated_spot_commitments
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    post.lpOwnershipRoot = input.preState.lpOwnershipRoot ∧
      post.routeBatchRoot = input.preState.routeBatchRoot ∧
      post.feeResidueRoot = input.preState.feeResidueRoot ∧
      post.poolTerminalObligationsRoot = input.preState.poolTerminalObligationsRoot := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨_hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  simp [acceptedPostState]

theorem accepted_pool_id_sequence_unchanged
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    poolIds post.pools = poolIds input.preState.pools := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  have hValid := (firstReject_none_iff input).mp hNoReject
  have hSelection := valid_guard hValid .selectionMismatch
  rw [hSelection.1]
  simp [acceptedPostState, poolIds, updatedSelectedPool]

theorem accepted_registry_remains_canonical
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    RegistryCanonical input.authority.release post.pools := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  have hValid := (firstReject_none_iff input).mp hNoReject
  have hRegistry := valid_guard hValid .laneMalformed
  have hSelection := valid_guard hValid .selectionMismatch
  have hUpdated := valid_updated_selected_pool_well_formed hValid
  rcases hRegistry.1 with ⟨hSorted, hNonempty, hCountCap, hAllPools⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSelection.1] at hSorted
    simpa [acceptedPostState, poolIds, updatedSelectedPool] using hSorted
  · rw [hSelection.1] at hNonempty
    simp [acceptedPostState]
  · rw [hSelection.1] at hCountCap
    simpa [acceptedPostState] using hCountCap
  · intro pool hMember
    simp only [acceptedPostState, List.mem_append, List.mem_cons] at hMember
    rcases hMember with hBefore | hUpdatedPool | hAfter
    · exact hAllPools pool <| by
        rw [hSelection.1]
        simp [hBefore]
    · subst pool
      exact hUpdated
    · exact hAllPools pool <| by
        rw [hSelection.1]
        simp [hAfter]

theorem accepted_derives_exact_pool_effects_and_ports
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    post.pools =
        input.selection.before ++ updatedSelectedPool input :: input.selection.after ∧
      effects = acceptedEffects input ∧
      effects.custodyDeltas = [
        { kind := .accountMovement
          accountingDomain := .spotPoolReserve
          asset := input.authority.policy.quoteAsset
          principal := input.selection.selected.definition.reserve0Principal
          deltaAtoms := Int.ofNat input.quotePort.amountAtoms },
        { kind := .accountMovement
          accountingDomain := .spotPoolReserve
          asset := input.authority.policy.zdexAsset
          principal := input.selection.selected.definition.reserve1Principal
          deltaAtoms := -Int.ofNat (purchasedZDEX input) }
      ] ∧
      effects.laneWrites = [
        { lane := .spotLiquidity
          preStateRoot := input.authority.currentPreStateRoot
          postStateRoot := spotLaneStateCommitment (acceptedPostState input) }
      ] ∧
      effects.consumedObjectIds = [] ∧
      ports.quoteInput = acceptedQuoteInputFlow input ∧
      ports.purchasedOutput = acceptedPurchasedOutputFlow input ∧
      ports.quoteInput.amountAtoms = input.quotePort.amountAtoms ∧
      ports.purchasedOutput.amountAtoms = purchasedZDEX input := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨_hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  simp [acceptedPostState, acceptedEffects, acceptedPorts,
    acceptedQuoteInputFlow, acceptedPurchasedOutputFlow]

theorem accepted_selected_pool_exact_update
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    lookupPool input.selection.selected.poolId post.pools =
        some (updatedSelectedPool input) ∧
      (updatedSelectedPool input).poolId = input.selection.selected.poolId ∧
      (updatedSelectedPool input).definition = input.selection.selected.definition ∧
      (updatedSelectedPool input).reserve0Atoms =
        input.selection.selected.reserve0Atoms + input.quotePort.amountAtoms ∧
      (updatedSelectedPool input).reserve1Atoms + purchasedZDEX input =
        input.selection.selected.reserve1Atoms ∧
      (updatedSelectedPool input).lpSupplyAtoms = input.selection.selected.lpSupplyAtoms ∧
      (updatedSelectedPool input).status = input.selection.selected.status ∧
      (updatedSelectedPool input).creationReleaseId =
        input.selection.selected.creationReleaseId ∧
      (updatedSelectedPool input).createdHeight = input.selection.selected.createdHeight := by
  have hLookup := accepted_selected_pool_lookup_exact hAccepted
  have hValid := accepted_implies_valid hAccepted
  have hDrain := valid_purchased_zdex_lt_reserve hValid
  refine ⟨hLookup, ?_⟩
  simp [updatedSelectedPool]
  omega

theorem accepted_price_safety_is_over_derived_output
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    PriceSafe input ∧
      input.priceEnvelope.minimumOutputAtoms = governedMinimumOutput input ∧
      input.priceEnvelope.minimumOutputAtoms ≤ purchasedZDEX input := by
  have hValid := accepted_implies_valid hAccepted
  have hPrice := valid_guard hValid .priceUnsafe
  have hMinimum := valid_guard hValid .minimumOutputMismatch
  exact ⟨hPrice, hMinimum.1, hMinimum.2.2⟩

theorem accepted_cpmm_k_nondecreasing
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    lookupPool input.selection.selected.poolId post.pools =
        some (updatedSelectedPool input) ∧
      input.selection.selected.reserve0Atoms * input.selection.selected.reserve1Atoms ≤
        (updatedSelectedPool input).reserve0Atoms *
          (updatedSelectedPool input).reserve1Atoms := by
  refine ⟨accepted_selected_pool_lookup_exact hAccepted, ?_⟩
  simpa [updatedSelectedPool, purchasedZDEX, netIn, feeTotal] using
    (cpmm_k_nondecreasing
      (reserveIn := input.selection.selected.reserve0Atoms)
      (reserveOut := input.selection.selected.reserve1Atoms)
      (gross := input.quotePort.amountAtoms)
      (feeBps := input.selection.selected.definition.feeBps))

theorem accepted_terminal_obligation_is_nonzero_and_context_bound
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    0 < obligation.obligationId ∧
      obligation = acceptedTerminalObligation input := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨_hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  simp [acceptedTerminalObligation]

theorem accepted_journal_binds_exact_transition
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    journal = acceptedJournal input ∧
      journal.postStateRoot = spotLaneStateCommitment post ∧
      journal.effectPlanRoot = spotEffectsCommitment effects ∧
      journal.privatePortsRoot = privatePortsCommitment ports ∧
      journal.terminalObligationCommitment =
        terminalObligationFullCommitment obligation ∧
      journal.terminalObligationId = obligation.obligationId := by
  rw [accepted_iff] at hAccepted
  rcases hAccepted with ⟨_hNoReject, rfl, rfl, rfl, rfl, rfl⟩
  simp [acceptedJournal, acceptedPostState, acceptedEffects, acceptedPorts,
    acceptedTerminalObligation]

theorem accepted_spot_value_conservation
    {input : Input} {post : SpotLaneState} {effects : SpotEffects}
    {ports : PrivatePorts} {journal : Journal} {obligation : TerminalObligation}
    (hAccepted : transition input = .accepted post effects ports journal obligation) :
    lookupPool input.selection.selected.poolId post.pools =
        some (updatedSelectedPool input) ∧
      (updatedSelectedPool input).reserve0Atoms =
        input.selection.selected.reserve0Atoms + input.quotePort.amountAtoms ∧
      (updatedSelectedPool input).reserve1Atoms + purchasedZDEX input =
        input.selection.selected.reserve1Atoms ∧
      feeTotal input + netIn input = input.quotePort.amountAtoms ∧
      effects.custodyDeltas = (acceptedEffects input).custodyDeltas ∧
      ports.quoteInput = acceptedQuoteInputFlow input ∧
      ports.purchasedOutput = acceptedPurchasedOutputFlow input ∧
      ports.quoteInput.amountAtoms = input.quotePort.amountAtoms ∧
      ports.purchasedOutput.amountAtoms = purchasedZDEX input := by
  have hValid := accepted_implies_valid hAccepted
  have hFee := valid_guard hValid .feeConsumesInput
  have hGross := fee_plus_net_eq_gross (Nat.le_of_lt hFee)
  have hUpdate := accepted_selected_pool_exact_update hAccepted
  have hExact := accepted_derives_exact_pool_effects_and_ports hAccepted
  rcases hUpdate with
    ⟨hLookup, _hId, _hDefinition, hQuote, hZDEX, _hLP, _hStatus, _hRelease, _hHeight⟩
  rcases hExact with
    ⟨_postPools, hEffects, _hCustody, _hLane, _hConsumed,
      hQuoteFlow, hPurchasedFlow, hQuoteAmount, hPurchasedAmount⟩
  exact ⟨hLookup, hQuote, hZDEX, hGross, by simp [hEffects],
    hQuoteFlow, hPurchasedFlow, hQuoteAmount, hPurchasedAmount⟩

def nonvacuityDefinition : PoolDefinition where
  asset0 := 1
  asset1 := 2
  feeBps := 0
  curveRelease := .cpmmV8ExactIn
  curveParamsRoot := 0
  reserve0Principal := 10
  reserve1Principal := 11

def nonvacuityPool : Pool where
  poolId := derivePoolId nonvacuityDefinition
  definition := nonvacuityDefinition
  reserve0Atoms := 1000
  reserve1Atoms := 1000
  lpSupplyAtoms := 1000
  status := .active
  creationReleaseId := 77
  createdHeight := 1

def nonvacuityState : SpotLaneState where
  pools := [nonvacuityPool]
  lpOwnershipRoot := 11
  routeBatchRoot := 12
  feeResidueRoot := 13
  poolTerminalObligationsRoot := 14

def nonvacuityPolicy : ExecutionPolicy where
  selectedPoolId := derivePoolId nonvacuityDefinition
  expectedDefinition := nonvacuityDefinition
  quoteAsset := 1
  zdexAsset := 2
  quoteSourcePrincipal := 20
  zdexDestinationPrincipal := 21

def nonvacuityPricePolicy : PricePolicy where
  maximumOracleAgeBlocks := 3
  minimumQuoteReserve := 500
  minimumZdexReserve := 500
  maximumPoolOracleDeviationBps := 2_000
  maximumExecutionImpactBps := 2_000
  maximumOracleExecutionDeviationBps := 1_000
  maximumQuoteReserveSpendBps := 2_000

def nonvacuityProfileAuthorization : ProfileAuthorization :=
  makeProfileAuthorization 1 2 approvedRouteReleaseId
    approvedSpotModuleReleaseId approvedTokenomicsModuleReleaseId
    31 approvedRelease nonvacuityPolicy nonvacuityPricePolicy

def nonvacuityOracleOccurrence : OracleOccurrence where
  oracleProviderId := 31
  quoteAsset := 1
  zdexAsset := 2
  quoteNumerator := 125
  zdexDenominator := 111
  observedHeight := 76
  finalityRoot := 96
  status := .final

def nonvacuityOracleRegistry : OracleRegistrySnapshot where
  occurrences := [nonvacuityOracleOccurrence]

def nonvacuityAuthority : AuthorityContext where
  chainId := 1
  deploymentId := 2
  currentProfileRoot := nonvacuityProfileAuthorization.profileId
  currentRouteReleaseId := approvedRouteReleaseId
  occurrenceId := 92
  currentPreStateRoot := spotLaneStateCommitment nonvacuityState
  writerEpoch := 0
  currentHeight := 77
  currentSpotModuleReleaseId := approvedSpotModuleReleaseId
  currentTokenomicsModuleReleaseId := approvedTokenomicsModuleReleaseId
  authorizedOracleProviderId := 31
  oracleOccurrenceId := deriveOracleOccurrenceId 1 2 nonvacuityOracleOccurrence
  oracleFinalityRoot := 96
  currentOracleRegistryRoot := oracleRegistryCommitment 1 2 nonvacuityOracleRegistry
  oracleRegistry := nonvacuityOracleRegistry
  release := approvedRelease
  policy := nonvacuityPolicy
  pricePolicy := nonvacuityPricePolicy
  profileAuthorization := nonvacuityProfileAuthorization
  oracleOccurrence := nonvacuityOracleOccurrence

def nonvacuityQuotePort : QuoteInputPort where
  profileRoot := nonvacuityProfileAuthorization.profileId
  routeReleaseId := approvedRouteReleaseId
  occurrenceId := 92
  preStateRoot := spotLaneStateCommitment nonvacuityState
  sourceModuleReleaseId := approvedTokenomicsModuleReleaseId
  destinationModuleReleaseId := approvedSpotModuleReleaseId
  sourcePreStateRoot := 201
  sourcePostStateRoot := 202
  sourceEffectPlanRoot := 203
  sourceJournalRoot := 204
  sourceReceiptBindingRoot := 205
  amountAtoms := 125

def nonvacuityPriceEnvelope : PriceEnvelope where
  profileRoot := nonvacuityProfileAuthorization.profileId
  routeReleaseId := approvedRouteReleaseId
  occurrenceId := 92
  preStateRoot := spotLaneStateCommitment nonvacuityState
  selectedPoolId := derivePoolId nonvacuityDefinition
  oracleOccurrenceId := deriveOracleOccurrenceId 1 2 nonvacuityOracleOccurrence
  oracleFinalityRoot := 96
  quoteAmountAtoms := 125
  currentHeight := 77
  oracleObservedHeight := 76
  oracleQuoteNumerator := 125
  oracleQuoteDenominator := 111
  claimedRouteSafeQuoteLimitAtoms := 200
  minimumOutputAtoms := 101

def nonvacuityInput : Input where
  authority := nonvacuityAuthority
  preState := nonvacuityState
  quotePort := nonvacuityQuotePort
  priceEnvelope := nonvacuityPriceEnvelope
  selection := { before := [], selected := nonvacuityPool, after := [] }

def withCommandOccurrence (input : Input) (occurrenceId : OccurrenceId) : Input :=
  { input with
    authority := { input.authority with occurrenceId := occurrenceId }
    quotePort := { input.quotePort with occurrenceId := occurrenceId }
    priceEnvelope := { input.priceEnvelope with occurrenceId := occurrenceId } }

def differentCommandOccurrenceInput : Input :=
  withCommandOccurrence nonvacuityInput 93

def unauthorizedOracleOccurrence : OracleOccurrence :=
  { nonvacuityOracleOccurrence with oracleProviderId := 32 }

def unauthorizedOracleInput : Input :=
  withOracleOccurrence nonvacuityInput unauthorizedOracleOccurrence

def freshnessBoundaryOracleOccurrence : OracleOccurrence :=
  { nonvacuityOracleOccurrence with observedHeight := 74 }

def freshnessBoundaryInput : Input :=
  withOracleOccurrence nonvacuityInput freshnessBoundaryOracleOccurrence

def staleOracleOccurrence : OracleOccurrence :=
  { nonvacuityOracleOccurrence with observedHeight := 73 }

def staleOracleInput : Input :=
  withOracleOccurrence nonvacuityInput staleOracleOccurrence

def registeredSiblingDefinition : PoolDefinition where
  asset0 := 3
  asset1 := 4
  feeBps := 25
  curveRelease := .registeredOther 8_001
  curveParamsRoot := 801
  reserve0Principal := 12
  reserve1Principal := 13

def registeredSiblingPool : Pool where
  poolId := derivePoolId registeredSiblingDefinition
  definition := registeredSiblingDefinition
  reserve0Atoms := 500
  reserve1Atoms := 700
  lpSupplyAtoms := 400
  status := .active
  creationReleaseId := 8_001
  createdHeight := 2

def registeredSiblingInput : Input :=
  withPreStateAndSelection nonvacuityInput
    { nonvacuityState with pools := [nonvacuityPool, registeredSiblingPool] }
    { before := [], selected := nonvacuityPool, after := [registeredSiblingPool] }

def unregisteredSiblingDefinition : PoolDefinition :=
  { registeredSiblingDefinition with curveRelease := .registeredOther 8_002 }

def unregisteredSiblingPool : Pool :=
  { registeredSiblingPool with
    poolId := derivePoolId unregisteredSiblingDefinition
    definition := unregisteredSiblingDefinition
    creationReleaseId := 8_002 }

def unregisteredSiblingInput : Input :=
  withPreStateAndSelection nonvacuityInput
    { nonvacuityState with pools := [nonvacuityPool, unregisteredSiblingPool] }
    { before := [], selected := nonvacuityPool, after := [unregisteredSiblingPool] }

def revokedSiblingRelease : SpotBuybackRelease :=
  { approvedRelease with
    registeredSiblingCurveReleases := [⟨8_002, .revoked⟩] }

def authorityMalformedInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentProfileRoot := 0 } }

def releaseMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        release := { approvedRelease with protocolFeeShareBps := 1 } } }

def profileMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        profileAuthorization :=
          { nonvacuityProfileAuthorization with executionPolicyCommitment := 999 } } }

def stateCommitmentMismatchInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentPreStateRoot := 999 } }

def quotePortMismatchInput : Input :=
  { nonvacuityInput with
    quotePort := { nonvacuityQuotePort with profileRoot := 999 } }

def quotePortProvenanceMismatchInput : Input :=
  { nonvacuityInput with
    quotePort :=
      { nonvacuityQuotePort with
        sourcePostStateRoot := nonvacuityQuotePort.sourcePreStateRoot } }

def priceSubjectMismatchInput : Input :=
  { nonvacuityInput with
    priceEnvelope := { nonvacuityPriceEnvelope with profileRoot := 999 } }

def oracleMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        oracleOccurrence := { nonvacuityOracleOccurrence with status := .pending } } }

def policyMismatchInput : Input :=
  withExecutionPolicy nonvacuityInput
    { nonvacuityPolicy with quoteSourcePrincipal := 0 }

def laneMalformedInput : Input :=
  withPreStateAndSelection nonvacuityInput
    { nonvacuityState with pools := [] }
    { before := [], selected := nonvacuityPool, after := [] }

def selectionMismatchInput : Input :=
  { nonvacuityInput with
    selection := {
      before := []
      selected := nonvacuityPool
      after := [nonvacuityPool]
    } }

def inactivePool : Pool :=
  { nonvacuityPool with status := .frozen }

def poolInactiveInput : Input :=
  withPreStateAndSelection nonvacuityInput
    { nonvacuityState with pools := [inactivePool] }
    { before := [], selected := inactivePool, after := [] }

def amountOutOfRangeInput : Input :=
  { nonvacuityInput with
    quotePort := { nonvacuityQuotePort with amountAtoms := 0 }
    priceEnvelope := { nonvacuityPriceEnvelope with quoteAmountAtoms := 0 } }

def arithmeticOutOfRangeInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentHeight := maxU64 + 1 }
    priceEnvelope := { nonvacuityPriceEnvelope with currentHeight := maxU64 + 1 } }

def maxU64HeightInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentHeight := maxU64 }
    priceEnvelope := { nonvacuityPriceEnvelope with currentHeight := maxU64 } }

def fullFeeDefinition : PoolDefinition :=
  { nonvacuityDefinition with feeBps := 10_000 }

def fullFeePool : Pool :=
  { nonvacuityPool with
    poolId := derivePoolId fullFeeDefinition
    definition := fullFeeDefinition }

def fullFeePolicy : ExecutionPolicy :=
  { nonvacuityPolicy with
    selectedPoolId := derivePoolId fullFeeDefinition
    expectedDefinition := fullFeeDefinition }

def feeConsumesInput : Input :=
  let policyInput := withExecutionPolicy nonvacuityInput fullFeePolicy
  withPreStateAndSelection
    { policyInput with
    priceEnvelope :=
      { policyInput.priceEnvelope with selectedPoolId := derivePoolId fullFeeDefinition } }
    { nonvacuityState with pools := [fullFeePool] }
    { before := [], selected := fullFeePool, after := [] }

def zeroOutputPool : Pool :=
  { nonvacuityPool with
    reserve0Atoms := maxReserveAtoms - 1
    reserve1Atoms := 1
    lpSupplyAtoms := 1 }

def zeroOutputInput : Input :=
  let stateInput := withPreStateAndSelection nonvacuityInput
    { nonvacuityState with pools := [zeroOutputPool] }
    { before := [], selected := zeroOutputPool, after := [] }
  { stateInput with
    quotePort := { stateInput.quotePort with amountAtoms := 1 }
    priceEnvelope := { stateInput.priceEnvelope with quoteAmountAtoms := 1 } }

def minimumOutputMismatchInput : Input :=
  { nonvacuityInput with
    priceEnvelope := { nonvacuityPriceEnvelope with minimumOutputAtoms := 102 } }

def priceUnsafeInput : Input :=
  let occurrence : OracleOccurrence :=
    { nonvacuityOracleOccurrence with
      quoteNumerator := 2
      zdexDenominator := 1 }
  let oracleInput := withOracleOccurrence nonvacuityInput occurrence
  { oracleInput with
    priceEnvelope :=
      { oracleInput.priceEnvelope with
        minimumOutputAtoms := 57 } }

def roundedFeeDefinition : PoolDefinition :=
  { nonvacuityDefinition with feeBps := 30 }

def roundedFeePool : Pool :=
  { nonvacuityPool with
    poolId := derivePoolId roundedFeeDefinition
    definition := roundedFeeDefinition }

def roundedFeePolicy : ExecutionPolicy :=
  { nonvacuityPolicy with
    selectedPoolId := derivePoolId roundedFeeDefinition
    expectedDefinition := roundedFeeDefinition }

def roundedFeeInput : Input :=
  let policyInput := withExecutionPolicy nonvacuityInput roundedFeePolicy
  let stateInput := withPreStateAndSelection
    policyInput
    { nonvacuityState with pools := [roundedFeePool] }
    { before := [], selected := roundedFeePool, after := [] }
  { stateInput with
    priceEnvelope :=
      { stateInput.priceEnvelope with
        selectedPoolId := derivePoolId roundedFeeDefinition } }

def oneAtomPool : Pool :=
  { nonvacuityPool with
    reserve0Atoms := 100
    reserve1Atoms := 10_000
    lpSupplyAtoms := 100 }

def oneAtomPricePolicy : PricePolicy where
  maximumOracleAgeBlocks := 3
  minimumQuoteReserve := 100
  minimumZdexReserve := 100
  maximumPoolOracleDeviationBps := 9_999
  maximumExecutionImpactBps := 9_999
  maximumOracleExecutionDeviationBps := 9_999
  maximumQuoteReserveSpendBps := 2_000

def oneAtomOracleOccurrence : OracleOccurrence :=
  { nonvacuityOracleOccurrence with
    quoteNumerator := 1
    zdexDenominator := 100 }

def oneAtomInput : Input :=
  let stateInput := withPreStateAndSelection
    nonvacuityInput
    { nonvacuityState with pools := [oneAtomPool] }
    { before := [], selected := oneAtomPool, after := [] }
  let policyInput := withPricePolicy stateInput oneAtomPricePolicy
  let oracleInput := withOracleOccurrence policyInput oneAtomOracleOccurrence
  { oracleInput with
    quotePort := { oracleInput.quotePort with amountAtoms := 1 }
    priceEnvelope :=
      { oracleInput.priceEnvelope with
        quoteAmountAtoms := 1
        claimedRouteSafeQuoteLimitAtoms := 20
        minimumOutputAtoms := 51 } }

theorem nonvacuity_output_is_derived : purchasedZDEX nonvacuityInput = 111 := by
  native_decide

theorem nonvacuity_first_reject_is_none : firstReject nonvacuityInput = none := by
  native_decide

theorem rounded_fee_fixture_is_live :
    feeTotal roundedFeeInput = 1 ∧
      purchasedZDEX roundedFeeInput = 110 ∧
      firstReject roundedFeeInput = none := by
  native_decide

theorem one_atom_fixture_is_live :
    oneAtomInput.quotePort.amountAtoms = 1 ∧
      purchasedZDEX oneAtomInput = 99 ∧
      firstReject oneAtomInput = none := by
  native_decide

theorem arithmetic_out_of_range_fixture_is_live :
    firstReject arithmeticOutOfRangeInput = some .arithmeticOutOfRange := by
  native_decide

theorem command_occurrence_separates_both_flow_ids :
    firstReject differentCommandOccurrenceInput = none ∧
      quoteInputFlowId nonvacuityInput ≠
        quoteInputFlowId differentCommandOccurrenceInput ∧
      purchasedOutputFlowId nonvacuityInput ≠
        purchasedOutputFlowId differentCommandOccurrenceInput := by
  constructor
  · native_decide
  constructor
  · intro hEqual
    have hFlow := flowIdentityCommitment_injective hEqual
    have hOccurrence := congrArg FlowIdentity.commandOccurrenceId hFlow
    norm_num [quoteInputFlowId, acceptedQuoteInputFlow,
      differentCommandOccurrenceInput, withCommandOccurrence,
      nonvacuityInput, nonvacuityAuthority] at hOccurrence
  · intro hEqual
    have hFlow := flowIdentityCommitment_injective hEqual
    have hOccurrence := congrArg FlowIdentity.commandOccurrenceId hFlow
    norm_num [purchasedOutputFlowId, acceptedPurchasedOutputFlow,
      differentCommandOccurrenceInput, withCommandOccurrence,
      nonvacuityInput, nonvacuityAuthority] at hOccurrence

theorem unauthorized_oracle_provider_rejects :
    firstReject unauthorizedOracleInput = some .oracleMismatch := by
  native_decide

theorem oracle_freshness_boundary_is_exact :
    firstReject freshnessBoundaryInput = none ∧
      firstReject staleOracleInput = some .priceUnsafe := by
  native_decide

theorem machine_height_boundary_is_exact :
    GuardHolds maxU64HeightInput .arithmeticOutOfRange ∧
      firstReject arithmeticOutOfRangeInput = some .arithmeticOutOfRange := by
  native_decide

theorem tokenomics_source_provenance_is_required :
    firstReject quotePortProvenanceMismatchInput = some .quotePortMismatch := by
  native_decide

theorem registered_sibling_curve_is_live :
    firstReject registeredSiblingInput = none := by
  native_decide

theorem unregistered_sibling_curve_rejects :
    firstReject unregisteredSiblingInput = some .laneMalformed := by
  native_decide

theorem revoked_sibling_curve_is_not_well_formed :
    ¬PoolStaticWellFormed revokedSiblingRelease unregisteredSiblingPool := by
  native_decide

theorem every_reject_family_has_a_concrete_witness :
    firstReject authorityMalformedInput = some .authorityMalformed ∧
      firstReject releaseMismatchInput = some .releaseMismatch ∧
      firstReject profileMismatchInput = some .profileMismatch ∧
      firstReject stateCommitmentMismatchInput = some .stateCommitmentMismatch ∧
      firstReject quotePortMismatchInput = some .quotePortMismatch ∧
      firstReject oracleMismatchInput = some .oracleMismatch ∧
      firstReject priceSubjectMismatchInput = some .priceSubjectMismatch ∧
      firstReject policyMismatchInput = some .policyMismatch ∧
      firstReject laneMalformedInput = some .laneMalformed ∧
      firstReject selectionMismatchInput = some .selectionMismatch ∧
      firstReject poolInactiveInput = some .poolInactive ∧
      firstReject amountOutOfRangeInput = some .amountOutOfRange ∧
      firstReject arithmeticOutOfRangeInput = some .arithmeticOutOfRange ∧
      firstReject feeConsumesInput = some .feeConsumesInput ∧
      firstReject zeroOutputInput = some .zeroOutput ∧
      firstReject minimumOutputMismatchInput = some .minimumOutputMismatch ∧
      firstReject priceUnsafeInput = some .priceUnsafe := by
  native_decide

theorem nonvacuity_accepts :
    transition nonvacuityInput = .accepted
      (acceptedPostState nonvacuityInput)
      (acceptedEffects nonvacuityInput)
      (acceptedPorts nonvacuityInput)
      (acceptedJournal nonvacuityInput)
      (acceptedTerminalObligation nonvacuityInput) := by
  simp only [transition, nonvacuity_first_reject_is_none]

end ZDEXSpotBuybackTransitionV1
end Proofs
