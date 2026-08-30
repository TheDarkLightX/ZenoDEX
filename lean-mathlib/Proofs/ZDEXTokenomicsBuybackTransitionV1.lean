import Proofs.ZDEXBuybackSpendV1
import Proofs.ZDEXSpotBuybackTransitionV1

/-!
Abstract formal functional core for the ZDEX_TOKENOMICS-owned part of one
governed, same-occurrence ZDEX buy-and-burn route.

This mathematical model owns fee allocation, buyback-reserve spending,
cadence, and the exact burn inside one abstract tokenomics state. It consumes
the typed purchased-ZDEX port and the `MUST_BURN_PURCHASED_ZDEX` terminal
obligation produced by `Proofs.ZDEXSpotBuybackTransitionV1`, and it produces
the typed quote-input port that the same Spot command consumes.

The fee amount is derived from committed fee ingress, so no caller may select a
fee budget. The quote spend is derived by the governed selection rule of
`Proofs.ZDEXBuybackSpendV1`, so no caller may select inventory. The burned
amount is read from the Spot purchased-ZDEX port, so no caller may select a
burn amount.

Nonclaims: this file does not model the runtime's two-phase V2 dependency
order, complete supply-control state, or full effect and reject schemas. It
does not establish canonical-byte encoding, cryptographic
root or collision resistance, Python/Rust parity, RISC0 receipt validity, Spot
lane-receipt verification, route or epoch composition, migration, or ZenoLedger
publication authority. The route-safe quote limit, the Oracle registry root,
and the Spot flow preimages remain authenticated verifier-port premises. No
mount, settlement, production, or value-moving authority is created.
-/

namespace Proofs
namespace ZDEXTokenomicsBuybackTransitionV1

open Proofs.ZDEXSpotBuybackTransitionV1 (encodeNats encodeNats_injective intCommitment)

abbrev Root := Nat
abbrev AssetId := Nat
abbrev PrincipalId := Nat
abbrev ReleaseId := Nat
abbrev OccurrenceId := Nat

/-- Spot leaf whose typed ports and terminal obligation this leaf consumes. -/
abbrev SpotFlow := Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity
abbrev SpotObligation := Proofs.ZDEXSpotBuybackTransitionV1.TerminalObligation

def maxU64 : Nat := Proofs.ZDEXSpotBuybackTransitionV1.maxU64
def maxU128 : Nat := Proofs.ZDEXSpotBuybackTransitionV1.maxU128
def maxI127 : Nat := Proofs.ZDEXSpotBuybackTransitionV1.maxI127

def basisPointsDenominator : Nat := 10_000

def approvedTokenomicsModuleReleaseId : ReleaseId :=
  Proofs.ZDEXSpotBuybackTransitionV1.approvedTokenomicsModuleReleaseId

def approvedRouteReleaseId : ReleaseId :=
  Proofs.ZDEXSpotBuybackTransitionV1.approvedRouteReleaseId

def approvedSpotModuleReleaseId : ReleaseId :=
  Proofs.ZDEXSpotBuybackTransitionV1.approvedSpotModuleReleaseId

/-! ## Closed fee destinations

The runtime keeps a canonically ordered tuple with a validated destination
sequence. The exact record removes order, cardinality, and duplicate-key
failure modes by construction. -/

inductive FeeDestination where
  | buyback
  | qualifiedHostPool
  | treasury
  | proofRewards
  | coverReserve
  | lpRebates
  deriving DecidableEq, Repr

def feeDestinationCode : FeeDestination -> Nat
  | .buyback => 1
  | .qualifiedHostPool => 2
  | .treasury => 3
  | .proofRewards => 4
  | .coverReserve => 5
  | .lpRebates => 6

theorem feeDestinationCode_injective : Function.Injective feeDestinationCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [feeDestinationCode]

/-- One value per closed destination. Cardinality, key, and order are exact. -/
structure DestinationAmounts where
  buyback : Nat
  qualifiedHostPool : Nat
  treasury : Nat
  proofRewards : Nat
  coverReserve : Nat
  lpRebates : Nat
  deriving DecidableEq, Repr

def DestinationAmounts.total (amounts : DestinationAmounts) : Nat :=
  amounts.buyback + amounts.qualifiedHostPool + amounts.treasury +
    amounts.proofRewards + amounts.coverReserve + amounts.lpRebates

/-- Every destination other than the buyback reserve. -/
def DestinationAmounts.otherTotal (amounts : DestinationAmounts) : Nat :=
  amounts.qualifiedHostPool + amounts.treasury + amounts.proofRewards +
    amounts.coverReserve + amounts.lpRebates

theorem DestinationAmounts.total_split (amounts : DestinationAmounts) :
    amounts.total = amounts.buyback + amounts.otherTotal := by
  unfold DestinationAmounts.total DestinationAmounts.otherTotal
  omega

def destinationAmountsCommitment (amounts : DestinationAmounts) : Root :=
  encodeNats [
    amounts.buyback,
    amounts.qualifiedHostPool,
    amounts.treasury,
    amounts.proofRewards,
    amounts.coverReserve,
    amounts.lpRebates
  ]

theorem destinationAmountsCommitment_injective :
    Function.Injective destinationAmountsCommitment := by
  rintro ⟨lb, lq, lt, lp, lc, ll⟩ ⟨rb, rq, rt, rp, rc, rl⟩ hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hFields
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
  rfl

/-! ## Governed fee allocation policy -/

structure FeeAllocationPolicy where
  buybackBps : Nat
  qualifiedHostPoolBps : Nat
  treasuryBps : Nat
  proofRewardsBps : Nat
  coverReserveBps : Nat
  lpRebatesBps : Nat
  deriving DecidableEq, Repr

def FeeAllocationPolicy.assignedBasisPoints (policy : FeeAllocationPolicy) : Nat :=
  policy.buybackBps + policy.qualifiedHostPoolBps + policy.treasuryBps +
    policy.proofRewardsBps + policy.coverReserveBps + policy.lpRebatesBps

/-- Unassigned basis points are carried as explicit residue, never dropped. -/
def FeeAllocationPolicyBounded (policy : FeeAllocationPolicy) : Prop :=
  policy.assignedBasisPoints ≤ basisPointsDenominator

instance feeAllocationPolicyBoundedDecidable (policy : FeeAllocationPolicy) :
    Decidable (FeeAllocationPolicyBounded policy) := by
  unfold FeeAllocationPolicyBounded
  infer_instance

def feeAllocationPolicyCommitment (policy : FeeAllocationPolicy) : Root :=
  encodeNats [
    policy.buybackBps,
    policy.qualifiedHostPoolBps,
    policy.treasuryBps,
    policy.proofRewardsBps,
    policy.coverReserveBps,
    policy.lpRebatesBps
  ]

theorem feeAllocationPolicyCommitment_injective :
    Function.Injective feeAllocationPolicyCommitment := by
  rintro ⟨lb, lq, lt, lp, lc, ll⟩ ⟨rb, rq, rt, rp, rc, rl⟩ hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hFields
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
  rfl

/-! ## Release envelope

Numeric caps, minimum spend, and cadence interval are release semantics for
this bounded candidate. They are not selected production economic policy. -/

structure TokenomicsBuybackRelease where
  moduleReleaseId : ReleaseId
  routeReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  perCommandQuoteCapAtoms : Nat
  minimumQuoteSpendAtoms : Nat
  minimumIntervalBlocks : Nat
  feeIngressPrincipal : PrincipalId
  feeResiduePrincipal : PrincipalId
  destinationPrincipalBase : PrincipalId
  zdexBurnPrincipal : PrincipalId
  deriving DecidableEq, Repr

/-- Each closed destination owns a distinct principal derived from the base. -/
def destinationPrincipal
    (release : TokenomicsBuybackRelease) (destination : FeeDestination) : PrincipalId :=
  release.destinationPrincipalBase + feeDestinationCode destination

theorem destinationPrincipal_injective (release : TokenomicsBuybackRelease) :
    Function.Injective (destinationPrincipal release) := by
  intro left right hEqual
  unfold destinationPrincipal at hEqual
  have hCodes : feeDestinationCode left = feeDestinationCode right :=
    Nat.add_left_cancel hEqual
  exact feeDestinationCode_injective hCodes

def releaseCommitment (release : TokenomicsBuybackRelease) : Root :=
  encodeNats [
    release.moduleReleaseId,
    release.routeReleaseId,
    release.spotModuleReleaseId,
    release.perCommandQuoteCapAtoms,
    release.minimumQuoteSpendAtoms,
    release.minimumIntervalBlocks,
    release.feeIngressPrincipal,
    release.feeResiduePrincipal,
    release.destinationPrincipalBase,
    release.zdexBurnPrincipal
  ]

theorem releaseCommitment_injective : Function.Injective releaseCommitment := by
  rintro ⟨la, lb, lc, ld, le, lf, lg, lh, li, lj⟩
    ⟨ra, rb, rc, rd, re, rf, rg, rh, ri, rj⟩ hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hFields
  subst h1; subst h2; subst h3; subst h4; subst h5
  subst h6; subst h7; subst h8; subst h9; subst h10
  rfl

/-! ## Profile authorization -/

structure ProfileAuthorization where
  profileId : Root
  chainId : Nat
  deploymentId : Nat
  routeReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  releaseCommitment : Root
  feePolicyCommitment : Root
  deriving DecidableEq, Repr

def deriveProfileId (authorization : ProfileAuthorization) : Root :=
  encodeNats [
    authorization.chainId,
    authorization.deploymentId,
    authorization.routeReleaseId,
    authorization.tokenomicsModuleReleaseId,
    authorization.spotModuleReleaseId,
    authorization.releaseCommitment,
    authorization.feePolicyCommitment
  ]

def ProfileAuthorizationSelfConsistent (authorization : ProfileAuthorization) : Prop :=
  authorization.profileId = deriveProfileId authorization

/-- A self-consistent profile root determines every authorized coordinate. -/
theorem self_consistent_profile_id_no_alias
    {left right : ProfileAuthorization}
    (hLeft : ProfileAuthorizationSelfConsistent left)
    (hRight : ProfileAuthorizationSelfConsistent right)
    (hEqual : left.profileId = right.profileId) :
    left = right := by
  unfold ProfileAuthorizationSelfConsistent deriveProfileId at hLeft hRight
  rw [hLeft, hRight] at hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hFields
  cases left
  cases right
  simp_all

def makeProfileAuthorization
    (chainId deploymentId : Nat)
    (routeReleaseId tokenomicsModuleReleaseId spotModuleReleaseId : ReleaseId)
    (release : TokenomicsBuybackRelease)
    (policy : FeeAllocationPolicy) : ProfileAuthorization :=
  let record : ProfileAuthorization :=
    { profileId := 0
      chainId := chainId
      deploymentId := deploymentId
      routeReleaseId := routeReleaseId
      tokenomicsModuleReleaseId := tokenomicsModuleReleaseId
      spotModuleReleaseId := spotModuleReleaseId
      releaseCommitment := releaseCommitment release
      feePolicyCommitment := feeAllocationPolicyCommitment policy }
  { record with profileId := deriveProfileId record }

theorem makeProfileAuthorization_is_self_consistent
    (chainId deploymentId : Nat)
    (routeReleaseId tokenomicsModuleReleaseId spotModuleReleaseId : ReleaseId)
    (release : TokenomicsBuybackRelease)
    (policy : FeeAllocationPolicy) :
    ProfileAuthorizationSelfConsistent
      (makeProfileAuthorization chainId deploymentId routeReleaseId
        tokenomicsModuleReleaseId spotModuleReleaseId release policy) := by
  rfl

/-! ## Complete tokenomics lane state -/

structure TokenomicsState where
  quoteAsset : AssetId
  zdexAsset : AssetId
  policyRoot : Root
  feeIngressAtoms : Nat
  unallocatedResidueAtoms : Nat
  destinationBalances : DestinationAmounts
  ownedAndCustodiedAtoms : Nat
  quoteAssetSupplyAtoms : Nat
  liveSupplyAtoms : Nat
  lastExecutionHeight : Option Nat
  stakingRoot : Root
  hostClaimsRoot : Root
  treasuryClaimsRoot : Root
  proofRewardsRoot : Root
  coverReserveRoot : Root
  lpRebatesRoot : Root
  deriving DecidableEq, Repr

/-- Quote atoms this lane has selected across ingress, residue, and reserves. -/
def TokenomicsState.selectedBalanceAtoms (state : TokenomicsState) : Nat :=
  state.feeIngressAtoms + state.unallocatedResidueAtoms + state.destinationBalances.total

def optionalHeightCode : Option Nat -> Nat
  | none => 0
  | some height => height + 1

theorem optionalHeightCode_injective : Function.Injective optionalHeightCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [optionalHeightCode]

def tokenomicsStateCommitment (state : TokenomicsState) : Root :=
  encodeNats [
    state.quoteAsset,
    state.zdexAsset,
    state.policyRoot,
    state.feeIngressAtoms,
    state.unallocatedResidueAtoms,
    destinationAmountsCommitment state.destinationBalances,
    state.ownedAndCustodiedAtoms,
    state.quoteAssetSupplyAtoms,
    state.liveSupplyAtoms,
    optionalHeightCode state.lastExecutionHeight,
    state.stakingRoot,
    state.hostClaimsRoot,
    state.treasuryClaimsRoot,
    state.proofRewardsRoot,
    state.coverReserveRoot,
    state.lpRebatesRoot
  ]

theorem tokenomicsStateCommitment_injective :
    Function.Injective tokenomicsStateCommitment := by
  intro left right hEqual
  have hFields := encodeNats_injective hEqual
  simp only [List.cons.injEq, and_true] at hFields
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hFields
  have hBalances := destinationAmountsCommitment_injective h6
  have hHeight := optionalHeightCode_injective h10
  cases left
  cases right
  simp_all

/-- Well-formedness the lane owner must preserve. Live supply is positive, so a
full-supply burn is unrepresentable, exactly as in the runtime state type. -/
def TokenomicsStateWellFormed
    (policy : FeeAllocationPolicy) (state : TokenomicsState) : Prop :=
  state.policyRoot = feeAllocationPolicyCommitment policy ∧
    0 < state.quoteAsset ∧
    0 < state.zdexAsset ∧
    state.quoteAsset ≠ state.zdexAsset ∧
    state.selectedBalanceAtoms ≤ state.ownedAndCustodiedAtoms ∧
    0 < state.liveSupplyAtoms ∧
    0 < state.stakingRoot ∧
    0 < state.hostClaimsRoot ∧
    0 < state.treasuryClaimsRoot ∧
    0 < state.proofRewardsRoot ∧
    0 < state.coverReserveRoot ∧
    0 < state.lpRebatesRoot

/-! ## Authority context -/

structure AuthorityContext where
  chainId : Nat
  deploymentId : Nat
  profileRoot : Root
  writerEpoch : Nat
  routeReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  occurrenceId : OccurrenceId
  preStateRoot : Root
  currentHeight : Nat
  oracleRegistryRoot : Root
  oracleOccurrenceId : OccurrenceId
  spotReleaseCommitment : Root
  spotExecutionPolicyCommitment : Root
  spotPricePolicyCommitment : Root
  routeSafeQuoteLimitAtoms : Nat
  routeSafeQuoteLimitBindingRoot : Root
  sourceJournalRoot : Root
  sourceReceiptBindingRoot : Root
  release : TokenomicsBuybackRelease
  policy : FeeAllocationPolicy
  profileAuthorization : ProfileAuthorization
  deriving DecidableEq, Repr

/-- Complete admission subject. Purchased ZDEX and the terminal obligation are
Spot-owned inputs; the quote spend and the fee split are derived here. -/
structure Input where
  authority : AuthorityContext
  preState : TokenomicsState
  obligation : SpotObligation
  quoteFlow : SpotFlow
  purchasedFlow : SpotFlow
  deriving DecidableEq, Repr

/-! ## Derived governed quantities -/

/-- The command has no independent fee amount: it consumes committed ingress. -/
def feeCharged (input : Input) : Nat := input.preState.feeIngressAtoms

def allocationOf (feeAtoms shareBps : Nat) : Nat :=
  feeAtoms * shareBps / basisPointsDenominator

def allocations (input : Input) : DestinationAmounts where
  buyback := allocationOf (feeCharged input) input.authority.policy.buybackBps
  qualifiedHostPool :=
    allocationOf (feeCharged input) input.authority.policy.qualifiedHostPoolBps
  treasury := allocationOf (feeCharged input) input.authority.policy.treasuryBps
  proofRewards := allocationOf (feeCharged input) input.authority.policy.proofRewardsBps
  coverReserve := allocationOf (feeCharged input) input.authority.policy.coverReserveBps
  lpRebates := allocationOf (feeCharged input) input.authority.policy.lpRebatesBps

def allocatedTotal (input : Input) : Nat := (allocations input).total

def buybackAllocation (input : Input) : Nat := (allocations input).buyback

def otherAllocations (input : Input) : Nat := (allocations input).otherTotal

def carriedResidue (input : Input) : Nat := feeCharged input - allocatedTotal input

def buybackReservePre (input : Input) : Nat := input.preState.destinationBalances.buyback

def availableReserve (input : Input) : Nat :=
  buybackReservePre input + buybackAllocation input

/-- The sole governed spend rule, reused from the existing spend kernel. -/
def quoteSpend (input : Input) : Nat :=
  Proofs.ZDEXBuybackSpendV1.selectedQuoteSpend
    (availableReserve input)
    input.authority.release.perCommandQuoteCapAtoms
    input.authority.routeSafeQuoteLimitAtoms

def buybackReservePost (input : Input) : Nat :=
  availableReserve input - quoteSpend input

/-- Purchased ZDEX is read from the Spot value port, never chosen locally. -/
def purchasedZDEX (input : Input) : Nat := input.purchasedFlow.amountAtoms

/-! ## Fee conservation arithmetic

Floor allocation never over-allocates: the sum of floored shares is bounded by
the floor of the summed shares, which a bounded policy keeps at or below the
charged fee. The unallocated remainder is carried as explicit residue. -/

theorem nat_div_add_div_le (a b n : Nat) : a / n + b / n ≤ (a + b) / n := by
  rcases Nat.eq_zero_or_pos n with hZero | hPositive
  · subst hZero
    simp
  · rw [Nat.le_div_iff_mul_le hPositive, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a n) (Nat.div_mul_le_self b n)

theorem nat_div_six_sum_le (a b c d e f n : Nat) :
    a / n + b / n + c / n + d / n + e / n + f / n ≤ (a + b + c + d + e + f) / n := by
  have h1 := nat_div_add_div_le a b n
  have h2 := nat_div_add_div_le (a + b) c n
  have h3 := nat_div_add_div_le (a + b + c) d n
  have h4 := nat_div_add_div_le (a + b + c + d) e n
  have h5 := nat_div_add_div_le (a + b + c + d + e) f n
  omega

theorem allocated_total_le_fee
    (input : Input)
    (hBounded : FeeAllocationPolicyBounded input.authority.policy) :
    allocatedTotal input ≤ feeCharged input := by
  have hSum := nat_div_six_sum_le
    (feeCharged input * input.authority.policy.buybackBps)
    (feeCharged input * input.authority.policy.qualifiedHostPoolBps)
    (feeCharged input * input.authority.policy.treasuryBps)
    (feeCharged input * input.authority.policy.proofRewardsBps)
    (feeCharged input * input.authority.policy.coverReserveBps)
    (feeCharged input * input.authority.policy.lpRebatesBps)
    basisPointsDenominator
  have hDistribute :
      feeCharged input * input.authority.policy.buybackBps +
          feeCharged input * input.authority.policy.qualifiedHostPoolBps +
          feeCharged input * input.authority.policy.treasuryBps +
          feeCharged input * input.authority.policy.proofRewardsBps +
          feeCharged input * input.authority.policy.coverReserveBps +
          feeCharged input * input.authority.policy.lpRebatesBps =
        feeCharged input * input.authority.policy.assignedBasisPoints := by
    unfold FeeAllocationPolicy.assignedBasisPoints
    ring
  rw [hDistribute] at hSum
  have hCapped :
      feeCharged input * input.authority.policy.assignedBasisPoints ≤
        feeCharged input * basisPointsDenominator :=
    Nat.mul_le_mul_left (feeCharged input) hBounded
  have hDivide :
      feeCharged input * input.authority.policy.assignedBasisPoints /
          basisPointsDenominator ≤
        feeCharged input * basisPointsDenominator / basisPointsDenominator :=
    Nat.div_le_div_right hCapped
  have hCancel :
      feeCharged input * basisPointsDenominator / basisPointsDenominator =
        feeCharged input := by
    unfold basisPointsDenominator
    omega
  simp only [allocatedTotal, allocations, DestinationAmounts.total, allocationOf]
  omega

/-- `F = b + sum(other) + r` on the exact derived allocation. -/
theorem accepted_fee_conservation
    (input : Input)
    (hBounded : FeeAllocationPolicyBounded input.authority.policy) :
    feeCharged input =
      buybackAllocation input + otherAllocations input + carriedResidue input := by
  have hBound := allocated_total_le_fee input hBounded
  have hSplit := DestinationAmounts.total_split (allocations input)
  simp only [carriedResidue, buybackAllocation, otherAllocations, allocatedTotal] at *
  omega

/-! ## Accepted post-state -/

def acceptedDestinationBalances (input : Input) : DestinationAmounts where
  buyback := buybackReservePost input
  qualifiedHostPool :=
    input.preState.destinationBalances.qualifiedHostPool +
      (allocations input).qualifiedHostPool
  treasury :=
    input.preState.destinationBalances.treasury + (allocations input).treasury
  proofRewards :=
    input.preState.destinationBalances.proofRewards + (allocations input).proofRewards
  coverReserve :=
    input.preState.destinationBalances.coverReserve + (allocations input).coverReserve
  lpRebates :=
    input.preState.destinationBalances.lpRebates + (allocations input).lpRebates

def acceptedPostState (input : Input) : TokenomicsState :=
  { input.preState with
    feeIngressAtoms := input.preState.feeIngressAtoms - feeCharged input
    unallocatedResidueAtoms :=
      input.preState.unallocatedResidueAtoms + carriedResidue input
    destinationBalances := acceptedDestinationBalances input
    ownedAndCustodiedAtoms := input.preState.ownedAndCustodiedAtoms - quoteSpend input
    liveSupplyAtoms := input.preState.liveSupplyAtoms - purchasedZDEX input
    lastExecutionHeight := some input.authority.currentHeight }

/-! ## Canonical tokenomics effects -/

inductive EffectKind where
  | custody
  | feeAllocation
  | reserve
  | burn
  deriving DecidableEq, Repr

def effectKindCode : EffectKind -> Nat
  | .custody => 1
  | .feeAllocation => 2
  | .reserve => 3
  | .burn => 4

theorem effectKindCode_injective : Function.Injective effectKindCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [effectKindCode]

inductive AccountingDomain where
  | feeIngress
  | feeDestination
  | feeResidue
  | zdexSupply
  deriving DecidableEq, Repr

def accountingDomainCode : AccountingDomain -> Nat
  | .feeIngress => 1
  | .feeDestination => 2
  | .feeResidue => 3
  | .zdexSupply => 4

theorem accountingDomainCode_injective : Function.Injective accountingDomainCode := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [accountingDomainCode]

/-- This leaf owns exactly one lane. The code is distinct from the Spot lane
code so a lane write cannot be relabelled across the sole-owner map. -/
inductive LaneId where
  | zdexTokenomics
  deriving DecidableEq, Repr

def laneIdCode : LaneId -> Nat
  | .zdexTokenomics => 2

theorem tokenomics_lane_code_differs_from_spot_lane_code :
    laneIdCode .zdexTokenomics ≠
      Proofs.ZDEXSpotBuybackTransitionV1.laneIdCode .spotLiquidity := by
  decide

structure EffectRow where
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

structure TokenomicsEffects where
  rows : List EffectRow
  laneWrites : List LaneWrite
  consumedObjectIds : List Nat
  dischargedObligationIds : List Nat
  deriving DecidableEq, Repr

def TokenomicsEffects.empty : TokenomicsEffects where
  rows := []
  laneWrites := []
  consumedObjectIds := []
  dischargedObligationIds := []

def effectRowCommitment (row : EffectRow) : Nat :=
  encodeNats [
    effectKindCode row.kind,
    accountingDomainCode row.accountingDomain,
    row.asset,
    row.principal,
    intCommitment row.deltaAtoms
  ]

def laneWriteCommitment (write : LaneWrite) : Nat :=
  encodeNats [laneIdCode write.lane, write.preStateRoot, write.postStateRoot]

/-- The economic effect plan root. It deliberately excludes the discharged
obligation identifiers: the Spot leaf consumes this root inside its quote port
before it can derive the obligation identifier this leaf later discharges. The
discharge is bound separately by `dischargeCommitment`. -/
def effectsCommitment (effects : TokenomicsEffects) : Root :=
  encodeNats [
    encodeNats (effects.rows.map effectRowCommitment),
    encodeNats (effects.laneWrites.map laneWriteCommitment),
    encodeNats effects.consumedObjectIds
  ]

/-- A zero-magnitude row is never emitted, matching the runtime effect type. -/
def allocationRows
    (input : Input) (destination : FeeDestination) (amount : Nat) : List EffectRow :=
  if amount = 0 then [] else
    [{ kind := .feeAllocation
       accountingDomain := .feeDestination
       asset := input.preState.quoteAsset
       principal := destinationPrincipal input.authority.release destination
       deltaAtoms := (amount : Int) }]

def residueRows (input : Input) : List EffectRow :=
  if carriedResidue input = 0 then [] else
    [{ kind := .reserve
       accountingDomain := .feeResidue
       asset := input.preState.quoteAsset
       principal := input.authority.release.feeResiduePrincipal
       deltaAtoms := (carriedResidue input : Int) }]

def feeIngressRow (input : Input) : EffectRow where
  kind := .custody
  accountingDomain := .feeIngress
  asset := input.preState.quoteAsset
  principal := input.authority.release.feeIngressPrincipal
  deltaAtoms := -(feeCharged input : Int)

def buybackSpendRow (input : Input) : EffectRow where
  kind := .custody
  accountingDomain := .feeDestination
  asset := input.preState.quoteAsset
  principal := destinationPrincipal input.authority.release .buyback
  deltaAtoms := -(quoteSpend input : Int)

/-- The burn principal is governed by the release. Reading it from the consumed
obligation would make this leaf's effect plan depend on a value that the Spot
leaf can only derive after consuming this plan. -/
def burnRow (input : Input) : EffectRow where
  kind := .burn
  accountingDomain := .zdexSupply
  asset := input.preState.zdexAsset
  principal := input.authority.release.zdexBurnPrincipal
  deltaAtoms := -(purchasedZDEX input : Int)

def acceptedEffects (input : Input) : TokenomicsEffects where
  rows :=
    feeIngressRow input ::
      (allocationRows input .buyback (allocations input).buyback ++
        allocationRows input .qualifiedHostPool (allocations input).qualifiedHostPool ++
        allocationRows input .treasury (allocations input).treasury ++
        allocationRows input .proofRewards (allocations input).proofRewards ++
        allocationRows input .coverReserve (allocations input).coverReserve ++
        allocationRows input .lpRebates (allocations input).lpRebates ++
        residueRows input ++
        [buybackSpendRow input, burnRow input])
  laneWrites := [
    { lane := .zdexTokenomics
      preStateRoot := input.authority.preStateRoot
      postStateRoot := tokenomicsStateCommitment (acceptedPostState input) }
  ]
  consumedObjectIds := []
  dischargedObligationIds := [input.obligation.obligationId]

/-! ## Terminal discharge and the residual route obligation -/

structure ObligationDischarge where
  obligationId : Nat
  obligationCommitment : Root
  kind : Proofs.ZDEXSpotBuybackTransitionV1.TerminalObligationKind
  burnDomain : Proofs.ZDEXSpotBuybackTransitionV1.BurnDomain
  consumerModuleReleaseId : ReleaseId
  burnAsset : AssetId
  burnPrincipal : PrincipalId
  burnedAtoms : Nat
  quoteInputFlowId : Nat
  purchasedOutputFlowId : Nat
  deriving DecidableEq, Repr

def acceptedDischarge (input : Input) : ObligationDischarge where
  obligationId := input.obligation.obligationId
  obligationCommitment :=
    Proofs.ZDEXSpotBuybackTransitionV1.terminalObligationFullCommitment input.obligation
  kind := input.obligation.kind
  burnDomain := input.obligation.burnDomain
  consumerModuleReleaseId := input.obligation.consumerModuleReleaseId
  burnAsset := input.obligation.burnAsset
  burnPrincipal := input.obligation.burnPrincipal
  burnedAtoms := purchasedZDEX input
  quoteInputFlowId := input.obligation.quoteInputFlowId
  purchasedOutputFlowId := input.obligation.purchasedOutputFlowId

/-- Discharging the Spot burn obligation does not close route composition. The
accepted result still carries a nonzero, fully context-bound coordination
obligation that only a route coordinator may discharge. -/
def routeCoordinationObligationId (input : Input) : Nat :=
  encodeNats [
    input.authority.chainId,
    input.authority.deploymentId,
    input.authority.profileRoot,
    input.authority.writerEpoch,
    input.authority.occurrenceId,
    input.authority.routeReleaseId,
    input.authority.tokenomicsModuleReleaseId,
    input.authority.spotModuleReleaseId,
    input.authority.preStateRoot,
    tokenomicsStateCommitment (acceptedPostState input),
    effectsCommitment (acceptedEffects input),
    input.obligation.obligationId,
    input.obligation.quoteInputFlowId,
    input.obligation.purchasedOutputFlowId,
    quoteSpend input,
    purchasedZDEX input
  ] + 1

theorem routeCoordinationObligationId_is_nonzero (input : Input) :
    0 < routeCoordinationObligationId input := by
  unfold routeCoordinationObligationId
  omega

/-! ## Journal -/

structure Journal where
  chainId : Nat
  deploymentId : Nat
  profileId : Root
  writerEpoch : Nat
  occurrenceId : OccurrenceId
  routeReleaseId : ReleaseId
  tokenomicsModuleReleaseId : ReleaseId
  spotModuleReleaseId : ReleaseId
  releaseCommitment : Root
  feePolicyCommitment : Root
  preStateRoot : Root
  postStateRoot : Root
  effectPlanRoot : Root
  quoteInputFlowId : Nat
  purchasedOutputFlowId : Nat
  dischargedObligationId : Nat
  routeCoordinationObligationId : Nat
  feeChargedAtoms : Nat
  buybackAllocationAtoms : Nat
  otherAllocationAtoms : Nat
  carriedResidueAtoms : Nat
  quoteSpendAtoms : Nat
  purchasedAtoms : Nat
  buybackReservePreAtoms : Nat
  buybackReservePostAtoms : Nat
  liveSupplyPreAtoms : Nat
  liveSupplyPostAtoms : Nat
  executionHeight : Nat
  consumedObjectIds : List Nat
  deriving DecidableEq, Repr

def acceptedJournal (input : Input) : Journal where
  chainId := input.authority.chainId
  deploymentId := input.authority.deploymentId
  profileId := input.authority.profileRoot
  writerEpoch := input.authority.writerEpoch
  occurrenceId := input.authority.occurrenceId
  routeReleaseId := input.authority.routeReleaseId
  tokenomicsModuleReleaseId := input.authority.tokenomicsModuleReleaseId
  spotModuleReleaseId := input.authority.spotModuleReleaseId
  releaseCommitment := releaseCommitment input.authority.release
  feePolicyCommitment := feeAllocationPolicyCommitment input.authority.policy
  preStateRoot := input.authority.preStateRoot
  postStateRoot := tokenomicsStateCommitment (acceptedPostState input)
  effectPlanRoot := effectsCommitment (acceptedEffects input)
  quoteInputFlowId := input.obligation.quoteInputFlowId
  purchasedOutputFlowId := input.obligation.purchasedOutputFlowId
  dischargedObligationId := input.obligation.obligationId
  routeCoordinationObligationId := routeCoordinationObligationId input
  feeChargedAtoms := feeCharged input
  buybackAllocationAtoms := buybackAllocation input
  otherAllocationAtoms := otherAllocations input
  carriedResidueAtoms := carriedResidue input
  quoteSpendAtoms := quoteSpend input
  purchasedAtoms := purchasedZDEX input
  buybackReservePreAtoms := buybackReservePre input
  buybackReservePostAtoms := buybackReservePost input
  liveSupplyPreAtoms := input.preState.liveSupplyAtoms
  liveSupplyPostAtoms := (acceptedPostState input).liveSupplyAtoms
  executionHeight := input.authority.currentHeight
  consumedObjectIds := []

/-! ## Machine-width and cadence admission -/

def FitsU64 (value : Nat) : Prop := value ≤ maxU64
def FitsU128 (value : Nat) : Prop := value ≤ maxU128
def FitsI127Magnitude (value : Nat) : Prop := value ≤ maxI127

def ArithmeticFits (input : Input) : Prop :=
  FitsU64 input.authority.currentHeight ∧
    FitsU64 input.authority.writerEpoch ∧
    FitsU64 (optionalHeightCode input.preState.lastExecutionHeight) ∧
    FitsU64 input.authority.release.minimumIntervalBlocks ∧
    FitsU128 (feeCharged input) ∧
    FitsU128 (feeCharged input * input.authority.policy.assignedBasisPoints) ∧
    FitsU128 (availableReserve input) ∧
    FitsU128 input.authority.release.perCommandQuoteCapAtoms ∧
    FitsU128 input.authority.routeSafeQuoteLimitAtoms ∧
    FitsU128 input.preState.ownedAndCustodiedAtoms ∧
    FitsU128 input.preState.quoteAssetSupplyAtoms ∧
    FitsU128 input.preState.selectedBalanceAtoms ∧
    FitsU128 input.preState.liveSupplyAtoms ∧
    FitsU128 (purchasedZDEX input) ∧
    FitsU128 (input.preState.unallocatedResidueAtoms + carriedResidue input) ∧
    FitsU128 (acceptedPostState input).destinationBalances.total ∧
    FitsI127Magnitude (feeCharged input) ∧
    FitsI127Magnitude (quoteSpend input) ∧
    FitsI127Magnitude (purchasedZDEX input)

/-- Consensus height decides cadence. A never-executed lane is always eligible;
after one execution the governed interval must have elapsed and the height must
not have regressed. -/
def CadenceEligible (input : Input) : Prop :=
  match input.preState.lastExecutionHeight with
  | none => True
  | some height =>
      height ≤ input.authority.currentHeight ∧
        Proofs.ZDEXBuybackSpendV1.cadenceEligible
          input.authority.currentHeight height
          input.authority.release.minimumIntervalBlocks

instance cadenceEligibleDecidable (input : Input) :
    Decidable (CadenceEligible input) := by
  unfold CadenceEligible Proofs.ZDEXBuybackSpendV1.cadenceEligible
  split <;> infer_instance

/-! ## Ordered typed rejection -/

inductive RejectCode where
  | authorityMalformed
  | releaseMismatch
  | profileMismatch
  | stateCommitmentMismatch
  | policyMismatch
  | laneMalformed
  | zeroFee
  | cadenceIneligible
  | arithmeticOutOfRange
  | amountOutOfRange
  | minimumSpendMismatch
  | terminalObligationMismatch
  | purchasedPortMismatch
  | quotePortMismatch
  deriving DecidableEq, Repr

def rejectOrder : List RejectCode := [
  .authorityMalformed,
  .releaseMismatch,
  .profileMismatch,
  .stateCommitmentMismatch,
  .policyMismatch,
  .laneMalformed,
  .zeroFee,
  .cadenceIneligible,
  .arithmeticOutOfRange,
  .amountOutOfRange,
  .minimumSpendMismatch,
  .terminalObligationMismatch,
  .purchasedPortMismatch,
  .quotePortMismatch
]

/-- Coordinates every Spot-produced value must share with this leaf. -/
def SpotFlowAuthorityBound (input : Input) (flow : SpotFlow) : Prop :=
  flow.chainId = input.authority.chainId ∧
    flow.deploymentId = input.authority.deploymentId ∧
    flow.profileId = input.authority.profileRoot ∧
    flow.writerEpoch = input.authority.writerEpoch ∧
    flow.commandOccurrenceId = input.authority.occurrenceId ∧
    flow.routeReleaseId = input.authority.routeReleaseId ∧
    flow.spotModuleReleaseId = input.authority.spotModuleReleaseId ∧
    flow.tokenomicsModuleReleaseId = input.authority.tokenomicsModuleReleaseId ∧
    flow.spotReleaseCommitment = input.authority.spotReleaseCommitment ∧
    flow.executionPolicyCommitment = input.authority.spotExecutionPolicyCommitment ∧
    flow.pricePolicyCommitment = input.authority.spotPricePolicyCommitment ∧
    flow.oracleRegistryRoot = input.authority.oracleRegistryRoot ∧
    flow.oracleOccurrenceId = input.authority.oracleOccurrenceId ∧
    flow.selectedPoolId = input.obligation.selectedPoolId ∧
    flow.preStateRoot = input.obligation.preStateRoot ∧
    flow.postStateRoot = input.obligation.postStateRoot

/-- Both flows must carry this leaf's exact source transition coordinates. -/
def TokenomicsSourceBound (input : Input) (flow : SpotFlow) : Prop :=
  flow.tokenomicsSourcePreStateRoot = input.authority.preStateRoot ∧
    flow.tokenomicsSourcePostStateRoot =
      tokenomicsStateCommitment (acceptedPostState input) ∧
    flow.tokenomicsSourceEffectPlanRoot = effectsCommitment (acceptedEffects input) ∧
    flow.tokenomicsSourceJournalRoot = input.authority.sourceJournalRoot ∧
    flow.tokenomicsSourceReceiptBindingRoot = input.authority.sourceReceiptBindingRoot ∧
    flow.tokenomicsSourcePreStateRoot ≠ flow.tokenomicsSourcePostStateRoot

def GuardHolds (input : Input) : RejectCode -> Prop
  | .authorityMalformed =>
      0 < input.authority.chainId ∧
        0 < input.authority.deploymentId ∧
        0 < input.authority.profileRoot ∧
        0 < input.authority.routeReleaseId ∧
        0 < input.authority.tokenomicsModuleReleaseId ∧
        0 < input.authority.spotModuleReleaseId ∧
        0 < input.authority.occurrenceId ∧
        0 < input.authority.preStateRoot ∧
        0 < input.authority.oracleRegistryRoot ∧
        0 < input.authority.oracleOccurrenceId ∧
        0 < input.authority.spotReleaseCommitment ∧
        0 < input.authority.spotExecutionPolicyCommitment ∧
        0 < input.authority.spotPricePolicyCommitment ∧
        0 < input.authority.routeSafeQuoteLimitBindingRoot ∧
        0 < input.authority.sourceJournalRoot ∧
        0 < input.authority.sourceReceiptBindingRoot
  | .releaseMismatch =>
      input.authority.release.moduleReleaseId =
          input.authority.tokenomicsModuleReleaseId ∧
        input.authority.release.routeReleaseId = input.authority.routeReleaseId ∧
        input.authority.release.spotModuleReleaseId =
          input.authority.spotModuleReleaseId ∧
        input.authority.tokenomicsModuleReleaseId = approvedTokenomicsModuleReleaseId ∧
        input.authority.routeReleaseId = approvedRouteReleaseId ∧
        input.authority.spotModuleReleaseId = approvedSpotModuleReleaseId ∧
        0 < input.authority.release.minimumQuoteSpendAtoms ∧
        0 < input.authority.release.minimumIntervalBlocks ∧
        input.authority.release.minimumQuoteSpendAtoms ≤
          input.authority.release.perCommandQuoteCapAtoms ∧
        0 < input.authority.release.destinationPrincipalBase ∧
        0 < input.authority.release.zdexBurnPrincipal ∧
        input.authority.release.feeIngressPrincipal ≠
          input.authority.release.feeResiduePrincipal
  | .profileMismatch =>
      ProfileAuthorizationSelfConsistent input.authority.profileAuthorization ∧
        input.authority.profileAuthorization.profileId = input.authority.profileRoot ∧
        input.authority.profileAuthorization.chainId = input.authority.chainId ∧
        input.authority.profileAuthorization.deploymentId =
          input.authority.deploymentId ∧
        input.authority.profileAuthorization.routeReleaseId =
          input.authority.routeReleaseId ∧
        input.authority.profileAuthorization.tokenomicsModuleReleaseId =
          input.authority.tokenomicsModuleReleaseId ∧
        input.authority.profileAuthorization.spotModuleReleaseId =
          input.authority.spotModuleReleaseId ∧
        input.authority.profileAuthorization.releaseCommitment =
          releaseCommitment input.authority.release ∧
        input.authority.profileAuthorization.feePolicyCommitment =
          feeAllocationPolicyCommitment input.authority.policy
  | .stateCommitmentMismatch =>
      input.authority.preStateRoot = tokenomicsStateCommitment input.preState
  | .policyMismatch =>
      FeeAllocationPolicyBounded input.authority.policy ∧
        input.preState.policyRoot = feeAllocationPolicyCommitment input.authority.policy
  | .laneMalformed => TokenomicsStateWellFormed input.authority.policy input.preState
  | .zeroFee => 0 < feeCharged input
  | .cadenceIneligible => CadenceEligible input
  | .arithmeticOutOfRange => ArithmeticFits input
  | .amountOutOfRange =>
      0 < quoteSpend input ∧
        0 < purchasedZDEX input ∧
        purchasedZDEX input < input.preState.liveSupplyAtoms ∧
        quoteSpend input ≤ input.preState.ownedAndCustodiedAtoms ∧
        0 < input.authority.routeSafeQuoteLimitAtoms
  | .minimumSpendMismatch =>
      input.authority.release.minimumQuoteSpendAtoms ≤ quoteSpend input
  | .terminalObligationMismatch =>
      input.obligation.kind = .mustBurnPurchasedZDEX ∧
        input.obligation.burnDomain = .zdexTokenSupply ∧
        input.obligation.lane = .spotLiquidity ∧
        input.obligation.consumerModuleReleaseId =
          input.authority.tokenomicsModuleReleaseId ∧
        input.obligation.burnAsset = input.preState.zdexAsset ∧
        input.obligation.burnPrincipal = input.authority.release.zdexBurnPrincipal ∧
        input.obligation.chainId = input.authority.chainId ∧
        input.obligation.deploymentId = input.authority.deploymentId ∧
        input.obligation.profileId = input.authority.profileRoot ∧
        input.obligation.writerEpoch = input.authority.writerEpoch ∧
        input.obligation.occurrenceId = input.authority.occurrenceId ∧
        input.obligation.routeReleaseId = input.authority.routeReleaseId ∧
        input.obligation.spotModuleReleaseId = input.authority.spotModuleReleaseId ∧
        input.obligation.tokenomicsModuleReleaseId =
          input.authority.tokenomicsModuleReleaseId ∧
        input.obligation.spotReleaseCommitment =
          input.authority.spotReleaseCommitment ∧
        input.obligation.executionPolicyCommitment =
          input.authority.spotExecutionPolicyCommitment ∧
        input.obligation.pricePolicyCommitment =
          input.authority.spotPricePolicyCommitment ∧
        input.obligation.oracleRegistryRoot = input.authority.oracleRegistryRoot ∧
        input.obligation.oracleOccurrenceId = input.authority.oracleOccurrenceId ∧
        0 < input.obligation.obligationId ∧
        0 < input.obligation.purchasedAtoms ∧
        input.obligation.preStateRoot ≠ input.obligation.postStateRoot
  | .purchasedPortMismatch =>
      input.purchasedFlow.role = .purchasedZDEXOutput ∧
        Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment input.purchasedFlow =
          input.obligation.purchasedOutputFlowId ∧
        input.purchasedFlow.asset = input.preState.zdexAsset ∧
        input.purchasedFlow.destinationPrincipal = input.obligation.burnPrincipal ∧
        input.purchasedFlow.amountAtoms = input.obligation.purchasedAtoms ∧
        SpotFlowAuthorityBound input input.purchasedFlow ∧
        TokenomicsSourceBound input input.purchasedFlow
  | .quotePortMismatch =>
      input.quoteFlow.role = .quoteInput ∧
        Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment input.quoteFlow =
          input.obligation.quoteInputFlowId ∧
        input.quoteFlow.asset = input.preState.quoteAsset ∧
        input.quoteFlow.sourcePrincipal =
          destinationPrincipal input.authority.release .buyback ∧
        input.quoteFlow.amountAtoms = quoteSpend input ∧
        input.quoteFlow.destinationPrincipal ≠ input.purchasedFlow.sourcePrincipal ∧
        SpotFlowAuthorityBound input input.quoteFlow ∧
        TokenomicsSourceBound input input.quoteFlow

instance guardDecidable (input : Input) (code : RejectCode) :
    Decidable (GuardHolds input code) := by
  cases code <;>
    simp only [GuardHolds, TokenomicsStateWellFormed, FeeAllocationPolicyBounded,
      ProfileAuthorizationSelfConsistent, ArithmeticFits, FitsU64, FitsU128,
      FitsI127Magnitude, SpotFlowAuthorityBound, TokenomicsSourceBound] <;>
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
    firstReject input = none ↔ Valid input :=
  firstFailing_none_iff input rejectOrder

/-- A reported code is the first failed guard in the declared order. -/
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

/-! ## Total deterministic transition -/

inductive Result where
  | accepted
      (postState : TokenomicsState)
      (effects : TokenomicsEffects)
      (journal : Journal)
      (discharge : ObligationDischarge)
      (routeObligationId : Nat)
  | rejected (code : RejectCode)
  deriving DecidableEq, Repr

def Result.postState (preState : TokenomicsState) : Result -> TokenomicsState
  | .accepted postState _ _ _ _ => postState
  | .rejected _ => preState

def Result.effects : Result -> TokenomicsEffects
  | .accepted _ effects _ _ _ => effects
  | .rejected _ => TokenomicsEffects.empty

def Result.discharge : Result -> Option ObligationDischarge
  | .accepted _ _ _ discharge _ => some discharge
  | .rejected _ => none

def Result.routeObligationId : Result -> Nat
  | .accepted _ _ _ _ routeObligationId => routeObligationId
  | .rejected _ => 0

def transition (input : Input) : Result :=
  match firstReject input with
  | some code => .rejected code
  | none => .accepted
      (acceptedPostState input)
      (acceptedEffects input)
      (acceptedJournal input)
      (acceptedDischarge input)
      (routeCoordinationObligationId input)

theorem transition_is_total (input : Input) :
    (∃ post effects journal discharge routeObligationId,
      transition input = .accepted post effects journal discharge routeObligationId) ∨
      (∃ code, transition input = .rejected code) := by
  unfold transition
  cases hReject : firstReject input with
  | none => exact Or.inl ⟨_, _, _, _, _, rfl⟩
  | some code => exact Or.inr ⟨code, rfl⟩

/-- Rejection is an exact no-op: identical state, no effect rows, no lane
write, no consumed object, no discharge, and no residual route obligation. -/
theorem rejected_is_exact_noop
    (input : Input) (code : RejectCode)
    (hRejected : transition input = .rejected code) :
    (transition input).postState input.preState = input.preState ∧
      (transition input).effects = TokenomicsEffects.empty ∧
      (transition input).discharge = none ∧
      (transition input).routeObligationId = 0 := by
  rw [hRejected]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem accepted_iff
    (input : Input) (post : TokenomicsState) (effects : TokenomicsEffects)
    (journal : Journal) (discharge : ObligationDischarge) (routeObligationId : Nat) :
    transition input = .accepted post effects journal discharge routeObligationId ↔
      firstReject input = none ∧
        post = acceptedPostState input ∧
        effects = acceptedEffects input ∧
        journal = acceptedJournal input ∧
        discharge = acceptedDischarge input ∧
        routeObligationId = routeCoordinationObligationId input := by
  unfold transition
  cases hReject : firstReject input with
  | none => simp [eq_comm]
  | some code => simp

theorem accepted_implies_valid
    {input : Input} {post : TokenomicsState} {effects : TokenomicsEffects}
    {journal : Journal} {discharge : ObligationDischarge} {routeObligationId : Nat}
    (hAccepted :
      transition input = .accepted post effects journal discharge routeObligationId) :
    Valid input := by
  rw [accepted_iff] at hAccepted
  exact (firstReject_none_iff input).mp hAccepted.1

/-! ## Guard accessors -/

theorem valid_policy_bounded {input : Input} (hValid : Valid input) :
    FeeAllocationPolicyBounded input.authority.policy :=
  (valid_guard hValid .policyMismatch).1

theorem valid_lane_well_formed {input : Input} (hValid : Valid input) :
    TokenomicsStateWellFormed input.authority.policy input.preState :=
  valid_guard hValid .laneMalformed

theorem valid_fee_positive {input : Input} (hValid : Valid input) :
    0 < feeCharged input :=
  valid_guard hValid .zeroFee

theorem valid_amounts {input : Input} (hValid : Valid input) :
    0 < quoteSpend input ∧
      0 < purchasedZDEX input ∧
      purchasedZDEX input < input.preState.liveSupplyAtoms ∧
      quoteSpend input ≤ input.preState.ownedAndCustodiedAtoms ∧
      0 < input.authority.routeSafeQuoteLimitAtoms :=
  valid_guard hValid .amountOutOfRange

theorem valid_cadence {input : Input} (hValid : Valid input) :
    CadenceEligible input :=
  valid_guard hValid .cadenceIneligible

/-! ## Exact fee allocation, reserve, spend, burn, and supply accounting -/

/-- The charged fee splits exactly into the buyback allocation, every other
governed destination, and the explicitly carried residue. -/
theorem accepted_transition_conserves_fee
    {input : Input} (hValid : Valid input) :
    feeCharged input =
      buybackAllocation input + otherAllocations input + carriedResidue input :=
  accepted_fee_conservation input (valid_policy_bounded hValid)

/-- The derived spend never exceeds the reserve joined by the same command, the
per-command cap, or the authenticated route-safe limit. -/
theorem accepted_spend_respects_every_governed_limit (input : Input) :
    quoteSpend input ≤ availableReserve input ∧
      quoteSpend input ≤ input.authority.release.perCommandQuoteCapAtoms ∧
      quoteSpend input ≤ input.authority.routeSafeQuoteLimitAtoms := by
  refine ⟨?_, ?_, ?_⟩
  · exact Proofs.ZDEXBuybackSpendV1.selected_le_available _ _ _
  · exact Proofs.ZDEXBuybackSpendV1.selected_le_per_command_cap _ _ _
  · exact Proofs.ZDEXBuybackSpendV1.selected_le_route_safe_limit _ _ _

/-- `B1 = B0 + b - q` with no truncation, and the equivalent additive form. -/
theorem accepted_buyback_reserve_transition (input : Input) :
    (acceptedPostState input).destinationBalances.buyback + quoteSpend input =
        buybackReservePre input + buybackAllocation input ∧
      (acceptedPostState input).destinationBalances.buyback =
        buybackReservePre input + buybackAllocation input - quoteSpend input := by
  have hBound : quoteSpend input ≤ buybackReservePre input + buybackAllocation input :=
    Proofs.ZDEXBuybackSpendV1.selected_le_available _ _ _
  have hPost : (acceptedPostState input).destinationBalances.buyback =
      buybackReservePre input + buybackAllocation input - quoteSpend input := rfl
  rw [hPost]
  omega

/-- The route-selected spend is exactly the amount the Spot quote port carries. -/
theorem accepted_quote_port_carries_the_derived_spend
    {input : Input} (hValid : Valid input) :
    input.quoteFlow.amountAtoms = quoteSpend input :=
  (valid_guard hValid .quotePortMismatch).2.2.2.2.1

/-- One amount appears in five independent places: the Spot purchased-ZDEX
value port, the terminal obligation being discharged, the discharge record, the
magnitude of the emitted burn effect, and the live-supply decrease. -/
theorem accepted_purchased_equals_burned
    {input : Input} (hValid : Valid input) :
    input.purchasedFlow.amountAtoms = purchasedZDEX input ∧
      input.obligation.purchasedAtoms = purchasedZDEX input ∧
      (acceptedDischarge input).burnedAtoms = purchasedZDEX input ∧
      (burnRow input).deltaAtoms = -(purchasedZDEX input : Int) ∧
      input.preState.liveSupplyAtoms -
        (acceptedPostState input).liveSupplyAtoms = purchasedZDEX input := by
  have hPort := (valid_guard hValid .purchasedPortMismatch).2.2.2.2.1
  obtain ⟨_, _, hBurnBelowSupply, _, _⟩ := valid_amounts hValid
  refine ⟨rfl, hPort.symm, rfl, rfl, ?_⟩
  have hPost : (acceptedPostState input).liveSupplyAtoms =
      input.preState.liveSupplyAtoms - purchasedZDEX input := rfl
  rw [hPost]
  omega

/-- Live supply falls by exactly the burned amount and stays representable. -/
theorem accepted_supply_reduction_is_exact
    {input : Input} (hValid : Valid input) :
    (acceptedPostState input).liveSupplyAtoms + purchasedZDEX input =
        input.preState.liveSupplyAtoms ∧
      (acceptedPostState input).liveSupplyAtoms =
        input.preState.liveSupplyAtoms - purchasedZDEX input ∧
      0 < (acceptedPostState input).liveSupplyAtoms := by
  obtain ⟨_, _, hBurnBelowSupply, _, _⟩ := valid_amounts hValid
  have hPost : (acceptedPostState input).liveSupplyAtoms =
      input.preState.liveSupplyAtoms - purchasedZDEX input := rfl
  rw [hPost]
  omega

/-- The only quote atoms that leave this lane are the governed spend. -/
theorem accepted_tokenomics_quote_conservation
    {input : Input} (hValid : Valid input) :
    (acceptedPostState input).selectedBalanceAtoms + quoteSpend input =
      input.preState.selectedBalanceAtoms := by
  have hAllocated : allocatedTotal input ≤ feeCharged input :=
    allocated_total_le_fee input (valid_policy_bounded hValid)
  have hSpend : quoteSpend input ≤ buybackReservePre input + buybackAllocation input :=
    Proofs.ZDEXBuybackSpendV1.selected_le_available _ _ _
  have hFee : feeCharged input = input.preState.feeIngressAtoms := rfl
  have hReservePre :
      buybackReservePre input = input.preState.destinationBalances.buyback := rfl
  have hResidue : carriedResidue input = feeCharged input - allocatedTotal input := rfl
  have hTotal : allocatedTotal input =
      buybackAllocation input + (allocations input).qualifiedHostPool +
        (allocations input).treasury + (allocations input).proofRewards +
        (allocations input).coverReserve + (allocations input).lpRebates := rfl
  have hPost : (acceptedPostState input).selectedBalanceAtoms =
      (input.preState.feeIngressAtoms - feeCharged input) +
        (input.preState.unallocatedResidueAtoms + carriedResidue input) +
        ((buybackReservePre input + buybackAllocation input - quoteSpend input) +
          (input.preState.destinationBalances.qualifiedHostPool +
            (allocations input).qualifiedHostPool) +
          (input.preState.destinationBalances.treasury + (allocations input).treasury) +
          (input.preState.destinationBalances.proofRewards +
            (allocations input).proofRewards) +
          (input.preState.destinationBalances.coverReserve +
            (allocations input).coverReserve) +
          (input.preState.destinationBalances.lpRebates +
            (allocations input).lpRebates)) := rfl
  have hPre : input.preState.selectedBalanceAtoms =
      input.preState.feeIngressAtoms + input.preState.unallocatedResidueAtoms +
        (input.preState.destinationBalances.buyback +
          input.preState.destinationBalances.qualifiedHostPool +
          input.preState.destinationBalances.treasury +
          input.preState.destinationBalances.proofRewards +
          input.preState.destinationBalances.coverReserve +
          input.preState.destinationBalances.lpRebates) := rfl
  rw [hPost, hPre]
  omega

/-- Owned custody and the selected balance fall by the same governed spend, so
the lane ownership invariant survives the transition. -/
theorem accepted_preserves_lane_well_formedness
    {input : Input} (hValid : Valid input) :
    TokenomicsStateWellFormed input.authority.policy (acceptedPostState input) := by
  obtain ⟨hPolicyRoot, hQuoteAsset, hZdexAsset, hDistinct, hOwned, hSupply,
    hStaking, hHost, hTreasury, hProof, hCover, hLp⟩ := valid_lane_well_formed hValid
  obtain ⟨_, _, hBurnBelowSupply, hSpendOwned, _⟩ := valid_amounts hValid
  have hConserved := accepted_tokenomics_quote_conservation hValid
  refine ⟨hPolicyRoot, hQuoteAsset, hZdexAsset, hDistinct, ?_, ?_,
    hStaking, hHost, hTreasury, hProof, hCover, hLp⟩
  · have hOwnedPost : (acceptedPostState input).ownedAndCustodiedAtoms =
        input.preState.ownedAndCustodiedAtoms - quoteSpend input := rfl
    rw [hOwnedPost]
    omega
  · have hSupplyPost : (acceptedPostState input).liveSupplyAtoms =
        input.preState.liveSupplyAtoms - purchasedZDEX input := rfl
    rw [hSupplyPost]
    omega

/-- Cadence is decided by consensus height and advances to the executed height. -/
theorem accepted_cadence_advances_to_the_execution_height
    {input : Input} (hValid : Valid input) :
    (acceptedPostState input).lastExecutionHeight = some input.authority.currentHeight ∧
      ∀ previous, input.preState.lastExecutionHeight = some previous ->
        previous + input.authority.release.minimumIntervalBlocks ≤
          input.authority.currentHeight := by
  refine ⟨rfl, ?_⟩
  intro previous hPrevious
  have hCadence := valid_cadence hValid
  unfold CadenceEligible Proofs.ZDEXBuybackSpendV1.cadenceEligible at hCadence
  rw [hPrevious] at hCadence
  exact hCadence.2

/-- Every state component this command does not own is preserved exactly. -/
theorem accepted_preserves_unrelated_tokenomics_commitments (input : Input) :
    (acceptedPostState input).quoteAsset = input.preState.quoteAsset ∧
      (acceptedPostState input).zdexAsset = input.preState.zdexAsset ∧
      (acceptedPostState input).policyRoot = input.preState.policyRoot ∧
      (acceptedPostState input).quoteAssetSupplyAtoms =
        input.preState.quoteAssetSupplyAtoms ∧
      (acceptedPostState input).stakingRoot = input.preState.stakingRoot ∧
      (acceptedPostState input).hostClaimsRoot = input.preState.hostClaimsRoot ∧
      (acceptedPostState input).treasuryClaimsRoot = input.preState.treasuryClaimsRoot ∧
      (acceptedPostState input).proofRewardsRoot = input.preState.proofRewardsRoot ∧
      (acceptedPostState input).coverReserveRoot = input.preState.coverReserveRoot ∧
      (acceptedPostState input).lpRebatesRoot = input.preState.lpRebatesRoot :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Committed ingress is fully consumed, so no partial-spend state survives. -/
theorem accepted_consumes_committed_fee_ingress (input : Input) :
    (acceptedPostState input).feeIngressAtoms = 0 ∧
      (acceptedPostState input).unallocatedResidueAtoms =
        input.preState.unallocatedResidueAtoms + carriedResidue input := by
  refine ⟨?_, rfl⟩
  have hPost : (acceptedPostState input).feeIngressAtoms =
      input.preState.feeIngressAtoms - feeCharged input := rfl
  have hFee : feeCharged input = input.preState.feeIngressAtoms := rfl
  rw [hPost, hFee]
  omega

/-! ## Canonical effect plan

The accepted effect plan is gross rather than netted: the buyback destination
is credited its full allocation and separately debited the governed spend, so
no arithmetic is hidden inside a net row. -/

theorem allocationRows_are_nonzero
    (input : Input) (destination : FeeDestination) (amount : Nat) :
    ∀ row ∈ allocationRows input destination amount, row.deltaAtoms ≠ 0 := by
  unfold allocationRows
  split
  · simp
  · rename_i hAmount
    intro row hMember
    simp only [List.mem_singleton] at hMember
    subst hMember
    show ((amount : Int)) ≠ 0
    omega

theorem residueRows_are_nonzero (input : Input) :
    ∀ row ∈ residueRows input, row.deltaAtoms ≠ 0 := by
  unfold residueRows
  split
  · simp
  · rename_i hResidue
    intro row hMember
    simp only [List.mem_singleton] at hMember
    subst hMember
    show ((carriedResidue input : Int)) ≠ 0
    omega

/-- Every emitted row carries a nonzero magnitude, matching the runtime effect
row type, which forbids a zero delta. -/
theorem accepted_effect_rows_are_nonzero
    {input : Input} (hValid : Valid input) :
    ∀ row ∈ (acceptedEffects input).rows, row.deltaAtoms ≠ 0 := by
  have hFee := valid_fee_positive hValid
  obtain ⟨hSpend, hPurchased, _, _, _⟩ := valid_amounts hValid
  intro row hMember
  simp only [acceptedEffects, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hMember
  rcases hMember with rfl | hMember
  · show (-(feeCharged input : Int)) ≠ 0
    omega
  rcases hMember with hMember | hTail
  · rcases hMember with hAllocation | hResidue
    · rcases hAllocation with ((((hRow | hRow) | hRow) | hRow) | hRow) | hRow <;>
        exact allocationRows_are_nonzero input _ _ row hRow
    · exact residueRows_are_nonzero input row hResidue
  · rcases hTail with rfl | rfl
    · show (-(quoteSpend input : Int)) ≠ 0
      omega
    · show (-(purchasedZDEX input : Int)) ≠ 0
      omega

/-- Every emitted row whose kind is a burn is the single derived burn row, so
no fee row can be relabelled into a supply burn and no second burn can appear.
Spot pool reserves are unreachable from here because this effect vocabulary
declares no Spot accounting domain. -/
theorem accepted_emits_a_single_burn_row (input : Input) :
    ∀ row ∈ (acceptedEffects input).rows, row.kind = .burn -> row = burnRow input := by
  have hAllocation :
      ∀ (row : EffectRow) destination amount,
        row ∈ allocationRows input destination amount -> row.kind = .feeAllocation := by
    intro row destination amount hRow
    unfold allocationRows at hRow
    split at hRow
    · simp at hRow
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hRow
      subst hRow
      rfl
  intro row hMember hBurn
  simp only [acceptedEffects, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hMember
  rcases hMember with rfl | hMember
  · simp [feeIngressRow] at hBurn
  rcases hMember with hMember | hTail
  · rcases hMember with hAllocationRow | hResidue
    · rcases hAllocationRow with ((((hRow | hRow) | hRow) | hRow) | hRow) | hRow <;>
        rw [hAllocation row _ _ hRow] at hBurn <;> simp at hBurn
    · unfold residueRows at hResidue
      split at hResidue
      · simp at hResidue
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hResidue
        subst hResidue
        simp at hBurn
  · rcases hTail with rfl | rfl
    · simp [buybackSpendRow] at hBurn
    · rfl

/-- The quote asset only ever moves between tokenomics accounting locations,
and the ZDEX asset is only ever burned. -/
theorem accepted_effect_rows_use_declared_assets (input : Input) :
    ∀ row ∈ (acceptedEffects input).rows,
      (row.accountingDomain = .zdexSupply ∧ row.asset = input.preState.zdexAsset ∧
          row.kind = .burn) ∨
        (row.accountingDomain ≠ .zdexSupply ∧
          row.asset = input.preState.quoteAsset) := by
  intro row hMember
  have hAllocation :
      ∀ destination amount, row ∈ allocationRows input destination amount ->
        row.accountingDomain ≠ .zdexSupply ∧ row.asset = input.preState.quoteAsset := by
    intro destination amount hRow
    unfold allocationRows at hRow
    split at hRow
    · simp at hRow
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hRow
      subst hRow
      exact ⟨by simp, rfl⟩
  simp only [acceptedEffects, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hMember
  rcases hMember with rfl | hMember
  · exact Or.inr ⟨by simp [feeIngressRow], rfl⟩
  rcases hMember with hMember | hTail
  · rcases hMember with hAllocationRow | hResidue
    · rcases hAllocationRow with ((((hRow | hRow) | hRow) | hRow) | hRow) | hRow <;>
        exact Or.inr (hAllocation _ _ hRow)
    · unfold residueRows at hResidue
      split at hResidue
      · simp at hResidue
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hResidue
        subst hResidue
        exact Or.inr ⟨by simp, rfl⟩
  · rcases hTail with rfl | rfl
    · exact Or.inr ⟨by simp [buybackSpendRow], rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩

/-- Exactly one lane write, on this lane, bound to the exact pre and post roots.
ABI V1 forbids persistent consumed objects, so the tuple stays empty. -/
theorem accepted_emits_one_bound_tokenomics_lane_write (input : Input) :
    (acceptedEffects input).laneWrites =
        [{ lane := .zdexTokenomics
           preStateRoot := input.authority.preStateRoot
           postStateRoot := tokenomicsStateCommitment (acceptedPostState input) }] ∧
      (acceptedEffects input).consumedObjectIds = [] :=
  ⟨rfl, rfl⟩

/-- The gross fee-allocation and spend rows for the buyback destination net to
exactly `b - q` while remaining individually auditable. -/
theorem accepted_buyback_rows_are_gross_not_netted (input : Input) :
    (buybackSpendRow input).deltaAtoms = -(quoteSpend input : Int) ∧
      allocationRows input .buyback (allocations input).buyback =
        (if (allocations input).buyback = 0 then [] else
          [{ kind := .feeAllocation
             accountingDomain := .feeDestination
             asset := input.preState.quoteAsset
             principal := destinationPrincipal input.authority.release .buyback
             deltaAtoms := ((allocations input).buyback : Int) }]) :=
  ⟨rfl, rfl⟩

/-! ## Realizable dependency order

The Spot leaf consumes this leaf's post-state root and effect-plan root inside
its quote port, then derives the terminal obligation. Both derived roots must
therefore be independent of the obligation this leaf later discharges, or the
composed route would require a fixpoint. -/

theorem post_state_is_independent_of_the_consumed_obligation
    (input : Input) (obligation : SpotObligation) :
    acceptedPostState { input with obligation := obligation } =
      acceptedPostState input := rfl

theorem effect_plan_root_is_independent_of_the_consumed_obligation
    (input : Input) (obligation : SpotObligation) :
    effectsCommitment (acceptedEffects { input with obligation := obligation }) =
      effectsCommitment (acceptedEffects input) := rfl

theorem derived_spend_is_independent_of_both_spot_ports
    (input : Input) (quoteFlow purchasedFlow : SpotFlow) :
    quoteSpend { input with quoteFlow := quoteFlow, purchasedFlow := purchasedFlow } =
      quoteSpend input := rfl

/-! ## Terminal discharge and the residual coordination obligation -/

def dischargeCommitment (discharge : ObligationDischarge) : Root :=
  encodeNats [
    discharge.obligationId,
    discharge.obligationCommitment,
    Proofs.ZDEXSpotBuybackTransitionV1.terminalObligationKindCode discharge.kind,
    Proofs.ZDEXSpotBuybackTransitionV1.burnDomainCode discharge.burnDomain,
    discharge.consumerModuleReleaseId,
    discharge.burnAsset,
    discharge.burnPrincipal,
    discharge.burnedAtoms,
    discharge.quoteInputFlowId,
    discharge.purchasedOutputFlowId
  ]

/-- The accepted result discharges exactly the `MUST_BURN_PURCHASED_ZDEX`
obligation the Spot leaf created, naming this lane as its consumer and burning
the exact purchased amount. -/
theorem accepted_discharges_the_exact_spot_obligation
    {input : Input} (hValid : Valid input) :
    (acceptedDischarge input).obligationId = input.obligation.obligationId ∧
      0 < (acceptedDischarge input).obligationId ∧
      (acceptedDischarge input).obligationCommitment =
        Proofs.ZDEXSpotBuybackTransitionV1.terminalObligationFullCommitment
          input.obligation ∧
      (acceptedDischarge input).kind = .mustBurnPurchasedZDEX ∧
      (acceptedDischarge input).burnDomain = .zdexTokenSupply ∧
      (acceptedDischarge input).consumerModuleReleaseId =
        input.authority.tokenomicsModuleReleaseId ∧
      (acceptedDischarge input).burnAsset = input.preState.zdexAsset ∧
      (acceptedDischarge input).burnPrincipal =
        input.authority.release.zdexBurnPrincipal ∧
      (acceptedDischarge input).burnedAtoms = purchasedZDEX input ∧
      (acceptedEffects input).dischargedObligationIds = [input.obligation.obligationId] := by
  have hObligation := valid_guard hValid .terminalObligationMismatch
  obtain ⟨hKind, hDomain, _, hConsumer, hAsset, hPrincipal, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hIdPositive, _, _⟩ := hObligation
  exact ⟨rfl, hIdPositive, rfl, hKind, hDomain, hConsumer, hAsset, hPrincipal, rfl, rfl⟩

/-- Discharging the Spot burn obligation does not close route composition: an
accepted result still carries a nonzero coordination obligation, and a rejected
one carries none. -/
theorem accepted_route_obligation_is_nonzero
    {input : Input} {post : TokenomicsState} {effects : TokenomicsEffects}
    {journal : Journal} {discharge : ObligationDischarge} {routeObligationId : Nat}
    (hAccepted :
      transition input = .accepted post effects journal discharge routeObligationId) :
    0 < routeObligationId := by
  rw [accepted_iff] at hAccepted
  rw [hAccepted.2.2.2.2.2]
  exact routeCoordinationObligationId_is_nonzero input

/-! ## Journal binding -/

/-- The journal repeats no independent value. Every economic field is the exact
derived quantity, and every root is the exact accepted commitment. -/
theorem accepted_journal_binds_exact_transition (input : Input) :
    (acceptedJournal input).preStateRoot = input.authority.preStateRoot ∧
      (acceptedJournal input).postStateRoot =
        tokenomicsStateCommitment (acceptedPostState input) ∧
      (acceptedJournal input).effectPlanRoot =
        effectsCommitment (acceptedEffects input) ∧
      (acceptedJournal input).feeChargedAtoms = feeCharged input ∧
      (acceptedJournal input).buybackAllocationAtoms = buybackAllocation input ∧
      (acceptedJournal input).otherAllocationAtoms = otherAllocations input ∧
      (acceptedJournal input).carriedResidueAtoms = carriedResidue input ∧
      (acceptedJournal input).quoteSpendAtoms = quoteSpend input ∧
      (acceptedJournal input).purchasedAtoms = purchasedZDEX input ∧
      (acceptedJournal input).buybackReservePreAtoms = buybackReservePre input ∧
      (acceptedJournal input).buybackReservePostAtoms = buybackReservePost input ∧
      (acceptedJournal input).liveSupplyPreAtoms = input.preState.liveSupplyAtoms ∧
      (acceptedJournal input).liveSupplyPostAtoms =
        (acceptedPostState input).liveSupplyAtoms ∧
      (acceptedJournal input).dischargedObligationId = input.obligation.obligationId ∧
      (acceptedJournal input).routeCoordinationObligationId =
        routeCoordinationObligationId input ∧
      (acceptedJournal input).executionHeight = input.authority.currentHeight ∧
      (acceptedJournal input).consumedObjectIds = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The journalled fee split satisfies the conservation equation directly. -/
theorem accepted_journal_fee_split_conserves
    {input : Input} (hValid : Valid input) :
    (acceptedJournal input).feeChargedAtoms =
      (acceptedJournal input).buybackAllocationAtoms +
        (acceptedJournal input).otherAllocationAtoms +
        (acceptedJournal input).carriedResidueAtoms :=
  accepted_transition_conserves_fee hValid

/-! ## Concrete witnesses

The fixtures mirror the existing research fee-allocation candidate: 2,000 bps
buyback, 0 bps qualified host pool, 3,000 bps treasury, 1,000 bps proof
rewards, 1,000 bps cover reserve, 500 bps LP rebates, and 2,500 bps carried as
explicit residue. The purchased amount reuses the 111-atom exact CPMM output of
the Spot checkpoint. These numbers are fixture semantics, not selected economic
policy. -/

def nonvacuityPolicy : FeeAllocationPolicy where
  buybackBps := 2_000
  qualifiedHostPoolBps := 0
  treasuryBps := 3_000
  proofRewardsBps := 1_000
  coverReserveBps := 1_000
  lpRebatesBps := 500

def nonvacuityRelease : TokenomicsBuybackRelease where
  moduleReleaseId := approvedTokenomicsModuleReleaseId
  routeReleaseId := approvedRouteReleaseId
  spotModuleReleaseId := approvedSpotModuleReleaseId
  perCommandQuoteCapAtoms := 400
  minimumQuoteSpendAtoms := 100
  minimumIntervalBlocks := 50
  feeIngressPrincipal := 501
  feeResiduePrincipal := 502
  destinationPrincipalBase := 600
  zdexBurnPrincipal := 700

def nonvacuityPreState : TokenomicsState where
  quoteAsset := 11
  zdexAsset := 12
  policyRoot := feeAllocationPolicyCommitment nonvacuityPolicy
  feeIngressAtoms := 1_000
  unallocatedResidueAtoms := 25
  destinationBalances :=
    { buyback := 300
      qualifiedHostPool := 10
      treasury := 20
      proofRewards := 30
      coverReserve := 40
      lpRebates := 50 }
  ownedAndCustodiedAtoms := 2_000
  quoteAssetSupplyAtoms := 5_000
  liveSupplyAtoms := 1_000_000
  lastExecutionHeight := some 100
  stakingRoot := 901
  hostClaimsRoot := 902
  treasuryClaimsRoot := 903
  proofRewardsRoot := 904
  coverReserveRoot := 905
  lpRebatesRoot := 906

def nonvacuityAuthorization : ProfileAuthorization :=
  makeProfileAuthorization 7 9 approvedRouteReleaseId approvedTokenomicsModuleReleaseId
    approvedSpotModuleReleaseId nonvacuityRelease nonvacuityPolicy

def nonvacuityAuthority : AuthorityContext where
  chainId := 7
  deploymentId := 9
  profileRoot := nonvacuityAuthorization.profileId
  writerEpoch := 3
  routeReleaseId := approvedRouteReleaseId
  tokenomicsModuleReleaseId := approvedTokenomicsModuleReleaseId
  spotModuleReleaseId := approvedSpotModuleReleaseId
  occurrenceId := 4_242
  preStateRoot := tokenomicsStateCommitment nonvacuityPreState
  currentHeight := 160
  oracleRegistryRoot := 8_001
  oracleOccurrenceId := 8_002
  spotReleaseCommitment := 8_101
  spotExecutionPolicyCommitment := 8_102
  spotPricePolicyCommitment := 8_103
  routeSafeQuoteLimitAtoms := 450
  routeSafeQuoteLimitBindingRoot := 8_104
  sourceJournalRoot := 8_105
  sourceReceiptBindingRoot := 8_106
  release := nonvacuityRelease
  policy := nonvacuityPolicy
  profileAuthorization := nonvacuityAuthorization

def nonvacuityObligation : SpotObligation where
  obligationId := 91_011
  kind := .mustBurnPurchasedZDEX
  burnDomain := .zdexTokenSupply
  chainId := 7
  deploymentId := 9
  profileId := nonvacuityAuthorization.profileId
  writerEpoch := 3
  occurrenceId := 4_242
  preStateRoot := 7_001
  postStateRoot := 7_002
  routeReleaseId := approvedRouteReleaseId
  spotModuleReleaseId := approvedSpotModuleReleaseId
  tokenomicsModuleReleaseId := approvedTokenomicsModuleReleaseId
  spotReleaseCommitment := 8_101
  executionPolicyCommitment := 8_102
  pricePolicyCommitment := 8_103
  oracleRegistryRoot := 8_001
  oracleOccurrenceId := 8_002
  lane := .spotLiquidity
  consumerModuleReleaseId := approvedTokenomicsModuleReleaseId
  burnAsset := 12
  burnPrincipal := 700
  selectedPoolId := 6_001
  quoteInputFlowId := 0
  purchasedOutputFlowId := 0
  purchasedAtoms := 111

def nonvacuityQuoteFlowBase : SpotFlow where
  role := .quoteInput
  chainId := 7
  deploymentId := 9
  profileId := nonvacuityAuthorization.profileId
  writerEpoch := 3
  commandOccurrenceId := 4_242
  preStateRoot := 7_001
  postStateRoot := 7_002
  routeReleaseId := approvedRouteReleaseId
  spotModuleReleaseId := approvedSpotModuleReleaseId
  tokenomicsModuleReleaseId := approvedTokenomicsModuleReleaseId
  spotReleaseCommitment := 8_101
  executionPolicyCommitment := 8_102
  pricePolicyCommitment := 8_103
  oracleRegistryRoot := 8_001
  oracleOccurrenceId := 8_002
  tokenomicsSourcePreStateRoot := 0
  tokenomicsSourcePostStateRoot := 0
  tokenomicsSourceEffectPlanRoot := 0
  tokenomicsSourceJournalRoot := 0
  tokenomicsSourceReceiptBindingRoot := 0
  selectedPoolId := 6_001
  asset := 11
  sourcePrincipal := 601
  destinationPrincipal := 6_101
  amountAtoms := 0

def nonvacuityPurchasedFlowBase : SpotFlow :=
  { nonvacuityQuoteFlowBase with
    role := .purchasedZDEXOutput
    asset := 12
    sourcePrincipal := 6_102
    destinationPrincipal := 700
    amountAtoms := 111 }

def nonvacuityBaseInput : Input where
  authority := nonvacuityAuthority
  preState := nonvacuityPreState
  obligation := nonvacuityObligation
  quoteFlow := nonvacuityQuoteFlowBase
  purchasedFlow := nonvacuityPurchasedFlowBase

/-- Bind the Spot ports to this leaf's derived source coordinates. The result
is a fixpoint because the derived post-state and effect-plan roots depend on no
field this function rewrites. -/
def bindPorts (input : Input) : Input :=
  let sourcePostRoot := tokenomicsStateCommitment (acceptedPostState input)
  let sourceEffectRoot := effectsCommitment (acceptedEffects input)
  let quoteFlow : SpotFlow :=
    { input.quoteFlow with
      amountAtoms := quoteSpend input
      tokenomicsSourcePreStateRoot := input.authority.preStateRoot
      tokenomicsSourcePostStateRoot := sourcePostRoot
      tokenomicsSourceEffectPlanRoot := sourceEffectRoot
      tokenomicsSourceJournalRoot := input.authority.sourceJournalRoot
      tokenomicsSourceReceiptBindingRoot := input.authority.sourceReceiptBindingRoot }
  let purchasedFlow : SpotFlow :=
    { input.purchasedFlow with
      tokenomicsSourcePreStateRoot := input.authority.preStateRoot
      tokenomicsSourcePostStateRoot := sourcePostRoot
      tokenomicsSourceEffectPlanRoot := sourceEffectRoot
      tokenomicsSourceJournalRoot := input.authority.sourceJournalRoot
      tokenomicsSourceReceiptBindingRoot := input.authority.sourceReceiptBindingRoot }
  { input with
    quoteFlow := quoteFlow
    purchasedFlow := purchasedFlow
    obligation :=
      { input.obligation with
        quoteInputFlowId :=
          Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment quoteFlow
        purchasedOutputFlowId :=
          Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment purchasedFlow } }

/-! ### Port binding is a one-step fixpoint

Each lemma is proved on a variable input, so the definitional check is purely
structural. Instantiating them keeps the concrete fixtures out of commitment
arithmetic. -/

theorem bindPorts_preserves_pre_state (input : Input) :
    (bindPorts input).preState = input.preState := rfl

theorem bindPorts_preserves_authority (input : Input) :
    (bindPorts input).authority = input.authority := rfl

theorem bindPorts_preserves_post_state (input : Input) :
    acceptedPostState (bindPorts input) = acceptedPostState input := rfl

theorem bindPorts_preserves_effect_plan_root (input : Input) :
    effectsCommitment (acceptedEffects (bindPorts input)) =
      effectsCommitment (acceptedEffects input) := rfl

theorem bindPorts_preserves_quote_spend (input : Input) :
    quoteSpend (bindPorts input) = quoteSpend input := rfl

theorem bindPorts_preserves_purchased (input : Input) :
    purchasedZDEX (bindPorts input) = purchasedZDEX input := rfl

theorem bindPorts_quote_flow_is_bound (input : Input) :
    Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment (bindPorts input).quoteFlow =
      (bindPorts input).obligation.quoteInputFlowId := rfl

theorem bindPorts_purchased_flow_is_bound (input : Input) :
    Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment
        (bindPorts input).purchasedFlow =
      (bindPorts input).obligation.purchasedOutputFlowId := rfl

theorem bindPorts_quote_source_bound (input : Input)
    (hAdvances : input.authority.preStateRoot ≠
      tokenomicsStateCommitment (acceptedPostState input)) :
    TokenomicsSourceBound (bindPorts input) (bindPorts input).quoteFlow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  show input.authority.preStateRoot ≠
    tokenomicsStateCommitment (acceptedPostState input)
  exact hAdvances

theorem bindPorts_purchased_source_bound (input : Input)
    (hAdvances : input.authority.preStateRoot ≠
      tokenomicsStateCommitment (acceptedPostState input)) :
    TokenomicsSourceBound (bindPorts input) (bindPorts input).purchasedFlow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  show input.authority.preStateRoot ≠
    tokenomicsStateCommitment (acceptedPostState input)
  exact hAdvances

theorem bindPorts_quote_flow_carries_derived_spend (input : Input) :
    (bindPorts input).quoteFlow.amountAtoms = quoteSpend (bindPorts input) := rfl

def withPreState (input : Input) (preState : TokenomicsState) : Input :=
  { input with
    preState := preState
    authority :=
      { input.authority with preStateRoot := tokenomicsStateCommitment preState } }

def withPolicy (input : Input) (policy : FeeAllocationPolicy) : Input :=
  let authorization := makeProfileAuthorization
    input.authority.chainId input.authority.deploymentId
    input.authority.routeReleaseId input.authority.tokenomicsModuleReleaseId
    input.authority.spotModuleReleaseId input.authority.release policy
  { input with
    authority :=
      { input.authority with
        policy := policy
        profileAuthorization := authorization
        profileRoot := authorization.profileId } }

def nonvacuityInput : Input := bindPorts nonvacuityBaseInput

/-- Cadence accepts the exact governed boundary height. -/
def cadenceBoundaryInput : Input :=
  bindPorts
    { nonvacuityBaseInput with
      authority := { nonvacuityAuthority with currentHeight := 150 } }

/-- A four-atom fee allocates one treasury atom and carries three atoms as
residue; every other destination share floors to zero. -/
def roundedFeeInput : Input :=
  bindPorts (withPreState nonvacuityBaseInput
    { nonvacuityPreState with feeIngressAtoms := 4 })

theorem valid_of_guards (input : Input)
    (hAuthority : GuardHolds input .authorityMalformed)
    (hRelease : GuardHolds input .releaseMismatch)
    (hProfile : GuardHolds input .profileMismatch)
    (hStateRoot : GuardHolds input .stateCommitmentMismatch)
    (hPolicy : GuardHolds input .policyMismatch)
    (hLane : GuardHolds input .laneMalformed)
    (hFee : GuardHolds input .zeroFee)
    (hCadence : GuardHolds input .cadenceIneligible)
    (hArithmetic : GuardHolds input .arithmeticOutOfRange)
    (hAmount : GuardHolds input .amountOutOfRange)
    (hMinimum : GuardHolds input .minimumSpendMismatch)
    (hObligation : GuardHolds input .terminalObligationMismatch)
    (hPurchased : GuardHolds input .purchasedPortMismatch)
    (hQuote : GuardHolds input .quotePortMismatch) :
    Valid input := by
  intro code hMember
  simp only [rejectOrder, List.mem_cons, List.not_mem_nil, or_false] at hMember
  rcases hMember with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    assumption

set_option maxRecDepth 4000 in
theorem nonvacuity_valid : Valid nonvacuityInput :=
  valid_of_guards nonvacuityInput
    (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
    ⟨by decide, rfl⟩
    ⟨rfl, by decide⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, by decide, by decide, by decide⟩
    ⟨rfl, bindPorts_purchased_flow_is_bound _, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_purchased_source_bound nonvacuityBaseInput (by decide)⟩
    ⟨rfl, bindPorts_quote_flow_is_bound _, rfl, rfl,
      bindPorts_quote_flow_carries_derived_spend _, by decide,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_quote_source_bound nonvacuityBaseInput (by decide)⟩

theorem nonvacuity_first_reject_is_none : firstReject nonvacuityInput = none :=
  (firstReject_none_iff nonvacuityInput).mpr nonvacuity_valid

theorem nonvacuity_accepts :
    transition nonvacuityInput = .accepted
      (acceptedPostState nonvacuityInput)
      (acceptedEffects nonvacuityInput)
      (acceptedJournal nonvacuityInput)
      (acceptedDischarge nonvacuityInput)
      (routeCoordinationObligationId nonvacuityInput) := by
  simp only [transition, nonvacuity_first_reject_is_none]

/-- Every governed quantity of the accepted fixture is the exact derived value. -/
theorem nonvacuity_derived_values :
    feeCharged nonvacuityInput = 1_000 ∧
      buybackAllocation nonvacuityInput = 200 ∧
      otherAllocations nonvacuityInput = 550 ∧
      carriedResidue nonvacuityInput = 250 ∧
      quoteSpend nonvacuityInput = 400 ∧
      buybackReservePre nonvacuityInput = 300 ∧
      buybackReservePost nonvacuityInput = 100 ∧
      purchasedZDEX nonvacuityInput = 111 ∧
      (acceptedPostState nonvacuityInput).liveSupplyAtoms = 999_889 ∧
      (acceptedPostState nonvacuityInput).feeIngressAtoms = 0 ∧
      (acceptedPostState nonvacuityInput).unallocatedResidueAtoms = 275 := by
  decide

set_option maxRecDepth 4000 in
theorem cadence_boundary_is_live :
    firstReject cadenceBoundaryInput = none := by
  refine (firstReject_none_iff cadenceBoundaryInput).mpr ?_
  exact valid_of_guards cadenceBoundaryInput
    (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
    ⟨by decide, rfl⟩
    ⟨rfl, by decide⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, by decide, by decide, by decide⟩
    ⟨rfl, bindPorts_purchased_flow_is_bound _, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_purchased_source_bound { nonvacuityBaseInput with
      authority := { nonvacuityAuthority with currentHeight := 150 } } (by decide)⟩
    ⟨rfl, bindPorts_quote_flow_is_bound _, rfl, rfl,
      bindPorts_quote_flow_carries_derived_spend _, by decide,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_quote_source_bound { nonvacuityBaseInput with
      authority := { nonvacuityAuthority with currentHeight := 150 } } (by decide)⟩

set_option maxRecDepth 4000 in
theorem rounded_fee_fixture_is_live :
    feeCharged roundedFeeInput = 4 ∧
      buybackAllocation roundedFeeInput = 0 ∧
      carriedResidue roundedFeeInput = 3 ∧
      quoteSpend roundedFeeInput = 300 ∧
      allocationRows roundedFeeInput .buyback (allocations roundedFeeInput).buyback = [] ∧
      firstReject roundedFeeInput = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  refine (firstReject_none_iff roundedFeeInput).mpr ?_
  exact valid_of_guards roundedFeeInput
    (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
    ⟨by decide, rfl⟩
    ⟨rfl, by decide⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, by decide, by decide, by decide⟩
    ⟨rfl, bindPorts_purchased_flow_is_bound _, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_purchased_source_bound (withPreState nonvacuityBaseInput
    { nonvacuityPreState with feeIngressAtoms := 4 }) (by decide)⟩
    ⟨rfl, bindPorts_quote_flow_is_bound _, rfl, rfl,
      bindPorts_quote_flow_carries_derived_spend _, by decide,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      bindPorts_quote_source_bound (withPreState nonvacuityBaseInput
    { nonvacuityPreState with feeIngressAtoms := 4 }) (by decide)⟩

/-! ## One concrete witness per rejection family -/

def authorityMalformedInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with chainId := 0 } }

def releaseMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        release := { nonvacuityRelease with minimumIntervalBlocks := 0 } } }

def profileMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        profileAuthorization := { nonvacuityAuthorization with chainId := 8 } } }

def stateCommitmentMismatchInput : Input :=
  { nonvacuityInput with
    authority :=
      { nonvacuityAuthority with
        preStateRoot := nonvacuityAuthority.preStateRoot + 1 } }

def policyMismatchInput : Input :=
  withPolicy nonvacuityInput { nonvacuityPolicy with buybackBps := 9_000 }

def laneMalformedInput : Input :=
  withPreState nonvacuityInput { nonvacuityPreState with stakingRoot := 0 }

def zeroFeeInput : Input :=
  withPreState nonvacuityInput { nonvacuityPreState with feeIngressAtoms := 0 }

def cadenceIneligibleInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentHeight := 149 } }

def arithmeticOutOfRangeInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with currentHeight := maxU64 + 1 } }

def amountOutOfRangeInput : Input :=
  { nonvacuityInput with
    purchasedFlow := { nonvacuityInput.purchasedFlow with amountAtoms := 0 } }

def minimumSpendMismatchInput : Input :=
  { nonvacuityInput with
    authority := { nonvacuityAuthority with routeSafeQuoteLimitAtoms := 50 } }

def terminalObligationMismatchInput : Input :=
  { nonvacuityInput with
    obligation :=
      { nonvacuityInput.obligation with consumerModuleReleaseId := 9_999 } }

/-- A substituted burn principal must not be discharged against this lane. -/
def purchasedPortMismatchInput : Input :=
  { nonvacuityInput with
    purchasedFlow :=
      { nonvacuityInput.purchasedFlow with destinationPrincipal := 701 } }

/-- A quote port that claims any amount other than the governed spend. -/
def quotePortMismatchInput : Input :=
  { nonvacuityInput with
    quoteFlow := { nonvacuityInput.quoteFlow with amountAtoms := 399 } }

set_option maxRecDepth 20000 in
theorem authority_malformed_witness_rejects :
    firstReject authorityMalformedInput = some .authorityMalformed := by
  decide

set_option maxRecDepth 20000 in
theorem release_mismatch_witness_rejects :
    firstReject releaseMismatchInput = some .releaseMismatch := by
  decide

set_option maxRecDepth 20000 in
theorem profile_mismatch_witness_rejects :
    firstReject profileMismatchInput = some .profileMismatch := by
  decide

set_option maxRecDepth 20000 in
theorem state_commitment_mismatch_witness_rejects :
    firstReject stateCommitmentMismatchInput = some .stateCommitmentMismatch := by
  decide

set_option maxRecDepth 20000 in
theorem policy_mismatch_witness_rejects :
    firstReject policyMismatchInput = some .policyMismatch := by
  have encodeNats_cons_positive (value : Nat) (rest : List Nat) :
      0 < encodeNats (value :: rest) := by
    change 0 < Nat.pair value (encodeNats rest) + 1
    omega
  have hProfileRootPositive : 0 < policyMismatchInput.authority.profileRoot := by
    unfold policyMismatchInput withPolicy makeProfileAuthorization deriveProfileId
    exact encodeNats_cons_positive _ _
  have hAuthority : GuardHolds policyMismatchInput .authorityMalformed := by
    rcases valid_guard nonvacuity_valid .authorityMalformed with
      ⟨hChain, hDeployment, _, hRoute, hTokenomics, hSpot, hOccurrence,
        hPreState, hOracleRegistry, hOracleOccurrence, hSpotRelease,
        hExecutionPolicy, hPricePolicy, hQuoteLimit, hJournal, hReceipt⟩
    exact ⟨hChain, hDeployment, hProfileRootPositive, hRoute, hTokenomics, hSpot,
      hOccurrence, hPreState, hOracleRegistry, hOracleOccurrence, hSpotRelease,
      hExecutionPolicy, hPricePolicy, hQuoteLimit, hJournal, hReceipt⟩
  have hRelease : GuardHolds policyMismatchInput .releaseMismatch :=
    valid_guard nonvacuity_valid .releaseMismatch
  have hProfile : GuardHolds policyMismatchInput .profileMismatch := by
    refine ⟨makeProfileAuthorization_is_self_consistent _ _ _ _ _ _ _, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hState : GuardHolds policyMismatchInput .stateCommitmentMismatch :=
    valid_guard nonvacuity_valid .stateCommitmentMismatch
  have hPolicy : ¬GuardHolds policyMismatchInput .policyMismatch := by
    intro hGuard
    have hBounded := hGuard.1
    norm_num [FeeAllocationPolicyBounded, FeeAllocationPolicy.assignedBasisPoints,
      policyMismatchInput, withPolicy, nonvacuityPolicy,
      basisPointsDenominator] at hBounded
  unfold firstReject rejectOrder
  simp only [firstFailing]
  rw [if_pos hAuthority, if_pos hRelease, if_pos hProfile, if_pos hState,
    if_neg hPolicy]

set_option maxRecDepth 20000 in
theorem lane_malformed_witness_rejects :
    firstReject laneMalformedInput = some .laneMalformed := by
  decide

set_option maxRecDepth 20000 in
theorem zero_fee_witness_rejects :
    firstReject zeroFeeInput = some .zeroFee := by
  decide

set_option maxRecDepth 20000 in
theorem cadence_ineligible_witness_rejects :
    firstReject cadenceIneligibleInput = some .cadenceIneligible := by
  decide

set_option maxRecDepth 20000 in
theorem arithmetic_out_of_range_witness_rejects :
    firstReject arithmeticOutOfRangeInput = some .arithmeticOutOfRange := by
  decide

set_option maxRecDepth 20000 in
theorem amount_out_of_range_witness_rejects :
    firstReject amountOutOfRangeInput = some .amountOutOfRange := by
  decide

set_option maxRecDepth 20000 in
theorem minimum_spend_mismatch_witness_rejects :
    firstReject minimumSpendMismatchInput = some .minimumSpendMismatch := by
  decide

/-- A consumer that is not this tokenomics module cannot discharge the burn. -/
theorem terminal_obligation_substitution_is_rejected :
    ¬GuardHolds terminalObligationMismatchInput .terminalObligationMismatch ∧
      firstReject terminalObligationMismatchInput ≠ none := by
  have hFail :
      ¬GuardHolds terminalObligationMismatchInput .terminalObligationMismatch := by
    intro hGuard
    exact absurd hGuard.2.2.2.1 (by decide)
  refine ⟨hFail, ?_⟩
  intro hNone
  exact hFail ((firstReject_none_iff _).mp hNone _ (by decide))

/-- The two port families are stated as guard failures plus rejection. Their
reported position is not machine-evaluated because deciding it would require
evaluating the Spot flow-identity commitment, whose exact natural-number
encoding is outside the kernel-checkable domain at this width. -/
theorem purchased_port_substitution_is_rejected :
    ¬GuardHolds purchasedPortMismatchInput .purchasedPortMismatch ∧
      firstReject purchasedPortMismatchInput ≠ none := by
  have hFail : ¬GuardHolds purchasedPortMismatchInput .purchasedPortMismatch := by
    intro hGuard
    exact absurd hGuard.2.2.2.1 (by decide)
  refine ⟨hFail, ?_⟩
  intro hNone
  exact hFail ((firstReject_none_iff _).mp hNone _ (by decide))

theorem quote_port_amount_substitution_is_rejected :
    ¬GuardHolds quotePortMismatchInput .quotePortMismatch ∧
      firstReject quotePortMismatchInput ≠ none := by
  have hFail : ¬GuardHolds quotePortMismatchInput .quotePortMismatch := by
    intro hGuard
    exact absurd hGuard.2.2.2.2.1 (by decide)
  refine ⟨hFail, ?_⟩
  intro hNone
  exact hFail ((firstReject_none_iff _).mp hNone _ (by decide))

theorem rejected_witness_is_an_exact_noop :
    (transition purchasedPortMismatchInput).effects = TokenomicsEffects.empty ∧
      (transition purchasedPortMismatchInput).discharge = none ∧
      (transition purchasedPortMismatchInput).routeObligationId = 0 := by
  cases hFirst : firstReject purchasedPortMismatchInput with
  | none => exact absurd hFirst purchased_port_substitution_is_rejected.2
  | some code =>
      have hTransition : transition purchasedPortMismatchInput = .rejected code := by
        unfold transition
        rw [hFirst]
      rw [hTransition]
      exact ⟨rfl, rfl, rfl⟩

/-- A flow from another command occurrence cannot alias an accepted port. -/
theorem command_occurrence_separates_the_quote_flow :
    Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment
        nonvacuityInput.quoteFlow ≠
      Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment
        { nonvacuityInput.quoteFlow with commandOccurrenceId := 4_243 } := by
  intro hEqual
  have hFlow :=
    Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment_injective hEqual
  have hOccurrence := congrArg
    Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity.commandOccurrenceId hFlow
  change (4_242 : Nat) = 4_243 at hOccurrence
  omega

/-! ## Exact pairing with the Spot leaf

These conditional refinement lemmas derive exact field equalities when the
tokenomics leaf consumes precisely the ports and terminal obligation produced
by a Spot input for the same occurrence. They do not construct a jointly valid
Spot/tokenomics witness or establish receipt-authenticated route composition. -/

theorem route_ports_are_exactly_paired
    {spotInput : Proofs.ZDEXSpotBuybackTransitionV1.Input} {tokenomicsInput : Input}
    (hValid : Valid tokenomicsInput)
    (hQuoteFlow : tokenomicsInput.quoteFlow =
      Proofs.ZDEXSpotBuybackTransitionV1.acceptedQuoteInputFlow spotInput)
    (hPurchasedFlow : tokenomicsInput.purchasedFlow =
      Proofs.ZDEXSpotBuybackTransitionV1.acceptedPurchasedOutputFlow spotInput) :
    spotInput.quotePort.amountAtoms = quoteSpend tokenomicsInput ∧
      Proofs.ZDEXSpotBuybackTransitionV1.purchasedZDEX spotInput =
        purchasedZDEX tokenomicsInput ∧
      spotInput.quotePort.sourcePostStateRoot =
        tokenomicsStateCommitment (acceptedPostState tokenomicsInput) ∧
      spotInput.quotePort.sourceEffectPlanRoot =
        effectsCommitment (acceptedEffects tokenomicsInput) := by
  have hQuoteGuard := valid_guard hValid .quotePortMismatch
  rcases hQuoteGuard with
    ⟨_, _, _, _, hAmount, _, _, hSource⟩
  have hQuoteAmount := congrArg
    Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity.amountAtoms hQuoteFlow
  have hPurchasedAmount := congrArg
    Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity.amountAtoms hPurchasedFlow
  have hSourcePost := congrArg
    Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity.tokenomicsSourcePostStateRoot
    hQuoteFlow
  have hSourceEffects := congrArg
    Proofs.ZDEXSpotBuybackTransitionV1.FlowIdentity.tokenomicsSourceEffectPlanRoot
    hQuoteFlow
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hQuoteAmount.symm.trans hAmount
  · exact hPurchasedAmount.symm
  · exact hSourcePost.symm.trans hSource.2.1
  · exact hSourceEffects.symm.trans hSource.2.2.1

/-- Live ZDEX supply falls by exactly the amount the Spot leaf purchased. -/
theorem route_supply_reduction_matches_spot_output
    {spotInput : Proofs.ZDEXSpotBuybackTransitionV1.Input} {tokenomicsInput : Input}
    (hValid : Valid tokenomicsInput)
    (hPurchasedFlow : tokenomicsInput.purchasedFlow =
      Proofs.ZDEXSpotBuybackTransitionV1.acceptedPurchasedOutputFlow spotInput) :
    (acceptedPostState tokenomicsInput).liveSupplyAtoms +
        Proofs.ZDEXSpotBuybackTransitionV1.purchasedZDEX spotInput =
      tokenomicsInput.preState.liveSupplyAtoms := by
  have hSupply := (accepted_supply_reduction_is_exact hValid).1
  have hPaired : Proofs.ZDEXSpotBuybackTransitionV1.purchasedZDEX spotInput =
      purchasedZDEX tokenomicsInput := by
    show _ = tokenomicsInput.purchasedFlow.amountAtoms
    rw [hPurchasedFlow]
    rfl
  rw [hPaired]
  exact hSupply

/-- If both inputs carry the same Spot-issued obligation and purchased flow,
the derived discharge fields reproduce the exact obligation id and amount. -/
theorem route_discharges_the_spot_issued_obligation
    {spotInput : Proofs.ZDEXSpotBuybackTransitionV1.Input} {tokenomicsInput : Input}
    (hObligation : tokenomicsInput.obligation =
      Proofs.ZDEXSpotBuybackTransitionV1.acceptedTerminalObligation spotInput)
    (hPurchasedFlow : tokenomicsInput.purchasedFlow =
      Proofs.ZDEXSpotBuybackTransitionV1.acceptedPurchasedOutputFlow spotInput) :
    (acceptedDischarge tokenomicsInput).obligationId =
        (Proofs.ZDEXSpotBuybackTransitionV1.acceptedTerminalObligation
          spotInput).obligationId ∧
      (acceptedDischarge tokenomicsInput).burnedAtoms =
        (Proofs.ZDEXSpotBuybackTransitionV1.acceptedTerminalObligation
          spotInput).purchasedAtoms := by
  refine ⟨?_, ?_⟩
  · show tokenomicsInput.obligation.obligationId =
      (Proofs.ZDEXSpotBuybackTransitionV1.acceptedTerminalObligation
        spotInput).obligationId
    rw [hObligation]
  show tokenomicsInput.purchasedFlow.amountAtoms =
    Proofs.ZDEXSpotBuybackTransitionV1.purchasedZDEX spotInput
  rw [hPurchasedFlow]
  rfl

end ZDEXTokenomicsBuybackTransitionV1
end Proofs
