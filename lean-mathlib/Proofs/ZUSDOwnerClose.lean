import Mathlib.Tactic

/-!
# zUSD Liquity V1 owner-close transition core

This module is a bounded, pure model of the unmounted F04/F21 owner-close
transition.  Unsigned source values use `Fin (2^256)`.  An active vault carries
proofs that its net debt is at least `1800e18`, its reserve is exactly `200e18`,
and its composite debt fits in the source domain.  Every accepted transition is
certificate-carrying; rejection commits the supplied prestate.

The modeled behavior is pinned to Liquity V1 commit
`8f52f2906f99414c0b1c3a84c95c74c319b7a8c6`:

* `BorrowerOperations.sol` SHA-256
  `b4108d5e529a3bb3ffb1f9a865c8653024e07c5949aa8f6964799fbd2dc03a65`;
* `TroveManager.sol` SHA-256
  `0b0ba14dc297938b98aa7f130924b3525706fa6b3736fa663c72c40f483f1895`;
* `Dependencies/LiquityBase.sol` SHA-256
  `a290cf752c79d305a02a6d8d357d36a8f105fd1b63582b1c3d08e3f1e34bae2a`;
* `LUSDToken.sol` SHA-256
  `d51c34e6b5b779da4ec2016fac2261d93432b8ea67cf76d31fbf677acb659969`.

The source `closeTrove` path applies pending rewards before reading debt and
collateral, requires Normal Mode and a candidate TCR at least the `150%` CCR,
removes one stake and sorted-list member, marks `closedByOwner`, burns owner net
debt plus the `200e18` Gas Pool reserve, and returns all collateral.  The source
manager also forbids closing the last active trove.
`LUSDToken.transfer` permits transfers to the Gas Pool.  Consequently the
aggregate Gas Pool invariant is a lower bound; donated excess is valid state.
The active-count reserve floor is a ZenoDEX reachability invariant derived from
the pinned fixed-reserve mint, close, liquidation, and transfer behavior; it is
not presented as a direct `closeTrove` source guard.

## Scope and explicit nonclaims

The checked claims cover bounded arithmetic, source constants, lossless
fourteen-reason guard coverage, reject-is-no-op, dependent accepted-result
binding, exact burns, collateral return, aggregate debt/supply equality,
stake/index decrement, terminal status, and concrete nonvacuity.  The witnesses
close scoped model defects CE-094, CE-095, CE-096, CE-097, CE-098, CE-101,
CE-103, CE-104, CE-105, CE-106, and CE-108: derived risk mode, dependent
result construction,
remaining-debt and collateral floors, zero-debt branch order, donation-tolerant
reserve custody, removal of cumulative-history admission, explicit positive
count, positive typed target identity, lifecycle/effect occurrence binding, and
post-close removal of the target-reserve association.

CE-103 intentionally leaves cumulative burn history out of admission state.
The exact per-transition burn remains certificate-bound; historical totals are
non-authorizing replay or chunk aggregates.  CE-107 UI split-open funding and
F04 reachability are outside this owner-close transition and are not claimed.
Python or Rust refinement, caller
authentication, pending-reward calculation/application, external/runtime vault
identity extraction and serialization binding, concrete sorted-list predecessor
and successor links, root/decision provenance, canonical serialization, and
atomic F15/F16 commit or outbox application remain external obligations.  A
theorem in this module does not authorize a runtime close until those bindings
are checked.
-/

namespace ZenoDEX.ZUSDOwnerClose

def u256Modulus : Nat := 2 ^ 256

/-- Unsigned 256-bit source value; out-of-range values are unrepresentable. -/
abbrev U256 := Fin u256Modulus

def atomsScale : Nat := 10 ^ 18

def liquityV1GasReserveAtoms : Nat := 200 * atomsScale

def liquityV1MinNetDebtAtoms : Nat := 1800 * atomsScale

def liquityV1MinCompositeDebtAtoms : Nat :=
  liquityV1MinNetDebtAtoms + liquityV1GasReserveAtoms

def liquityV1CCRE18 : Nat := 1_500_000_000_000_000_000

def u256Zero : U256 :=
  ⟨0, by simp [u256Modulus]⟩

def u256One : U256 :=
  ⟨1, by norm_num [u256Modulus]⟩

def u256Two : U256 :=
  ⟨2, by norm_num [u256Modulus]⟩

def u256Max : U256 :=
  ⟨u256Modulus - 1, Nat.sub_lt (by simp [u256Modulus]) (by omega)⟩

/-- Exact subtraction after the corresponding underflow guard. -/
def subtractExact (left right : U256) (_h : right.val ≤ left.val) : U256 :=
  ⟨left.val - right.val,
    lt_of_le_of_lt (Nat.sub_le left.val right.val) left.isLt⟩

/-- Exact addition after the corresponding U256 capacity guard. -/
def addExact (left right : U256)
    (h : left.val + right.val < u256Modulus) : U256 :=
  ⟨left.val + right.val, h⟩

/-- Runtime-shaped vault identity; zero is unrepresentable. -/
structure VaultIdentity where
  value : U256
  positive : 0 < value.val
  deriving DecidableEq

def vaultIdentityOne : VaultIdentity :=
  ⟨u256One, by norm_num [u256One, u256Modulus]⟩

def vaultIdentityTwo : VaultIdentity :=
  ⟨u256Two, by norm_num [u256Two, u256Modulus]⟩

theorem vault_identity_value_ne_zero (identity : VaultIdentity) :
    identity.value ≠ u256Zero := by
  intro hZero
  have hPositive := identity.positive
  rw [hZero] at hPositive
  simp [u256Zero] at hPositive

/-- Liquity V1 F04 active occurrence with source-fixed debt shape. -/
structure ActiveVault where
  identity : VaultIdentity
  collateral : U256
  netDebt : U256
  reserveDebt : U256
  stake : U256
  collateralPositive : 0 < collateral.val
  netDebtAtLeastSourceMinimum : liquityV1MinNetDebtAtoms ≤ netDebt.val
  reserveIsSourceConstant : reserveDebt.val = liquityV1GasReserveAtoms
  compositeDebtFits : netDebt.val + reserveDebt.val < u256Modulus

def compositeDebt (vault : ActiveVault) : U256 :=
  ⟨vault.netDebt.val + vault.reserveDebt.val, vault.compositeDebtFits⟩

/-- Typed reserve ownership; amount equality alone cannot bind a source vault. -/
structure TargetReserveBinding where
  targetVaultIdentity : VaultIdentity
  amount : U256
  deriving DecidableEq

def expectedTargetReserve (vault : ActiveVault) : TargetReserveBinding :=
  {
    targetVaultIdentity := vault.identity
    amount := vault.reserveDebt
  }

theorem expected_target_reserve_binds_identity_and_amount
    (vault : ActiveVault) :
    (expectedTargetReserve vault).targetVaultIdentity = vault.identity ∧
      (expectedTargetReserve vault).amount = vault.reserveDebt := by
  exact ⟨rfl, rfl⟩

/-- Closed-by-owner carries no active vault value fields. -/
inductive VaultLifecycle where
  | active (vault : ActiveVault) (targetReserve : TargetReserveBinding)
  | closedByOwner (vaultIdentity : VaultIdentity) (closeOccurrence : U256)

/-- F04/F17/F21 aggregate projection owned by the scoped model. -/
structure OwnerCloseState where
  lifecycle : VaultLifecycle
  systemCollateral : U256
  systemCompositeDebt : U256
  totalActiveStake : U256
  activeVaultAndIndexCount : U256
  ownerZUSDBalance : U256
  ownerCollateralBalance : U256
  gasPoolCustody : U256
  totalZUSDSupply : U256
  transitionSequence : U256

/-- Lifecycle-indexed target projection; a closed occurrence has no target slot. -/
def targetReserve (state : OwnerCloseState) : Option TargetReserveBinding :=
  match state.lifecycle with
  | .active _ binding => some binding
  | .closedByOwner _ _ => none

/-- CE-108 construction law: lifecycle and reserve variant are exhaustive. -/
theorem lifecycle_target_reserve_exact_partition (state : OwnerCloseState) :
    (∃ vault binding,
        state.lifecycle = .active vault binding ∧
          targetReserve state = some binding) ∨
      (∃ identity occurrence,
        state.lifecycle = .closedByOwner identity occurrence ∧
          targetReserve state = none) := by
  cases hLifecycle : state.lifecycle with
  | active vault binding =>
      left
      exact ⟨vault, binding, rfl, by simp [targetReserve, hLifecycle]⟩
  | closedByOwner identity occurrence =>
      right
      exact ⟨identity, occurrence, rfl, by simp [targetReserve, hLifecycle]⟩

inductive RiskMode where
  | normal
  | recovery
  deriving DecidableEq, Repr

/-- Trusted decision projections supplied to the pure model. -/
structure CloseVaultRequest where
  targetVaultIdentity : VaultIdentity
  authorityMatchesOwner : Bool
  walletMatchesOwner : Bool
  modeSystemCollateral : U256
  modeSystemCompositeDebt : U256
  candidateSystemCollateral : U256
  candidateSystemCompositeDebt : U256
  priceE18 : U256
  pricePositive : 0 < priceE18.val
  systemNumeratorFitsWhenDebtPositive :
    modeSystemCompositeDebt.val ≠ 0 →
    modeSystemCollateral.val * priceE18.val < u256Modulus
  candidateNumeratorFitsWhenDebtPositive :
    candidateSystemCompositeDebt.val ≠ 0 →
    candidateSystemCollateral.val * priceE18.val < u256Modulus
  contextCurrent : Bool

def activeTarget
    (pre : OwnerCloseState) (request : CloseVaultRequest) : Option ActiveVault :=
  match pre.lifecycle with
  | .active vault _binding =>
      if request.targetVaultIdentity = vault.identity then some vault else none
  | .closedByOwner _ _ => none

def aggregateUnderflowGuardsPass
    (pre : OwnerCloseState) (vault : ActiveVault) : Prop :=
  vault.collateral.val ≤ pre.systemCollateral.val ∧
    (compositeDebt vault).val ≤ pre.systemCompositeDebt.val ∧
    vault.stake.val ≤ pre.totalActiveStake.val ∧
    (compositeDebt vault).val ≤ pre.totalZUSDSupply.val

instance instDecidableAggregateUnderflowGuardsPass
    (pre : OwnerCloseState) (vault : ActiveVault) :
    Decidable (aggregateUnderflowGuardsPass pre vault) := by
  unfold aggregateUnderflowGuardsPass
  infer_instance

def accountingCapacityGuardsPass
    (pre : OwnerCloseState) (vault : ActiveVault) : Prop :=
  pre.ownerCollateralBalance.val + vault.collateral.val < u256Modulus ∧
    pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms < u256Modulus

instance instDecidableAccountingCapacityGuardsPass
    (pre : OwnerCloseState) (vault : ActiveVault) :
    Decidable (accountingCapacityGuardsPass pre vault) := by
  unfold accountingCapacityGuardsPass
  infer_instance

def candidateAggregateIsExact
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (vault : ActiveVault) : Prop :=
  request.candidateSystemCollateral.val =
      pre.systemCollateral.val - vault.collateral.val ∧
    request.candidateSystemCompositeDebt.val =
      pre.systemCompositeDebt.val - (compositeDebt vault).val ∧
    0 < pre.activeVaultAndIndexCount.val ∧
    (pre.activeVaultAndIndexCount.val - 1) *
        liquityV1MinCompositeDebtAtoms ≤
      request.candidateSystemCompositeDebt.val ∧
    pre.activeVaultAndIndexCount.val - 1 ≤
      request.candidateSystemCollateral.val ∧
    pre.totalZUSDSupply.val = pre.systemCompositeDebt.val ∧
    pre.ownerZUSDBalance.val ≤ pre.totalZUSDSupply.val ∧
    pre.gasPoolCustody.val ≤ pre.totalZUSDSupply.val ∧
    pre.ownerZUSDBalance.val + pre.gasPoolCustody.val ≤
      pre.totalZUSDSupply.val

instance instDecidableCandidateAggregateIsExact
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (vault : ActiveVault) :
    Decidable (candidateAggregateIsExact pre request vault) := by
  unfold candidateAggregateIsExact
  infer_instance

/-- Liquity's integer TCR classifier, including the zero-debt Normal case. -/
def tcrAtOrAboveCCR
    (collateral compositeDebtValue priceE18 : U256) : Prop :=
  compositeDebtValue.val = 0 ∨
    liquityV1CCRE18 ≤
      collateral.val * priceE18.val / compositeDebtValue.val

instance instDecidableTCRAtOrAboveCCR
    (collateral compositeDebtValue priceE18 : U256) :
    Decidable (tcrAtOrAboveCCR collateral compositeDebtValue priceE18) := by
  unfold tcrAtOrAboveCCR
  infer_instance

def systemTCRAtOrAboveCCR (request : CloseVaultRequest) : Prop :=
  tcrAtOrAboveCCR request.modeSystemCollateral
    request.modeSystemCompositeDebt request.priceE18

instance instDecidableSystemTCRAtOrAboveCCR
    (request : CloseVaultRequest) :
    Decidable (systemTCRAtOrAboveCCR request) := by
  unfold systemTCRAtOrAboveCCR
  infer_instance

def candidateTCRAtOrAboveCCR (request : CloseVaultRequest) : Prop :=
  tcrAtOrAboveCCR request.candidateSystemCollateral
    request.candidateSystemCompositeDebt request.priceE18

instance instDecidableCandidateTCRAtOrAboveCCR
    (request : CloseVaultRequest) :
    Decidable (candidateTCRAtOrAboveCCR request) := by
  unfold candidateTCRAtOrAboveCCR
  infer_instance

/-- CE-094 replacement: mode is derived from arithmetic, never nominal input. -/
def deriveRiskMode (request : CloseVaultRequest) : RiskMode :=
  if systemTCRAtOrAboveCCR request then .normal else .recovery

theorem deriveRiskMode_normal_iff_system_tcr_at_or_above_ccr
    (request : CloseVaultRequest) :
    deriveRiskMode request = .normal ↔ systemTCRAtOrAboveCCR request := by
  unfold deriveRiskMode
  by_cases hNormal : systemTCRAtOrAboveCCR request <;> simp [hNormal]

theorem deriveRiskMode_recovery_iff_system_tcr_below_ccr
    (request : CloseVaultRequest) :
    deriveRiskMode request = .recovery ↔ ¬ systemTCRAtOrAboveCCR request := by
  unfold deriveRiskMode
  by_cases hNormal : systemTCRAtOrAboveCCR request <;> simp [hNormal]

/-- The CE-094 classifier is exhaustive and disjoint. -/
theorem deriveRiskMode_exact_partition (request : CloseVaultRequest) :
    (deriveRiskMode request = .normal ∧
        systemTCRAtOrAboveCCR request ∧
        deriveRiskMode request ≠ .recovery) ∨
      (deriveRiskMode request = .recovery ∧
        ¬ systemTCRAtOrAboveCCR request ∧
        deriveRiskMode request ≠ .normal) := by
  by_cases hNormal : systemTCRAtOrAboveCCR request
  · left
    simp [deriveRiskMode, hNormal]
  · right
    simp [deriveRiskMode, hNormal]

/-- Runtime stale-context binding projected into the scoped arithmetic model. -/
def modeProjectionMatches
    (pre : OwnerCloseState) (request : CloseVaultRequest) : Prop :=
  request.modeSystemCollateral = pre.systemCollateral ∧
    request.modeSystemCompositeDebt = pre.systemCompositeDebt

instance instDecidableModeProjectionMatches
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    Decidable (modeProjectionMatches pre request) := by
  unfold modeProjectionMatches
  infer_instance

/--
CE-098 custody rule.  Exact target binding is required.  Custody below the
target passes this projection so the following insufficiency guard owns that
failure.  Otherwise every active source reserve must be covered, while donated
excess remains admissible.
-/
def reserveProjectionMatches
    (pre : OwnerCloseState) (vault : ActiveVault) : Prop :=
  targetReserve pre = some (expectedTargetReserve vault) ∧
    (pre.gasPoolCustody.val < vault.reserveDebt.val ∨
      (pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms <
          u256Modulus ∧
        pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤
          pre.gasPoolCustody.val))

instance instDecidableReserveProjectionMatches
    (pre : OwnerCloseState) (vault : ActiveVault) :
    Decidable (reserveProjectionMatches pre vault) := by
  unfold reserveProjectionMatches
  infer_instance

/-- The complete conjunction required by an accepted owner close. -/
def Admissible
    (pre : OwnerCloseState) (request : CloseVaultRequest) : Prop :=
  match activeTarget pre request with
  | none => False
  | some vault =>
      request.authorityMatchesOwner = true ∧
        request.walletMatchesOwner = true ∧
        deriveRiskMode request = .normal ∧
        vault.netDebt.val ≤ pre.ownerZUSDBalance.val ∧
        1 < pre.activeVaultAndIndexCount.val ∧
        aggregateUnderflowGuardsPass pre vault ∧
        accountingCapacityGuardsPass pre vault ∧
        candidateAggregateIsExact pre request vault ∧
        candidateTCRAtOrAboveCCR request ∧
        reserveProjectionMatches pre vault ∧
        vault.reserveDebt.val ≤ pre.gasPoolCustody.val ∧
        pre.transitionSequence.val < u256Modulus - 1 ∧
        request.contextCurrent = true ∧
        modeProjectionMatches pre request

instance instDecidableAdmissible
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    Decidable (Admissible pre request) := by
  unfold Admissible
  split <;> infer_instance

/-- Stable runtime reject ABI, in declaration order. -/
inductive OwnerCloseReject where
  | targetVaultInactive
  | wrongVaultOwner
  | ownerWalletBindingMismatch
  | recoveryMode
  | insufficientOwnerNetDebtBalance
  | finalActiveVault
  | candidateAggregateUnderflow
  | candidateAccountingOverflow
  | candidateAggregateInconsistent
  | postCloseTCRBelowCCR
  | reserveCustodyMismatch
  | reserveCustodyInsufficient
  | ownerCloseSequenceExhausted
  | staleOwnerCloseContext
  deriving DecidableEq, Repr

def rejectOrder : List OwnerCloseReject :=
  [.targetVaultInactive,
    .wrongVaultOwner,
    .ownerWalletBindingMismatch,
    .recoveryMode,
    .insufficientOwnerNetDebtBalance,
    .finalActiveVault,
    .candidateAggregateUnderflow,
    .candidateAccountingOverflow,
    .candidateAggregateInconsistent,
    .postCloseTCRBelowCCR,
    .reserveCustodyMismatch,
    .reserveCustodyInsufficient,
    .ownerCloseSequenceExhausted,
    .staleOwnerCloseContext]

def rejectRank : OwnerCloseReject → Nat
  | .targetVaultInactive => 0
  | .wrongVaultOwner => 1
  | .ownerWalletBindingMismatch => 2
  | .recoveryMode => 3
  | .insufficientOwnerNetDebtBalance => 4
  | .finalActiveVault => 5
  | .candidateAggregateUnderflow => 6
  | .candidateAccountingOverflow => 7
  | .candidateAggregateInconsistent => 8
  | .postCloseTCRBelowCCR => 9
  | .reserveCustodyMismatch => 10
  | .reserveCustodyInsufficient => 11
  | .ownerCloseSequenceExhausted => 12
  | .staleOwnerCloseContext => 13

def activeDependentPass
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (predicate : ActiveVault → Bool) : Bool :=
  match activeTarget pre request with
  | none => true
  | some vault => predicate vault

/-- A blocked dependent guard counts as nonfailing, matching the Python ABI. -/
def guardPass
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    OwnerCloseReject → Bool
  | .targetVaultInactive => (activeTarget pre request).isSome
  | .wrongVaultOwner =>
      activeDependentPass pre request fun _ => request.authorityMatchesOwner
  | .ownerWalletBindingMismatch =>
      activeDependentPass pre request fun _ => request.walletMatchesOwner
  | .recoveryMode => decide (deriveRiskMode request = .normal)
  | .insufficientOwnerNetDebtBalance =>
      activeDependentPass pre request fun vault =>
        if request.walletMatchesOwner = true then
          decide (vault.netDebt.val ≤ pre.ownerZUSDBalance.val)
        else
          true
  | .finalActiveVault =>
      activeDependentPass pre request fun _ =>
        decide (1 < pre.activeVaultAndIndexCount.val)
  | .candidateAggregateUnderflow =>
      activeDependentPass pre request fun vault =>
        decide (aggregateUnderflowGuardsPass pre vault)
  | .candidateAccountingOverflow =>
      activeDependentPass pre request fun vault =>
        decide (accountingCapacityGuardsPass pre vault)
  | .candidateAggregateInconsistent =>
      activeDependentPass pre request fun vault =>
        if aggregateUnderflowGuardsPass pre vault ∧
            accountingCapacityGuardsPass pre vault then
          decide (candidateAggregateIsExact pre request vault)
        else
          true
  | .postCloseTCRBelowCCR =>
      activeDependentPass pre request fun vault =>
        if aggregateUnderflowGuardsPass pre vault ∧
            accountingCapacityGuardsPass pre vault ∧
            candidateAggregateIsExact pre request vault then
          decide (candidateTCRAtOrAboveCCR request)
        else
          true
  | .reserveCustodyMismatch =>
      activeDependentPass pre request fun vault =>
        decide (reserveProjectionMatches pre vault)
  | .reserveCustodyInsufficient =>
      activeDependentPass pre request fun vault =>
        decide (vault.reserveDebt.val ≤ pre.gasPoolCustody.val)
  | .ownerCloseSequenceExhausted =>
      decide (pre.transitionSequence.val < u256Modulus - 1)
  | .staleOwnerCloseContext =>
      request.contextCurrent && decide (modeProjectionMatches pre request)

/-- Lossless failures are a stable-order subsequence of the fourteen-reason ABI. -/
def guardFailures
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    List OwnerCloseReject :=
  rejectOrder.filter fun reason => !(guardPass pre request reason)

theorem rejectOrder_has_fourteen_entries : rejectOrder.length = 14 := by
  decide

theorem rejectOrder_has_strict_rank_order :
    rejectOrder.Pairwise fun left right => rejectRank left < rejectRank right := by
  decide

theorem guardFailures_follow_declared_order
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    List.Sublist (guardFailures pre request) rejectOrder := by
  exact List.filter_sublist

/-- The fourteen guards are lossless: an empty failure list is exactly admissibility. -/
theorem guardFailures_eq_nil_iff_admissible
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    guardFailures pre request = [] ↔ Admissible pre request := by
  cases hTarget : activeTarget pre request with
  | none =>
      simp [guardFailures, rejectOrder, guardPass, activeDependentPass,
        Admissible, hTarget]
  | some vault =>
      simp [guardFailures, rejectOrder, guardPass, activeDependentPass,
        Admissible, hTarget]
      intro _hAuthority hWallet _hNormal
      simp [hWallet]
      tauto

/-- Exact data-only effect plan for the future composition shell. -/
structure OwnerCloseEffects where
  vaultIdentity : VaultIdentity
  closeOccurrence : U256
  ownerNetDebtBurn : U256
  gasReserveBurn : U256
  totalZUSDBurn : U256
  systemCompositeDebtDecrease : U256
  collateralReturn : U256
  systemCollateralDecrease : U256
  stakeRemoval : U256
  activeVaultAndIndexCountDecrease : U256

def buildEffects
    (vault : ActiveVault) (closeOccurrence : U256) : OwnerCloseEffects :=
  {
    vaultIdentity := vault.identity
    closeOccurrence := closeOccurrence
    ownerNetDebtBurn := vault.netDebt
    gasReserveBurn := vault.reserveDebt
    totalZUSDBurn := compositeDebt vault
    systemCompositeDebtDecrease := compositeDebt vault
    collateralReturn := vault.collateral
    systemCollateralDecrease := vault.collateral
    stakeRemoval := vault.stake
    activeVaultAndIndexCountDecrease := u256One
  }

def buildPostState
    (pre : OwnerCloseState) (vault : ActiveVault)
    (hBalance : vault.netDebt.val ≤ pre.ownerZUSDBalance.val)
    (hCount : 1 < pre.activeVaultAndIndexCount.val)
    (hUnderflow : aggregateUnderflowGuardsPass pre vault)
    (hCapacity : accountingCapacityGuardsPass pre vault)
    (hReserve : vault.reserveDebt.val ≤ pre.gasPoolCustody.val)
    (hSequence : pre.transitionSequence.val < u256Modulus - 1) :
    OwnerCloseState :=
  let closeOccurrence : U256 :=
    ⟨pre.transitionSequence.val + 1, by omega⟩
  {
    lifecycle := .closedByOwner vault.identity closeOccurrence
    systemCollateral := subtractExact pre.systemCollateral vault.collateral hUnderflow.1
    systemCompositeDebt :=
      subtractExact pre.systemCompositeDebt (compositeDebt vault) hUnderflow.2.1
    totalActiveStake :=
      subtractExact pre.totalActiveStake vault.stake hUnderflow.2.2.1
    activeVaultAndIndexCount :=
      subtractExact pre.activeVaultAndIndexCount u256One (by
        change 1 ≤ pre.activeVaultAndIndexCount.val
        omega)
    ownerZUSDBalance := subtractExact pre.ownerZUSDBalance vault.netDebt hBalance
    ownerCollateralBalance :=
      addExact pre.ownerCollateralBalance vault.collateral hCapacity.1
    gasPoolCustody := subtractExact pre.gasPoolCustody vault.reserveDebt hReserve
    totalZUSDSupply :=
      subtractExact pre.totalZUSDSupply (compositeDebt vault) hUnderflow.2.2.2
    transitionSequence := closeOccurrence
  }

/-- Accepted candidates package every critical owner-close equality. -/
structure OwnerCloseAcceptedCertificate
    (pre : OwnerCloseState) (request : CloseVaultRequest) where
  sourceVault : ActiveVault
  sourceSelected : activeTarget pre request = some sourceVault
  post : OwnerCloseState
  effects : OwnerCloseEffects
  effectVaultIdentityExact : effects.vaultIdentity = sourceVault.identity
  effectCloseOccurrenceExact : effects.closeOccurrence = post.transitionSequence
  derivedNormalModeOnly : deriveRiskMode request = .normal
  systemTCRAtLeastCCR : systemTCRAtOrAboveCCR request
  modeProjectionExact : modeProjectionMatches pre request
  preSystemTCRAtLeastCCR :
    tcrAtOrAboveCCR pre.systemCollateral pre.systemCompositeDebt request.priceE18
  moreThanOneActiveVault : 1 < pre.activeVaultAndIndexCount.val
  postCloseTCRAtLeastCCR : candidateTCRAtOrAboveCCR request
  remainingActiveCompositeDebtFloor :
    (pre.activeVaultAndIndexCount.val - 1) *
        liquityV1MinCompositeDebtAtoms ≤
      request.candidateSystemCompositeDebt.val
  candidateAggregateCountPositive :
    0 < pre.activeVaultAndIndexCount.val
  remainingActiveCollateralFloor :
    pre.activeVaultAndIndexCount.val - 1 ≤
      request.candidateSystemCollateral.val
  sourceNetDebtMinimum :
    liquityV1MinNetDebtAtoms ≤ sourceVault.netDebt.val
  sourceReserveExact :
    sourceVault.reserveDebt.val = liquityV1GasReserveAtoms
  targetReserveMatchesSource :
    targetReserve pre = some (expectedTargetReserve sourceVault)
  sourceReserveCustodySufficient :
    sourceVault.reserveDebt.val ≤ pre.gasPoolCustody.val
  gasPoolCoversAllActiveReserves :
    pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤
      pre.gasPoolCustody.val
  ownerBurnExact : effects.ownerNetDebtBurn = sourceVault.netDebt
  reserveBurnExact : effects.gasReserveBurn = sourceVault.reserveDebt
  compositeBurnExact : effects.totalZUSDBurn = compositeDebt sourceVault
  systemDebtEffectExact :
    effects.systemCompositeDebtDecrease = effects.totalZUSDBurn
  collateralReturnExact : effects.collateralReturn = sourceVault.collateral
  systemCollateralEffectExact :
    effects.systemCollateralDecrease = effects.collateralReturn
  stakeRemovalExact : effects.stakeRemoval = sourceVault.stake
  indexCountEffectExact : effects.activeVaultAndIndexCountDecrease = u256One
  supplyDecreaseExact :
    post.totalZUSDSupply.val + effects.totalZUSDBurn.val =
      pre.totalZUSDSupply.val
  systemDebtDecreaseExact :
    post.systemCompositeDebt.val + effects.totalZUSDBurn.val =
      pre.systemCompositeDebt.val
  ownerBalanceDecreaseExact :
    post.ownerZUSDBalance.val + effects.ownerNetDebtBurn.val =
      pre.ownerZUSDBalance.val
  reserveCustodyDecreaseExact :
    post.gasPoolCustody.val + effects.gasReserveBurn.val =
      pre.gasPoolCustody.val
  ownerCollateralCreditExact :
    post.ownerCollateralBalance.val =
      pre.ownerCollateralBalance.val + effects.collateralReturn.val
  systemCollateralDecreaseExact :
    post.systemCollateral.val + effects.collateralReturn.val =
      pre.systemCollateral.val
  stakeDecreaseExact :
    post.totalActiveStake.val + effects.stakeRemoval.val =
      pre.totalActiveStake.val
  activeCountDecreaseExact :
    post.activeVaultAndIndexCount.val + 1 = pre.activeVaultAndIndexCount.val
  postSupplyEqualsSystemDebt :
    post.totalZUSDSupply = post.systemCompositeDebt
  targetReserveCleared : targetReserve post = none
  terminalClosedByOwner :
    post.lifecycle = .closedByOwner sourceVault.identity post.transitionSequence
  sequenceAdvanced :
    post.transitionSequence.val = pre.transitionSequence.val + 1

def buildAcceptedCertificate
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (hAdmissible : Admissible pre request) :
    OwnerCloseAcceptedCertificate pre request := by
  match hTarget : activeTarget pre request with
  | none =>
      simp [Admissible, hTarget] at hAdmissible
  | some vault =>
      have hAll := hAdmissible
      simp only [Admissible, hTarget] at hAll
      rcases hAll with
        ⟨_hAuthority, _hWallet, hNormal, hBalance, hCount, hUnderflow,
          hCapacity, hCandidate, hTCR, hReserveProjection, hReserve,
          hSequence, _hContext, hModeProjection⟩
      have hSystemTCR : systemTCRAtOrAboveCCR request :=
        (deriveRiskMode_normal_iff_system_tcr_at_or_above_ccr request).mp hNormal
      have hPreSystemTCR :
          tcrAtOrAboveCCR pre.systemCollateral pre.systemCompositeDebt
            request.priceE18 := by
        rcases hModeProjection with ⟨hModeCollateral, hModeDebt⟩
        unfold systemTCRAtOrAboveCCR at hSystemTCR
        rw [hModeCollateral, hModeDebt] at hSystemTCR
        exact hSystemTCR
      have hSystemCollateral :
          vault.collateral.val ≤ pre.systemCollateral.val := hUnderflow.1
      have hSystemDebt :
          (compositeDebt vault).val ≤ pre.systemCompositeDebt.val :=
        hUnderflow.2.1
      have hStake : vault.stake.val ≤ pre.totalActiveStake.val :=
        hUnderflow.2.2.1
      have hSupply :
          (compositeDebt vault).val ≤ pre.totalZUSDSupply.val :=
        hUnderflow.2.2.2
      rcases hCandidate with
        ⟨_hCandidateCollateral, _hCandidateDebt, hCandidateCountPositive,
          hRemainingActiveDebtFloor, hRemainingActiveCollateralFloor,
          hSupplyDebt, _hWalletSupply, _hGasSupply, _hCustodySupply⟩
      have hTargetReserveExact :
          targetReserve pre = some (expectedTargetReserve vault) :=
        hReserveProjection.1
      have hGasPoolReserveFloor :
          pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤
            pre.gasPoolCustody.val := by
        rcases hReserveProjection.2 with hBelowTarget | hCovered
        · omega
        · exact hCovered.2
      let post := buildPostState pre vault hBalance hCount hUnderflow
        hCapacity hReserve hSequence
      let effects := buildEffects vault post.transitionSequence
      have hSupplyDecrease :
          post.totalZUSDSupply.val + effects.totalZUSDBurn.val =
            pre.totalZUSDSupply.val := by
        change
          pre.totalZUSDSupply.val - (compositeDebt vault).val +
              (compositeDebt vault).val = pre.totalZUSDSupply.val
        omega
      have hSystemDebtDecrease :
          post.systemCompositeDebt.val + effects.totalZUSDBurn.val =
            pre.systemCompositeDebt.val := by
        change
          pre.systemCompositeDebt.val - (compositeDebt vault).val +
              (compositeDebt vault).val = pre.systemCompositeDebt.val
        omega
      have hOwnerBalanceDecrease :
          post.ownerZUSDBalance.val + effects.ownerNetDebtBurn.val =
            pre.ownerZUSDBalance.val := by
        change
          pre.ownerZUSDBalance.val - vault.netDebt.val + vault.netDebt.val =
            pre.ownerZUSDBalance.val
        omega
      have hReserveCustodyDecrease :
          post.gasPoolCustody.val + effects.gasReserveBurn.val =
            pre.gasPoolCustody.val := by
        change
          pre.gasPoolCustody.val - vault.reserveDebt.val +
              vault.reserveDebt.val = pre.gasPoolCustody.val
        omega
      have hSystemCollateralDecrease :
          post.systemCollateral.val + effects.collateralReturn.val =
            pre.systemCollateral.val := by
        change
          pre.systemCollateral.val - vault.collateral.val +
              vault.collateral.val = pre.systemCollateral.val
        omega
      have hStakeDecrease :
          post.totalActiveStake.val + effects.stakeRemoval.val =
            pre.totalActiveStake.val := by
        change
          pre.totalActiveStake.val - vault.stake.val + vault.stake.val =
            pre.totalActiveStake.val
        omega
      have hActiveCountDecrease :
          post.activeVaultAndIndexCount.val + 1 =
            pre.activeVaultAndIndexCount.val := by
        change
          pre.activeVaultAndIndexCount.val - 1 + 1 =
            pre.activeVaultAndIndexCount.val
        omega
      have hPostSupplyDebt :
          post.totalZUSDSupply = post.systemCompositeDebt := by
        apply Fin.ext
        change
          pre.totalZUSDSupply.val - (compositeDebt vault).val =
            pre.systemCompositeDebt.val - (compositeDebt vault).val
        omega
      refine {
        sourceVault := vault
        sourceSelected := hTarget
        post := post
        effects := effects
        effectVaultIdentityExact := rfl
        effectCloseOccurrenceExact := rfl
        derivedNormalModeOnly := hNormal
        systemTCRAtLeastCCR := hSystemTCR
        modeProjectionExact := hModeProjection
        preSystemTCRAtLeastCCR := hPreSystemTCR
        moreThanOneActiveVault := hCount
        postCloseTCRAtLeastCCR := hTCR
        remainingActiveCompositeDebtFloor := hRemainingActiveDebtFloor
        candidateAggregateCountPositive := hCandidateCountPositive
        remainingActiveCollateralFloor := hRemainingActiveCollateralFloor
        sourceNetDebtMinimum := vault.netDebtAtLeastSourceMinimum
        sourceReserveExact := vault.reserveIsSourceConstant
        targetReserveMatchesSource := hTargetReserveExact
        sourceReserveCustodySufficient := hReserve
        gasPoolCoversAllActiveReserves := hGasPoolReserveFloor
        ownerBurnExact := rfl
        reserveBurnExact := rfl
        compositeBurnExact := rfl
        systemDebtEffectExact := rfl
        collateralReturnExact := rfl
        systemCollateralEffectExact := rfl
        stakeRemovalExact := rfl
        indexCountEffectExact := rfl
        supplyDecreaseExact := hSupplyDecrease
        systemDebtDecreaseExact := hSystemDebtDecrease
        ownerBalanceDecreaseExact := hOwnerBalanceDecrease
        reserveCustodyDecreaseExact := hReserveCustodyDecrease
        ownerCollateralCreditExact := rfl
        systemCollateralDecreaseExact := hSystemCollateralDecrease
        stakeDecreaseExact := hStakeDecrease
        activeCountDecreaseExact := hActiveCountDecrease
        postSupplyEqualsSystemDebt := hPostSupplyDebt
        targetReserveCleared := rfl
        terminalClosedByOwner := rfl
        sequenceAdvanced := rfl
      }

/-- Total result algebra: accepted certificate or complete stable-order failures. -/
inductive OwnerCloseResult
    (pre : OwnerCloseState) (request : CloseVaultRequest) where
  | accepted (certificate : OwnerCloseAcceptedCertificate pre request)
  | rejected (failures : List OwnerCloseReject)

def runOwnerClose
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    OwnerCloseResult pre request :=
  if hAdmissible : Admissible pre request then
    .accepted (buildAcceptedCertificate pre request hAdmissible)
  else
    .rejected (guardFailures pre request)

/-- The critical runner accepts exactly the admissible transition domain. -/
theorem run_owner_close_accepts_iff_admissible
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    (∃ certificate,
        runOwnerClose pre request = .accepted certificate) ↔
      Admissible pre request := by
  by_cases hAdmissible : Admissible pre request <;>
    simp [runOwnerClose, hAdmissible]

/-- Every inadmissible input returns its exact complete guard vector. -/
theorem run_owner_close_inadmissible_returns_exact_failures
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (hInadmissible : ¬ Admissible pre request) :
    runOwnerClose pre request =
      .rejected (guardFailures pre request) := by
  simp [runOwnerClose, hInadmissible]

def committedState
    (pre : OwnerCloseState) (request : CloseVaultRequest) :
    OwnerCloseResult pre request → OwnerCloseState
  | .accepted certificate => certificate.post
  | .rejected _ => pre

/-- CE-095 closure in the pure model: acceptance commits its dependent certificate. -/
theorem accepted_result_commits_exact_certificate_post
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    committedState pre request (.accepted certificate) = certificate.post := by
  rfl

/-- Every rejected result is an exact no-op at the scoped commit projection. -/
theorem ordered_rejection_is_noop
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (failures : List OwnerCloseReject) :
    committedState pre request (.rejected failures) = pre := by
  rfl

theorem run_rejection_is_noop
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (failures : List OwnerCloseReject)
    (hRejected : runOwnerClose pre request = .rejected failures) :
    committedState pre request (runOwnerClose pre request) = pre := by
  rw [hRejected]
  rfl

/-- An inadmissible transition always has at least one stable-ABI failure. -/
theorem inadmissible_has_reported_failure
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (hInadmissible : ¬ Admissible pre request) :
    guardFailures pre request ≠ [] := by
  intro hEmpty
  exact hInadmissible
    ((guardFailures_eq_nil_iff_admissible pre request).mp hEmpty)

/-- The actual runner can only return a declared-order failure subsequence. -/
theorem run_rejected_failures_follow_declared_order
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (failures : List OwnerCloseReject)
    (hRejected : runOwnerClose pre request = .rejected failures) :
    List.Sublist failures rejectOrder := by
  unfold runOwnerClose at hRejected
  split at hRejected
  · contradiction
  · cases hRejected
    exact guardFailures_follow_declared_order pre request

/-- The runtime rejection has both stable order and exact no-op commit semantics. -/
theorem run_ordered_rejection_is_noop
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (failures : List OwnerCloseReject)
    (hRejected : runOwnerClose pre request = .rejected failures) :
    List.Sublist failures rejectOrder ∧
      committedState pre request (runOwnerClose pre request) = pre :=
  ⟨run_rejected_failures_follow_declared_order pre request failures hRejected,
    run_rejection_is_noop pre request failures hRejected⟩

/-- A `ClosedByOwner` occurrence cannot become active again through this FSM. -/
theorem closed_by_owner_is_terminal_for_owner_close
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (identity : VaultIdentity) (occurrence : U256)
    (hClosed : pre.lifecycle = .closedByOwner identity occurrence) :
    ∃ failures,
      runOwnerClose pre request = .rejected failures ∧
        .targetVaultInactive ∈ failures := by
  have hTarget : activeTarget pre request = none := by
    simp [activeTarget, hClosed]
  have hNotAdmissible : ¬ Admissible pre request := by
    simp [Admissible, hTarget]
  have hRun :
      runOwnerClose pre request = .rejected (guardFailures pre request) := by
    simp [runOwnerClose, hNotAdmissible]
  have hInactive :
      .targetVaultInactive ∈ guardFailures pre request := by
    simp [guardFailures, rejectOrder, guardPass, hTarget]
  exact ⟨guardFailures pre request, hRun, hInactive⟩

/-- Accepted closure is Normal-Mode-only, as in pinned `closeTrove`. -/
theorem liquity_v1_8f52f290_owner_close_accept_implies_normal_mode
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    deriveRiskMode request = .normal ∧
      systemTCRAtOrAboveCCR request ∧
      modeProjectionMatches pre request ∧
      tcrAtOrAboveCCR pre.systemCollateral pre.systemCompositeDebt
        request.priceE18 :=
  ⟨certificate.derivedNormalModeOnly, certificate.systemTCRAtLeastCCR,
    certificate.modeProjectionExact, certificate.preSystemTCRAtLeastCCR⟩

/-- Pinned `_closeTrove` forbids removal of the last active trove. -/
theorem liquity_v1_8f52f290_owner_close_accept_implies_not_last_vault
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    1 < pre.activeVaultAndIndexCount.val :=
  certificate.moreThanOneActiveVault

/-- Pinned `closeTrove` requires candidate TCR at least the 150% CCR. -/
theorem liquity_v1_8f52f290_owner_close_accept_implies_post_tcr_at_least_ccr
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    candidateTCRAtOrAboveCCR request :=
  certificate.postCloseTCRAtLeastCCR

/-- Pinned active source occurrences carry at least `1800e18` net debt. -/
theorem liquity_v1_8f52f290_owner_close_source_min_net_debt_1800e18
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    liquityV1MinNetDebtAtoms ≤ certificate.sourceVault.netDebt.val :=
  certificate.sourceNetDebtMinimum

/-- Pinned active source occurrences carry exactly the `200e18` Gas Pool reserve. -/
theorem liquity_v1_8f52f290_owner_close_reserve_exact_200e18
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.sourceVault.reserveDebt.val = liquityV1GasReserveAtoms :=
  certificate.sourceReserveExact

/-- CE-098: accepted input binds the target reserve and covers all active reserves. -/
theorem accepted_gas_pool_is_a_reserve_floor_with_exact_target_binding
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    targetReserve pre = some (expectedTargetReserve certificate.sourceVault) ∧
      certificate.sourceVault.reserveDebt.val ≤ pre.gasPoolCustody.val ∧
      pre.activeVaultAndIndexCount.val * liquityV1GasReserveAtoms ≤
        pre.gasPoolCustody.val :=
  ⟨certificate.targetReserveMatchesSource,
    certificate.sourceReserveCustodySufficient,
    certificate.gasPoolCoversAllActiveReserves⟩

/-- CE-108: a closed vault leaves no target-reserve association in poststate. -/
theorem accepted_clears_target_reserve_association
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    targetReserve certificate.post = none :=
  certificate.targetReserveCleared

theorem liquity_v1_8f52f290_constant_reserve_is_200e18 :
    liquityV1GasReserveAtoms = 200_000_000_000_000_000_000 := by
  norm_num [liquityV1GasReserveAtoms, atomsScale]

theorem liquity_v1_8f52f290_constant_min_net_debt_is_1800e18 :
    liquityV1MinNetDebtAtoms = 1_800_000_000_000_000_000_000 := by
  norm_num [liquityV1MinNetDebtAtoms, atomsScale]

theorem liquity_v1_8f52f290_constant_min_composite_debt_is_2000e18 :
    liquityV1MinCompositeDebtAtoms = 2_000_000_000_000_000_000_000 := by
  norm_num [liquityV1MinCompositeDebtAtoms, liquityV1MinNetDebtAtoms,
    liquityV1GasReserveAtoms, atomsScale]

/-- CE-096: accepted aggregate debt covers every remaining active occurrence. -/
theorem accepted_candidate_debt_covers_remaining_active_minimum
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    (pre.activeVaultAndIndexCount.val - 1) *
        liquityV1MinCompositeDebtAtoms ≤
      request.candidateSystemCompositeDebt.val :=
  certificate.remainingActiveCompositeDebtFloor

/-- CE-101/104: accepted candidate aggregates retain positive active coverage. -/
theorem accepted_candidate_aggregate_has_positive_count_and_collateral_coverage
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    0 < pre.activeVaultAndIndexCount.val ∧
      pre.activeVaultAndIndexCount.val - 1 ≤
        request.candidateSystemCollateral.val :=
  ⟨certificate.candidateAggregateCountPositive,
    certificate.remainingActiveCollateralFloor⟩

/-- Exact composite supply/debt burn is owner net debt plus reserve. -/
theorem accepted_burns_exact_net_plus_reserve
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.effects.totalZUSDBurn.val =
        certificate.effects.ownerNetDebtBurn.val +
          certificate.effects.gasReserveBurn.val ∧
      certificate.post.totalZUSDSupply.val +
          certificate.effects.totalZUSDBurn.val = pre.totalZUSDSupply.val ∧
      certificate.post.systemCompositeDebt.val +
          certificate.effects.totalZUSDBurn.val =
        pre.systemCompositeDebt.val := by
  constructor
  · rw [certificate.compositeBurnExact, certificate.ownerBurnExact,
      certificate.reserveBurnExact]
    rfl
  · exact ⟨certificate.supplyDecreaseExact,
      certificate.systemDebtDecreaseExact⟩

/-- Full source collateral is removed from the aggregate and credited to the owner. -/
theorem accepted_returns_full_collateral
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.effects.collateralReturn = certificate.sourceVault.collateral ∧
      certificate.post.ownerCollateralBalance.val =
        pre.ownerCollateralBalance.val +
          certificate.effects.collateralReturn.val ∧
      certificate.post.systemCollateral.val +
          certificate.effects.collateralReturn.val = pre.systemCollateral.val :=
  ⟨certificate.collateralReturnExact, certificate.ownerCollateralCreditExact,
    certificate.systemCollateralDecreaseExact⟩

/-- One accepted close removes the exact source stake and one active index member. -/
theorem accepted_removes_exact_stake_and_one_index_member
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.effects.stakeRemoval = certificate.sourceVault.stake ∧
      certificate.post.totalActiveStake.val +
          certificate.effects.stakeRemoval.val = pre.totalActiveStake.val ∧
      certificate.effects.activeVaultAndIndexCountDecrease = u256One ∧
      certificate.post.activeVaultAndIndexCount.val + 1 =
        pre.activeVaultAndIndexCount.val :=
  ⟨certificate.stakeRemovalExact, certificate.stakeDecreaseExact,
    certificate.indexCountEffectExact, certificate.activeCountDecreaseExact⟩

/-- `ClosedByOwner` is terminal for this occurrence and binds the new sequence. -/
theorem accepted_constructs_closed_by_owner_terminal_status
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.post.lifecycle =
        .closedByOwner certificate.sourceVault.identity
          certificate.post.transitionSequence ∧
      certificate.effects.vaultIdentity = certificate.sourceVault.identity ∧
      certificate.effects.closeOccurrence = certificate.post.transitionSequence ∧
      certificate.post.transitionSequence.val = pre.transitionSequence.val + 1 :=
  ⟨certificate.terminalClosedByOwner, certificate.effectVaultIdentityExact,
    certificate.effectCloseOccurrenceExact, certificate.sequenceAdvanced⟩

/-- Aggregate conservation bundle for every accepted scoped transition. -/
theorem accepted_preserves_owner_close_aggregate_conservation
    {pre : OwnerCloseState} {request : CloseVaultRequest}
    (certificate : OwnerCloseAcceptedCertificate pre request) :
    certificate.post.totalZUSDSupply = certificate.post.systemCompositeDebt ∧
      certificate.post.totalZUSDSupply.val +
          certificate.effects.totalZUSDBurn.val = pre.totalZUSDSupply.val ∧
      certificate.post.systemCompositeDebt.val +
          certificate.effects.systemCompositeDebtDecrease.val =
        pre.systemCompositeDebt.val ∧
      certificate.post.gasPoolCustody.val +
          certificate.effects.gasReserveBurn.val = pre.gasPoolCustody.val := by
  have hSystemDebt :
      certificate.post.systemCompositeDebt.val +
          certificate.effects.systemCompositeDebtDecrease.val =
        pre.systemCompositeDebt.val := by
    rw [certificate.systemDebtEffectExact]
    exact certificate.systemDebtDecreaseExact
  exact ⟨certificate.postSupplyEqualsSystemDebt,
    certificate.supplyDecreaseExact, hSystemDebt,
    certificate.reserveCustodyDecreaseExact⟩

/-- Recovery Mode always contributes the ordinal-three rejection. -/
theorem recovery_mode_guard_is_complete
    (pre : OwnerCloseState) (request : CloseVaultRequest)
    (hRecovery : deriveRiskMode request = .recovery) :
    .recoveryMode ∈ guardFailures pre request := by
  simp [guardFailures, rejectOrder, guardPass, hRecovery]

/-- With an active target, count one triggers the ordinal-five final-vault guard. -/
theorem final_active_vault_guard_is_complete
    (pre : OwnerCloseState) (request : CloseVaultRequest) (vault : ActiveVault)
    (hTarget : activeTarget pre request = some vault)
    (hFinal : ¬ 1 < pre.activeVaultAndIndexCount.val) :
    .finalActiveVault ∈ guardFailures pre request := by
  simp [guardFailures, rejectOrder, guardPass, activeDependentPass, hTarget,
    hFinal]

/-- Once arithmetic prerequisites pass, a below-CCR candidate owns ordinal nine. -/
theorem post_close_tcr_guard_is_complete
    (pre : OwnerCloseState) (request : CloseVaultRequest) (vault : ActiveVault)
    (hTarget : activeTarget pre request = some vault)
    (hUnderflow : aggregateUnderflowGuardsPass pre vault)
    (hCapacity : accountingCapacityGuardsPass pre vault)
    (hCandidate : candidateAggregateIsExact pre request vault)
    (hBelow : ¬ candidateTCRAtOrAboveCCR request) :
    .postCloseTCRBelowCCR ∈ guardFailures pre request := by
  simp [guardFailures, rejectOrder, guardPass, activeDependentPass, hTarget,
    hUnderflow, hCapacity, hCandidate, hBelow]

/-! ## Concrete acceptance witness -/

def witnessActiveVault : ActiveVault :=
  {
    identity := vaultIdentityOne
    collateral := ⟨12 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    netDebt :=
      ⟨1_800 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    reserveDebt :=
      ⟨200 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    stake := ⟨12 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    collateralPositive := by norm_num [atomsScale]
    netDebtAtLeastSourceMinimum := by
      norm_num [liquityV1MinNetDebtAtoms, atomsScale]
    reserveIsSourceConstant := by
      norm_num [liquityV1GasReserveAtoms, atomsScale]
    compositeDebtFits := by norm_num [u256Modulus, atomsScale]
  }

def witnessPreState : OwnerCloseState :=
  {
    lifecycle := .active witnessActiveVault
      (expectedTargetReserve witnessActiveVault)
    systemCollateral :=
      ⟨24 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    systemCompositeDebt :=
      ⟨4_000 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    totalActiveStake :=
      ⟨32 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    activeVaultAndIndexCount := ⟨2, by norm_num [u256Modulus]⟩
    ownerZUSDBalance :=
      ⟨1_800 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    ownerCollateralBalance := u256Zero
    gasPoolCustody :=
      ⟨400 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    totalZUSDSupply :=
      ⟨4_000 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    transitionSequence := u256Zero
  }

/-- CE-098 witness: one donated zUSD atom above aggregate reserve custody. -/
def witnessExcessDonationPreState : OwnerCloseState :=
  {
    witnessPreState with
    gasPoolCustody :=
      ⟨400 * atomsScale + 1, by norm_num [u256Modulus, atomsScale]⟩
  }

/-- CE-098 witness: sufficient target custody but one atom below aggregate floor. -/
def witnessAggregateReserveShortfallPreState : OwnerCloseState :=
  {
    witnessPreState with
    gasPoolCustody :=
      ⟨400 * atomsScale - 1, by norm_num [u256Modulus, atomsScale]⟩
  }

/-- CE-105 witness: correct reserve amount bound to the wrong vault identity. -/
def witnessWrongReserveTargetPreState : OwnerCloseState :=
  {
    witnessPreState with
    lifecycle := .active witnessActiveVault {
        targetVaultIdentity := vaultIdentityTwo
        amount := witnessActiveVault.reserveDebt
      }
  }

def witnessWrongReserveAmountPreState : OwnerCloseState :=
  {
    witnessPreState with
    lifecycle := .active witnessActiveVault {
        targetVaultIdentity := vaultIdentityOne
        amount :=
          ⟨199 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
      }
  }

def witnessTargetReserveInsufficientPreState : OwnerCloseState :=
  {
    witnessPreState with
    gasPoolCustody :=
      ⟨200 * atomsScale - 1, by norm_num [u256Modulus, atomsScale]⟩
  }

def witnessRequest : CloseVaultRequest :=
  {
    targetVaultIdentity := vaultIdentityOne
    authorityMatchesOwner := true
    walletMatchesOwner := true
    modeSystemCollateral :=
      ⟨24 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    modeSystemCompositeDebt :=
      ⟨4_000 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    candidateSystemCollateral :=
      ⟨12 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    candidateSystemCompositeDebt :=
      ⟨2_000 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    priceE18 :=
      ⟨250 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    pricePositive := by norm_num [atomsScale]
    systemNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [u256Modulus, atomsScale]
    candidateNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [u256Modulus, atomsScale]
    contextCurrent := true
  }

def witnessBelowCCRRequest : CloseVaultRequest :=
  {
    witnessRequest with
    modeSystemCollateral :=
      ⟨24 * atomsScale - 1, by norm_num [u256Modulus, atomsScale]⟩
    systemNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [witnessRequest, u256Modulus, atomsScale]
  }

def witnessZeroDebtRequest : CloseVaultRequest :=
  {
    witnessRequest with
    modeSystemCollateral := u256Zero
    modeSystemCompositeDebt := u256Zero
    systemNumeratorFitsWhenDebtPositive := by
      intro hPositiveDebt
      simp [u256Zero] at hPositiveDebt
  }

def witnessZeroDebtMaxRequest : CloseVaultRequest :=
  {
    witnessRequest with
    modeSystemCollateral := u256Max
    modeSystemCompositeDebt := u256Zero
    candidateSystemCollateral := u256Max
    candidateSystemCompositeDebt := u256Zero
    priceE18 := u256Max
    pricePositive := by norm_num [u256Max, u256Modulus]
    systemNumeratorFitsWhenDebtPositive := by
      intro hPositiveDebt
      simp [u256Zero] at hPositiveDebt
    candidateNumeratorFitsWhenDebtPositive := by
      intro hPositiveDebt
      simp [u256Zero] at hPositiveDebt
  }

def witnessWrongTargetRequest : CloseVaultRequest :=
  {
    witnessRequest with
    targetVaultIdentity := vaultIdentityTwo
  }

def witnessCE096GhostPreState : OwnerCloseState :=
  {
    witnessPreState with
    systemCompositeDebt :=
      ⟨2_200 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    totalZUSDSupply :=
      ⟨2_200 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
  }

def witnessCE101CollateralFloorPreState : OwnerCloseState :=
  {
    witnessPreState with
    systemCollateral :=
      ⟨12 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
  }

def witnessCE101CollateralFloorRequest : CloseVaultRequest :=
  {
    witnessRequest with
    modeSystemCollateral :=
      ⟨12 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    candidateSystemCollateral := u256Zero
    priceE18 :=
      ⟨500 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    pricePositive := by norm_num [atomsScale]
    systemNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [witnessRequest, u256Modulus, atomsScale]
    candidateNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [u256Zero, u256Modulus]
  }

def witnessCE104ZeroCountPreState : OwnerCloseState :=
  {
    witnessPreState with
    activeVaultAndIndexCount := u256Zero
  }

def witnessCE096GhostRequest : CloseVaultRequest :=
  {
    witnessRequest with
    modeSystemCompositeDebt :=
      ⟨2_200 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    candidateSystemCompositeDebt :=
      ⟨200 * atomsScale, by norm_num [u256Modulus, atomsScale]⟩
    systemNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [witnessRequest, u256Modulus, atomsScale]
    candidateNumeratorFitsWhenDebtPositive := by
      intro _hPositiveDebt
      norm_num [witnessRequest, u256Modulus, atomsScale]
  }

/-- CE-094 exact CCR equality derives Normal. -/
theorem witness_ce094_exact_ccr_derives_normal :
    deriveRiskMode witnessRequest = .normal ∧
      systemTCRAtOrAboveCCR witnessRequest := by
  decide

/-- CE-094 one collateral atom below CCR derives Recovery. -/
theorem witness_ce094_strictly_below_ccr_derives_recovery :
    deriveRiskMode witnessBelowCCRRequest = .recovery ∧
      ¬ systemTCRAtOrAboveCCR witnessBelowCCRRequest := by
  decide

/-- Liquity's zero-composite-debt convention derives Normal. -/
theorem witness_ce094_zero_debt_derives_normal :
    deriveRiskMode witnessZeroDebtRequest = .normal ∧
      systemTCRAtOrAboveCCR witnessZeroDebtRequest := by
  decide

/-- CE-097 preserves source branch order even at maximal collateral and price. -/
theorem witness_ce097_zero_debt_max_inputs_derive_normal :
    deriveRiskMode witnessZeroDebtMaxRequest = .normal ∧
      systemTCRAtOrAboveCCR witnessZeroDebtMaxRequest := by
  decide

/-- CE-106: request target equality is derived, so a different identity is inactive. -/
theorem witness_ce106_wrong_request_target_is_rejected :
    guardFailures witnessPreState witnessWrongTargetRequest =
      [.targetVaultInactive] := by
  decide

/-- Positive-debt TCR numerator overflow cannot inhabit a checked request. -/
theorem ce097_positive_debt_system_tcr_numerator_is_u256_bounded
    (request : CloseVaultRequest)
    (hPositiveDebt : request.modeSystemCompositeDebt.val ≠ 0) :
    request.modeSystemCollateral.val * request.priceE18.val < u256Modulus :=
  request.systemNumeratorFitsWhenDebtPositive hPositiveDebt

/-- CE-096's old 200e18 ghost remainder fails the 2000e18 active minimum. -/
theorem witness_ce096_ghost_active_minimum_debt_is_rejected :
    guardFailures witnessCE096GhostPreState witnessCE096GhostRequest =
      [.candidateAggregateInconsistent] := by
  decide

/-- CE-101: zero remaining collateral cannot represent one active vault. -/
theorem witness_ce101_remaining_active_collateral_floor_is_rejected :
    guardFailures witnessCE101CollateralFloorPreState
        witnessCE101CollateralFloorRequest =
      [.candidateAggregateInconsistent] := by
  decide

/-- CE-104: zero count is explicit and Nat subtraction cannot hide it. -/
theorem witness_ce104_zero_count_reason_vector_is_complete :
    guardFailures witnessCE104ZeroCountPreState witnessRequest =
      [.finalActiveVault, .candidateAggregateInconsistent] := by
  decide

/-- CE-098: donated excess is admissible and cannot grief owner close. -/
theorem witness_ce098_excess_gas_pool_donation_is_admissible :
    Admissible witnessExcessDonationPreState witnessRequest := by
  decide

/-- CE-098: target sufficiency cannot mask aggregate reserve shortfall. -/
theorem witness_ce098_aggregate_reserve_shortfall_is_rejected :
    guardFailures witnessAggregateReserveShortfallPreState witnessRequest =
      [.reserveCustodyMismatch] := by
  decide

/-- CE-105: amount equality cannot mask a wrong reserve target identity. -/
theorem witness_ce105_wrong_reserve_target_identity_is_rejected :
    guardFailures witnessWrongReserveTargetPreState witnessRequest =
      [.reserveCustodyMismatch] := by
  decide

theorem witness_wrong_reserve_amount_is_rejected :
    guardFailures witnessWrongReserveAmountPreState witnessRequest =
      [.reserveCustodyMismatch] := by
  decide

/-- Custody below one target reserve belongs only to ordinal eleven. -/
theorem witness_target_reserve_insufficiency_has_exact_reason :
    guardFailures witnessTargetReserveInsufficientPreState witnessRequest =
      [.reserveCustodyInsufficient] := by
  decide

def witnessExcessDonationAcceptedCertificate :
    OwnerCloseAcceptedCertificate witnessExcessDonationPreState witnessRequest :=
  buildAcceptedCertificate witnessExcessDonationPreState witnessRequest
    witness_ce098_excess_gas_pool_donation_is_admissible

/-- The close burns one reserve and preserves the donated excess atom. -/
theorem witness_ce098_donated_excess_survives_exact_reserve_burn :
    witnessExcessDonationAcceptedCertificate.post.gasPoolCustody.val =
      200 * atomsScale + 1 := by
  have hDecrease :=
    witnessExcessDonationAcceptedCertificate.reserveCustodyDecreaseExact
  rw [witnessExcessDonationAcceptedCertificate.reserveBurnExact] at hDecrease
  rw [witnessExcessDonationAcceptedCertificate.sourceReserveExact] at hDecrease
  norm_num [witnessExcessDonationPreState, witnessPreState,
    liquityV1GasReserveAtoms, atomsScale] at hDecrease
  norm_num [atomsScale]
  omega

theorem witness_owner_close_guards_nonvacuous :
    Admissible witnessPreState witnessRequest := by
  decide

def witnessAcceptedCertificate :
    OwnerCloseAcceptedCertificate witnessPreState witnessRequest :=
  buildAcceptedCertificate witnessPreState witnessRequest
    witness_owner_close_guards_nonvacuous

def resultIsAccepted
    {pre : OwnerCloseState} {request : CloseVaultRequest} :
    OwnerCloseResult pre request → Bool
  | .accepted _ => true
  | .rejected _ => false

theorem witness_owner_close_transition_accepts :
    resultIsAccepted (runOwnerClose witnessPreState witnessRequest) = true := by
  decide

theorem witness_owner_close_exact_boundary_poststate :
    witnessAcceptedCertificate.post.systemCollateral.val = 12 * atomsScale ∧
      witnessAcceptedCertificate.post.systemCompositeDebt.val =
        2_000 * atomsScale ∧
      witnessAcceptedCertificate.post.gasPoolCustody.val = 200 * atomsScale ∧
      witnessAcceptedCertificate.post.activeVaultAndIndexCount.val = 1 := by
  have hSource :
      witnessAcceptedCertificate.sourceVault = witnessActiveVault := by
    have hSelected := witnessAcceptedCertificate.sourceSelected
    simpa [activeTarget, witnessPreState, witnessRequest, witnessActiveVault,
      vaultIdentityOne] using hSelected.symm
  have hCollateral := witnessAcceptedCertificate.systemCollateralDecreaseExact
  rw [witnessAcceptedCertificate.collateralReturnExact, hSource] at hCollateral
  have hDebt := witnessAcceptedCertificate.systemDebtDecreaseExact
  rw [witnessAcceptedCertificate.compositeBurnExact, hSource] at hDebt
  have hReserve := witnessAcceptedCertificate.reserveCustodyDecreaseExact
  rw [witnessAcceptedCertificate.reserveBurnExact, hSource] at hReserve
  have hCount := witnessAcceptedCertificate.activeCountDecreaseExact
  norm_num [witnessPreState, witnessActiveVault, compositeDebt, atomsScale] at hCollateral
  norm_num [witnessPreState, witnessActiveVault, compositeDebt, atomsScale] at hDebt
  norm_num [witnessPreState, witnessActiveVault, compositeDebt, atomsScale] at hReserve
  norm_num [witnessPreState, witnessActiveVault, compositeDebt, atomsScale] at hCount
  norm_num [atomsScale] at *
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

end ZenoDEX.ZUSDOwnerClose
