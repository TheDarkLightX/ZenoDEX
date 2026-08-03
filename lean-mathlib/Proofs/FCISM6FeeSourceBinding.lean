import Mathlib

/-!
# FCIS M6 fee source binding

This file proves the connective algebra for two unmounted M6 relations:

* a B1A-valid fee configuration is bound to one exact authority header; and
* a positive borrowing-fee occurrence is bound to one authenticated command
  projection and one exact debt transition.

It also states the current-liability equation required when principal is minted
to users and the borrowing fee is retained as an outstanding protocol claim.

The file does not prove source authentication, store currentness, the Python
refinement, U256 bounds, atomic publication, runtime mounting, or no-bypass.
-/

namespace FCISM6FeeSourceBinding

/-- The authority-header coordinates used by active fee-configuration binding. -/
structure AuthorityHeader (Root Deployment : Type) where
  configurationRoot : Root
  deployment : Deployment
  sequence : Nat
  deploymentConfigRoot : Root
  authorityEpoch : Nat
  zusdStateRoot : Root

/-- The independently validated configuration coordinates. -/
structure ValidatedConfiguration (Root Deployment : Type) where
  root : Root
  canonicalRoot : Root
  deployment : Deployment
  activationSequence : Nat

/-- The exact four-law B1B state-binding relation. -/
def StateBound
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (configuration : ValidatedConfiguration Root Deployment) : Prop :=
  configuration.root = configuration.canonicalRoot ∧
    configuration.root = header.configurationRoot ∧
    configuration.deployment = header.deployment ∧
    configuration.activationSequence ≤ header.sequence

/-- A state-bound configuration cannot simultaneously carry a foreign root. -/
theorem state_bound_rejects_configuration_root_substitution
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (configuration : ValidatedConfiguration Root Deployment)
    (hbound : StateBound header configuration)
    (hforeign : configuration.root ≠ header.configurationRoot) :
    False := by
  exact hforeign hbound.2.1

/-- A future configuration cannot satisfy the state-bound relation. -/
theorem state_bound_rejects_future_activation
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (configuration : ValidatedConfiguration Root Deployment)
    (hbound : StateBound header configuration)
    (hfuture : header.sequence < configuration.activationSequence) :
    False := by
  exact (Nat.not_lt_of_ge hbound.2.2.2) hfuture

/-- Minimal arithmetic coordinates reconstructed from an authenticated borrow. -/
structure BorrowFeeOccurrence (Root : Type) where
  requestIdentityRoot : Root
  commandRoot : Root
  requestExpectedSequence : Nat
  requestDeploymentConfigRoot : Root
  requestAuthorityEpoch : Nat
  preStateRoot : Root
  postStateRoot : Root
  principal : Nat
  fee : Nat
  debtDelta : Nat
  preDebt : Nat
  postDebt : Nat

/-- Source binding plus the exact debt equation for one positive occurrence. -/
def AuthenticatedOccurrence
    {Root : Type}
    (occurrence : BorrowFeeOccurrence Root)
    (expectedCommandRoot : Root) : Prop :=
  occurrence.commandRoot = expectedCommandRoot ∧
    0 < occurrence.fee ∧
    occurrence.debtDelta = occurrence.principal + occurrence.fee ∧
    occurrence.postDebt = occurrence.preDebt + occurrence.debtDelta

/-- Exact state and authenticated-request coordinates required by composition. -/
def StateOccurrenceAligned
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (occurrence : BorrowFeeOccurrence Root) : Prop :=
  occurrence.preStateRoot = header.zusdStateRoot ∧
    occurrence.requestExpectedSequence = header.sequence ∧
    occurrence.requestDeploymentConfigRoot = header.deploymentConfigRoot ∧
    occurrence.requestAuthorityEpoch = header.authorityEpoch

/-- An occurrence from a foreign zUSD pre-state cannot satisfy state alignment. -/
theorem state_occurrence_alignment_rejects_crossed_zusd_root
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (occurrence : BorrowFeeOccurrence Root)
    (haligned : StateOccurrenceAligned header occurrence)
    (hforeign : occurrence.preStateRoot ≠ header.zusdStateRoot) :
    False := by
  exact hforeign haligned.1

/-- State alignment exposes all three authenticated request-context equalities. -/
theorem state_occurrence_alignment_exposes_request_context
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (occurrence : BorrowFeeOccurrence Root)
    (haligned : StateOccurrenceAligned header occurrence) :
    occurrence.requestExpectedSequence = header.sequence ∧
      occurrence.requestDeploymentConfigRoot = header.deploymentConfigRoot ∧
      occurrence.requestAuthorityEpoch = header.authorityEpoch := by
  exact haligned.2

/-- An authenticated occurrence cannot be reused under a foreign command root. -/
theorem authenticated_occurrence_rejects_command_substitution
    {Root : Type}
    (occurrence : BorrowFeeOccurrence Root)
    (expectedCommandRoot : Root)
    (hoccurrence : AuthenticatedOccurrence occurrence expectedCommandRoot)
    (hforeign : occurrence.commandRoot ≠ expectedCommandRoot) :
    False := by
  exact hforeign hoccurrence.1

/-- The occurrence debt successor is exactly pre-debt plus principal plus fee. -/
theorem authenticated_occurrence_debt_formula
    {Root : Type}
    (occurrence : BorrowFeeOccurrence Root)
    (expectedCommandRoot : Root)
    (hoccurrence : AuthenticatedOccurrence occurrence expectedCommandRoot) :
    occurrence.postDebt = occurrence.preDebt + occurrence.principal + occurrence.fee := by
  rcases hoccurrence with ⟨_, _, hdelta, hpost⟩
  omega

/--
If principal becomes circulating supply and the fee becomes a current protocol
claim, the managed-asset supply-plus-claim identity follows from the debt step.
-/
theorem borrowing_fee_preserves_supply_plus_claim_identity
    (preSupply preClaim preDebt principal fee postSupply postClaim postDebt : Nat)
    (hpre : preSupply + preClaim = preDebt)
    (hsupply : postSupply = preSupply + principal)
    (hclaim : postClaim = preClaim + fee)
    (hdebt : postDebt = preDebt + principal + fee) :
    postSupply + postClaim = postDebt := by
  omega

/-- The state, command, and economic obligations compose without losing a root. -/
theorem bound_configuration_and_authenticated_occurrence_compose
    {Root Deployment : Type}
    (header : AuthorityHeader Root Deployment)
    (configuration : ValidatedConfiguration Root Deployment)
    (occurrence : BorrowFeeOccurrence Root)
    (expectedCommandRoot : Root)
    (preSupply preClaim postSupply postClaim : Nat)
    (hbound : StateBound header configuration)
    (hoccurrence : AuthenticatedOccurrence occurrence expectedCommandRoot)
    (haligned : StateOccurrenceAligned header occurrence)
    (hpre : preSupply + preClaim = occurrence.preDebt)
    (hsupply : postSupply = preSupply + occurrence.principal)
    (hclaim : postClaim = preClaim + occurrence.fee) :
    configuration.root = header.configurationRoot ∧
      occurrence.commandRoot = expectedCommandRoot ∧
      occurrence.preStateRoot = header.zusdStateRoot ∧
      occurrence.requestExpectedSequence = header.sequence ∧
      occurrence.requestDeploymentConfigRoot = header.deploymentConfigRoot ∧
      occurrence.requestAuthorityEpoch = header.authorityEpoch ∧
      postSupply + postClaim = occurrence.postDebt := by
  have heconomic : postSupply + postClaim = occurrence.postDebt := by
    apply borrowing_fee_preserves_supply_plus_claim_identity
        preSupply preClaim occurrence.preDebt occurrence.principal occurrence.fee
        postSupply postClaim occurrence.postDebt
    · exact hpre
    · exact hsupply
    · exact hclaim
    · exact authenticated_occurrence_debt_formula occurrence expectedCommandRoot hoccurrence
  exact ⟨hbound.2.1, hoccurrence.1, haligned.1, haligned.2.1,
    haligned.2.2.1, haligned.2.2.2, heconomic⟩

#print axioms state_bound_rejects_configuration_root_substitution
#print axioms state_bound_rejects_future_activation
#print axioms authenticated_occurrence_debt_formula
#print axioms state_occurrence_alignment_rejects_crossed_zusd_root
#print axioms state_occurrence_alignment_exposes_request_context
#print axioms borrowing_fee_preserves_supply_plus_claim_identity
#print axioms bound_configuration_and_authenticated_occurrence_compose

end FCISM6FeeSourceBinding
