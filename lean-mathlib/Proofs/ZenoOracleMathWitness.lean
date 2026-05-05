import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# ZenoOracle Math Witnesses

Small checked arithmetic anchors for the first ZenoOracle Julia witness sweep.

These theorems intentionally stay concrete and bounded. They are bridge targets
for later restricted theorems over the full median, budget, and sync gates.
-/

namespace Proofs
namespace ZenoOracleMathWitness

def MaxDeviationBpsSorted (lo mid hi bps : Nat) : Nat :=
  max (((mid - lo) * bps) / mid) (((hi - mid) * bps) / mid)

def DivergenceBps (left right bps : Nat) : Nat :=
  if left <= right then
    ((right - left) * bps) / right
  else
    ((left - right) * bps) / right

def EpochLag (left right : Nat) : Nat :=
  if left <= right then right - left else left - right

def TerminalReceiptDAGOK
    (depsAvailable noDuplicateReceipts contentHashesBound : Prop) : Prop :=
  And depsAvailable (And noDuplicateReceipts contentHashesBound)

def OracleRuntimeBindingOK
    (registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop) : Prop :=
  And registryRootBound (And runtimeStateBound (And valueBound sameConsumerAction))

def O4OrO5OracleUseOK
    (o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop) :
    Prop :=
  And o3ReceiptOK (And zenoProofAccepted (And sameQueryValueWindow sameConsumerAction))

def O5IndependenceWitnessOK
    (primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop) :
    Prop :=
  And primaryO5Claim
    (And distinctVerifiers
      (And distinctProofKinds (And sameInputRoot (And sameOutputRoot dagClosed))))

def O5OracleUseOK
    (o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop) :
    Prop :=
  And
    (O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction)
    (O5IndependenceWitnessOK
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed)

def LiveEconomicsEscrowFloor
    (initialDisputePool bondA bondB bondC feePaid : Nat) : Nat :=
  initialDisputePool + bondA + bondB + bondC + feePaid

def EscrowFundingOK (requiredFloor balance : Nat) : Prop :=
  requiredFloor <= balance

def GovernanceTimelockOK
    (queuedAt executableAfter executedAt delay : Nat) : Prop :=
  And (queuedAt + delay <= executableAfter) (executableAfter <= executedAt)

def LiveEconomicsReceiptBundleOK
    (governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound : Prop) :
    Prop :=
  And governanceApprovalBound
    (And governanceExecutionBound (And escrowFundingBound replayFloorBound))

theorem median_deviation_boundary_accepts :
    MaxDeviationBpsSorted 98000000 100000000 102000000 10000 = 200 := by
  norm_num [MaxDeviationBpsSorted]

theorem median_deviation_boundary_rejects :
    MaxDeviationBpsSorted 98000000 100000000 103000000 10000 = 300 := by
  norm_num [MaxDeviationBpsSorted]

theorem median_deviation_zero_scale
    {lo mid hi : Nat} :
    MaxDeviationBpsSorted lo mid hi 0 = 0 := by
  simp [MaxDeviationBpsSorted]

theorem median_deviation_equal_values
    {value bps : Nat} :
    MaxDeviationBpsSorted value value value bps = 0 := by
  simp [MaxDeviationBpsSorted]

theorem divergence_self
    {value bps : Nat} :
    DivergenceBps value value bps = 0 := by
  simp [DivergenceBps]

theorem epoch_lag_self
    {epoch : Nat} :
    EpochLag epoch epoch = 0 := by
  simp [EpochLag]

theorem epoch_lag_comm
    {left right : Nat} :
    EpochLag left right = EpochLag right left := by
  unfold EpochLag
  by_cases hLeft : left <= right
  · by_cases hRight : right <= left
    · simp [hLeft, hRight]
    · simp [hLeft, hRight]
  · have hRight : right <= left := by omega
    simp [hLeft, hRight]

theorem epoch_lag_zero_iff_equal
    {left right : Nat} :
    EpochLag left right = 0 ↔ left = right := by
  unfold EpochLag
  by_cases hLeft : left <= right
  · simp [hLeft]
    omega
  · have hRight : right <= left := by omega
    simp [hLeft]
    omega

theorem reward_pool_conservation
    {before reward after : Nat}
    (hAfter : after <= before)
    (hReward : reward = before - after) :
    after + reward = before := by
  omega

theorem positive_reward_requires_pool_decrease
    {before reward after : Nat}
    (hConservation : after + reward = before)
    (hPositive : 0 < reward) :
    after < before := by
  omega

theorem reward_pool_transition_reward_le_before
    {before reward after : Nat}
    (hConservation : after + reward = before) :
    reward <= before := by
  omega

theorem bonded_slash_conservation
    {bond slash after : Nat}
    (hAfter : after = bond - slash)
    (hSlash : slash <= bond) :
    after + slash = bond := by
  omega

theorem live_economics_escrow_floor_sample :
    LiveEconomicsEscrowFloor
      20000000
      250000000000
      250000000000
      250000000000
      100000000 = 750120000000 := by
  norm_num [LiveEconomicsEscrowFloor]

theorem escrow_funding_ok_rejects_shortfall
    {requiredFloor balance : Nat}
    (hShortfall : balance < requiredFloor) :
    Not (EscrowFundingOK requiredFloor balance) := by
  intro h
  unfold EscrowFundingOK at h
  omega

theorem governance_timelock_ok_requires_executed_after_delay
    {queuedAt executableAfter executedAt delay : Nat}
    (h : GovernanceTimelockOK queuedAt executableAfter executedAt delay) :
    queuedAt + delay <= executedAt := by
  unfold GovernanceTimelockOK at h
  omega

theorem governance_timelock_rejects_early_execution
    {queuedAt executableAfter executedAt delay : Nat}
    (hEarly : executedAt < executableAfter) :
    Not (GovernanceTimelockOK queuedAt executableAfter executedAt delay) := by
  intro h
  unfold GovernanceTimelockOK at h
  omega

theorem live_economics_receipt_bundle_ok_requires_governance_execution
    {governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound : Prop}
    (h :
      LiveEconomicsReceiptBundleOK
        governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound) :
    governanceExecutionBound := by
  exact h.right.left

theorem live_economics_receipt_bundle_ok_requires_escrow_funding
    {governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound : Prop}
    (h :
      LiveEconomicsReceiptBundleOK
        governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound) :
    escrowFundingBound := by
  exact h.right.right.left

theorem live_economics_receipt_bundle_ok_requires_replay_floor
    {governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound : Prop}
    (h :
      LiveEconomicsReceiptBundleOK
        governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound) :
    replayFloorBound := by
  exact h.right.right.right

theorem reward_pool_conservation_witness :
    75000000 + 25000000 = 100000000 := by
  norm_num

theorem reward_pool_overpay_rejected_witness :
    101000000 ≠ 100000000 - 0 := by
  norm_num

theorem source_cartel_operator_concentration_witness :
    1 < 3 := by
  norm_num

theorem split_brain_divergence_witness :
    DivergenceBps 100000000 110000000 10000 = 909 := by
  norm_num [DivergenceBps]

theorem split_brain_divergence_rejects_policy :
    100 < DivergenceBps 100000000 110000000 10000 := by
  norm_num [DivergenceBps]

theorem split_brain_epoch_lag_witness :
    EpochLag 10 13 = 3 := by
  norm_num [EpochLag]

theorem split_brain_epoch_lag_rejects_policy :
    1 < EpochLag 10 13 := by
  norm_num [EpochLag]

theorem terminal_dag_ok_requires_dependencies
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop}
    (h : TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound) :
    depsAvailable := by
  exact h.left

theorem terminal_dag_ok_requires_no_duplicate_receipts
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop}
    (h : TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound) :
    noDuplicateReceipts := by
  exact h.right.left

theorem terminal_dag_ok_requires_content_hashes_bound
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop}
    (h : TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound) :
    contentHashesBound := by
  exact h.right.right

theorem runtime_binding_ok_requires_registry_root
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (h : OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) :
    registryRootBound := by
  exact h.left

theorem runtime_binding_ok_requires_runtime_state
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (h : OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) :
    runtimeStateBound := by
  exact h.right.left

theorem runtime_binding_ok_requires_value_bound
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (h : OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) :
    valueBound := by
  exact h.right.right.left

theorem o4_or_o5_use_requires_o3_receipt
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    o3ReceiptOK := by
  exact h.left

theorem o4_or_o5_use_requires_same_consumer_action
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    sameConsumerAction := by
  exact h.right.right.right

theorem o5_independence_witness_requires_distinct_verifiers
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    distinctVerifiers := by
  exact h.right.left

theorem o5_independence_witness_requires_dag_closed
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    dagClosed := by
  exact h.right.right.right.right.right

theorem o5_use_requires_o3_receipt
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    o3ReceiptOK := by
  exact o4_or_o5_use_requires_o3_receipt h.left

theorem o5_use_requires_independence_witness
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    O5IndependenceWitnessOK
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed := by
  exact h.right

theorem o5_use_rejects_missing_distinct_verifiers
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hMissingDistinctVerifiers : Not distinctVerifiers) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hMissingDistinctVerifiers (o5_independence_witness_requires_distinct_verifiers h.right)

theorem o5_use_rejects_missing_dag_closure
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hMissingDagClosed : Not dagClosed) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hMissingDagClosed (o5_independence_witness_requires_dag_closed h.right)

end ZenoOracleMathWitness
end Proofs
