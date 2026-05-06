import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# ZenoOracle Math Witnesses

Checked arithmetic anchors for the ZenoOracle Julia witness sweep.

These theorems include bounded samples plus restricted general anchors. They are
bridge targets for later theorem families over the full median, budget, and sync
gates.
-/

namespace Proofs
namespace ZenoOracleMathWitness

def MaxDeviationBpsSorted (lo mid hi bps : Nat) : Nat :=
  max (((mid - lo) * bps) / mid) (((hi - mid) * bps) / mid)

def MedianDeviationWithinBpsSorted
    (lo mid hi bps maxAllowed : Nat) : Prop :=
  MaxDeviationBpsSorted lo mid hi bps <= maxAllowed

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

def OracleSyncWindowOK (sourceEpoch targetEpoch maxLag : Nat) : Prop :=
  EpochLag sourceEpoch targetEpoch <= maxLag

def O3ActionBindingOK (terminalDAGOK runtimeBindingOK syncWindowOK : Prop) : Prop :=
  And terminalDAGOK (And runtimeBindingOK syncWindowOK)

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

def SettlementExecutionTotalE8
    (reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta : Nat) :
    Nat :=
  reportReward + disputeReward + bondWithdrawn + slashed + feePaid + treasuryDelta + burnDelta

theorem settlement_execution_components_le_total
    {reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta : Nat} :
    reportReward <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      disputeReward <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      bondWithdrawn <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      slashed <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      feePaid <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      treasuryDelta <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta ∧
      burnDelta <=
        SettlementExecutionTotalE8
          reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta := by
  unfold SettlementExecutionTotalE8
  omega

theorem settlement_execution_components_le_budget
    {reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta budget : Nat}
    (hBudget :
      SettlementExecutionTotalE8
        reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta <= budget) :
    reportReward <= budget ∧
      disputeReward <= budget ∧
      bondWithdrawn <= budget ∧
      slashed <= budget ∧
      feePaid <= budget ∧
      treasuryDelta <= budget ∧
      burnDelta <= budget := by
  have hComponents :=
    settlement_execution_components_le_total
      (reportReward := reportReward)
      (disputeReward := disputeReward)
      (bondWithdrawn := bondWithdrawn)
      (slashed := slashed)
      (feePaid := feePaid)
      (treasuryDelta := treasuryDelta)
      (burnDelta := burnDelta)
  exact
    ⟨
      Nat.le_trans hComponents.left hBudget,
      Nat.le_trans hComponents.right.left hBudget,
      Nat.le_trans hComponents.right.right.left hBudget,
      Nat.le_trans hComponents.right.right.right.left hBudget,
      Nat.le_trans hComponents.right.right.right.right.left hBudget,
      Nat.le_trans hComponents.right.right.right.right.right.left hBudget,
      Nat.le_trans hComponents.right.right.right.right.right.right hBudget
    ⟩

theorem settlement_execution_total_budget_monotone
    {reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta oldBudget newBudget : Nat}
    (hBudget :
      SettlementExecutionTotalE8
        reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta <= oldBudget)
    (hLe : oldBudget <= newBudget) :
    SettlementExecutionTotalE8
      reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta <= newBudget := by
  exact Nat.le_trans hBudget hLe

theorem settlement_execution_components_le_larger_budget
    {reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta oldBudget newBudget : Nat}
    (hBudget :
      SettlementExecutionTotalE8
        reportReward disputeReward bondWithdrawn slashed feePaid treasuryDelta burnDelta <= oldBudget)
    (hLe : oldBudget <= newBudget) :
    reportReward <= newBudget ∧
      disputeReward <= newBudget ∧
      bondWithdrawn <= newBudget ∧
      slashed <= newBudget ∧
      feePaid <= newBudget ∧
      treasuryDelta <= newBudget ∧
      burnDelta <= newBudget := by
  exact
    settlement_execution_components_le_budget
      (settlement_execution_total_budget_monotone hBudget hLe)

def SettlementExecutionReceiptOK
    (queryBound totalsBound assetBound contractBound : Prop) : Prop :=
  And queryBound (And totalsBound (And assetBound contractBound))

def LiveEconomicsReceiptBundleV2OK
    (governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound
      settlementExecutionBound : Prop) :
    Prop :=
  And
    (LiveEconomicsReceiptBundleOK
      governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound)
    settlementExecutionBound

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

theorem median_deviation_within_requires_low_side
    {lo mid hi bps maxAllowed : Nat}
    (h : MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed) :
    (((mid - lo) * bps) / mid) <= maxAllowed := by
  unfold MedianDeviationWithinBpsSorted MaxDeviationBpsSorted at h
  exact (max_le_iff.mp h).left

theorem median_deviation_within_requires_high_side
    {lo mid hi bps maxAllowed : Nat}
    (h : MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed) :
    (((hi - mid) * bps) / mid) <= maxAllowed := by
  unfold MedianDeviationWithinBpsSorted MaxDeviationBpsSorted at h
  exact (max_le_iff.mp h).right

theorem median_deviation_within_of_side_bounds
    {lo mid hi bps maxAllowed : Nat}
    (hLo : (((mid - lo) * bps) / mid) <= maxAllowed)
    (hHi : (((hi - mid) * bps) / mid) <= maxAllowed) :
    MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed := by
  unfold MedianDeviationWithinBpsSorted MaxDeviationBpsSorted
  exact max_le hLo hHi

theorem median_deviation_within_iff_side_bounds
    {lo mid hi bps maxAllowed : Nat} :
    MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed ↔
      (((mid - lo) * bps) / mid) <= maxAllowed ∧
        (((hi - mid) * bps) / mid) <= maxAllowed := by
  constructor
  · intro h
    exact ⟨
      median_deviation_within_requires_low_side h,
      median_deviation_within_requires_high_side h
    ⟩
  · intro h
    exact median_deviation_within_of_side_bounds h.left h.right

theorem median_deviation_within_monotone_max_allowed
    {lo mid hi bps oldMaxAllowed newMaxAllowed : Nat}
    (h : MedianDeviationWithinBpsSorted lo mid hi bps oldMaxAllowed)
    (hLe : oldMaxAllowed <= newMaxAllowed) :
    MedianDeviationWithinBpsSorted lo mid hi bps newMaxAllowed := by
  unfold MedianDeviationWithinBpsSorted at *
  omega

theorem median_deviation_rejects_low_side_above_bound
    {lo mid hi bps maxAllowed : Nat}
    (hLow : maxAllowed < (((mid - lo) * bps) / mid)) :
    Not (MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed) := by
  intro h
  have hLo := median_deviation_within_requires_low_side h
  omega

theorem median_deviation_rejects_high_side_above_bound
    {lo mid hi bps maxAllowed : Nat}
    (hHigh : maxAllowed < (((hi - mid) * bps) / mid)) :
    Not (MedianDeviationWithinBpsSorted lo mid hi bps maxAllowed) := by
  intro h
  have hHi := median_deviation_within_requires_high_side h
  omega

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

theorem epoch_lag_triangle
    (left bridge right : Nat) :
    EpochLag left right <= EpochLag left bridge + EpochLag bridge right := by
  unfold EpochLag
  by_cases hLB : left <= bridge
  · by_cases hBR : bridge <= right
    · have hLR : left <= right := by omega
      simp [hLB, hBR, hLR]
      omega
    · have hRB : right <= bridge := by omega
      by_cases hLR : left <= right
      · simp [hLB, hBR, hLR]
        omega
      · have hRL : right <= left := by omega
        simp [hLB, hBR, hLR]
        omega
  · have hBL : bridge <= left := by omega
    by_cases hBR : bridge <= right
    · by_cases hLR : left <= right
      · simp [hLB, hBR, hLR]
        omega
      · have hRL : right <= left := by omega
        simp [hLB, hBR, hLR]
        omega
    · have hRB : right <= bridge := by omega
      have hRL : right <= left := by omega
      have hLR : Not (left <= right) := by omega
      simp [hLB, hBR, hLR]
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

theorem live_economics_settlement_execution_total_sample :
    SettlementExecutionTotalE8
      50000000
      10000000
      250000000000
      5000000
      100000000
      60000000
      15000000 = 250240000000 := by
  norm_num [SettlementExecutionTotalE8]

theorem live_economics_settlement_execution_total_drift_rejected :
    250239999999 ≠
      SettlementExecutionTotalE8
        50000000
        10000000
        250000000000
        5000000
        100000000
        60000000
        15000000 := by
  norm_num [SettlementExecutionTotalE8]

theorem settlement_execution_receipt_ok_requires_query_binding
    {queryBound totalsBound assetBound contractBound : Prop}
    (h : SettlementExecutionReceiptOK queryBound totalsBound assetBound contractBound) :
    queryBound := by
  exact h.left

theorem settlement_execution_receipt_ok_requires_totals_binding
    {queryBound totalsBound assetBound contractBound : Prop}
    (h : SettlementExecutionReceiptOK queryBound totalsBound assetBound contractBound) :
    totalsBound := by
  exact h.right.left

theorem settlement_execution_receipt_ok_requires_asset_binding
    {queryBound totalsBound assetBound contractBound : Prop}
    (h : SettlementExecutionReceiptOK queryBound totalsBound assetBound contractBound) :
    assetBound := by
  exact h.right.right.left

theorem settlement_execution_receipt_ok_requires_contract_binding
    {queryBound totalsBound assetBound contractBound : Prop}
    (h : SettlementExecutionReceiptOK queryBound totalsBound assetBound contractBound) :
    contractBound := by
  exact h.right.right.right

theorem settlement_execution_receipt_ok_iff_obligations
    {queryBound totalsBound assetBound contractBound : Prop} :
    SettlementExecutionReceiptOK queryBound totalsBound assetBound contractBound ↔
      queryBound ∧ totalsBound ∧ assetBound ∧ contractBound := by
  constructor
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩

theorem settlement_execution_receipt_rejects_missing_asset_binding
    {queryBound totalsBound contractBound : Prop} :
    Not (SettlementExecutionReceiptOK queryBound totalsBound False contractBound) := by
  intro h
  exact settlement_execution_receipt_ok_requires_asset_binding h

theorem settlement_execution_receipt_rejects_missing_totals_binding
    {queryBound assetBound contractBound : Prop} :
    Not (SettlementExecutionReceiptOK queryBound False assetBound contractBound) := by
  intro h
  exact settlement_execution_receipt_ok_requires_totals_binding h

theorem settlement_execution_receipt_rejects_missing_contract_binding
    {queryBound totalsBound assetBound : Prop} :
    Not (SettlementExecutionReceiptOK queryBound totalsBound assetBound False) := by
  intro h
  exact settlement_execution_receipt_ok_requires_contract_binding h

theorem live_economics_receipt_bundle_v2_requires_settlement_execution
    {governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound
      settlementExecutionBound : Prop}
    (h :
      LiveEconomicsReceiptBundleV2OK
        governanceApprovalBound governanceExecutionBound escrowFundingBound replayFloorBound
        settlementExecutionBound) :
    settlementExecutionBound := by
  exact h.right

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

theorem terminal_dag_ok_iff_obligations
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop} :
    TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound ↔
      depsAvailable ∧ noDuplicateReceipts ∧ contentHashesBound := by
  constructor
  · intro h
    exact ⟨h.left, h.right.left, h.right.right⟩
  · intro h
    exact ⟨h.left, h.right.left, h.right.right⟩

theorem terminal_dag_rejects_missing_dependency
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop}
    (hMissingDeps : Not depsAvailable) :
    Not (TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound) := by
  intro h
  exact hMissingDeps h.left

theorem terminal_dag_rejects_content_hash_drift
    {depsAvailable noDuplicateReceipts contentHashesBound : Prop}
    (hContentDrift : Not contentHashesBound) :
    Not (TerminalReceiptDAGOK depsAvailable noDuplicateReceipts contentHashesBound) := by
  intro h
  exact hContentDrift h.right.right

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

theorem runtime_binding_ok_requires_same_consumer_action
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (h : OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) :
    sameConsumerAction := by
  exact h.right.right.right

theorem runtime_binding_ok_iff_obligations
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop} :
    OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction ↔
      registryRootBound ∧ runtimeStateBound ∧ valueBound ∧ sameConsumerAction := by
  constructor
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩

theorem runtime_binding_rejects_registry_root_drift
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (hRegistryDrift : Not registryRootBound) :
    Not (OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) := by
  intro h
  exact hRegistryDrift h.left

theorem runtime_binding_rejects_runtime_state_drift
    {registryRootBound runtimeStateBound valueBound sameConsumerAction : Prop}
    (hRuntimeDrift : Not runtimeStateBound) :
    Not (OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction) := by
  intro h
  exact hRuntimeDrift h.right.left

theorem oracle_sync_window_ok_comm
    {sourceEpoch targetEpoch maxLag : Nat} :
    OracleSyncWindowOK sourceEpoch targetEpoch maxLag ↔
      OracleSyncWindowOK targetEpoch sourceEpoch maxLag := by
  unfold OracleSyncWindowOK
  rw [epoch_lag_comm]

theorem oracle_sync_window_rejects_lag_above_max
    {sourceEpoch targetEpoch maxLag : Nat}
    (hLag : maxLag < EpochLag sourceEpoch targetEpoch) :
    Not (OracleSyncWindowOK sourceEpoch targetEpoch maxLag) := by
  intro h
  unfold OracleSyncWindowOK at h
  omega

theorem oracle_sync_window_ok_monotone
    {sourceEpoch targetEpoch oldMaxLag newMaxLag : Nat}
    (h : OracleSyncWindowOK sourceEpoch targetEpoch oldMaxLag)
    (hLe : oldMaxLag <= newMaxLag) :
    OracleSyncWindowOK sourceEpoch targetEpoch newMaxLag := by
  unfold OracleSyncWindowOK at *
  omega

theorem oracle_sync_window_ok_compose
    {sourceEpoch bridgeEpoch targetEpoch maxLagAB maxLagBC : Nat}
    (hAB : OracleSyncWindowOK sourceEpoch bridgeEpoch maxLagAB)
    (hBC : OracleSyncWindowOK bridgeEpoch targetEpoch maxLagBC) :
    OracleSyncWindowOK sourceEpoch targetEpoch (maxLagAB + maxLagBC) := by
  unfold OracleSyncWindowOK at *
  have hTriangle := epoch_lag_triangle sourceEpoch bridgeEpoch targetEpoch
  omega

theorem o3_action_binding_ok_requires_terminal_dag
    {terminalDAGOK runtimeBindingOK syncWindowOK : Prop}
    (h : O3ActionBindingOK terminalDAGOK runtimeBindingOK syncWindowOK) :
    terminalDAGOK := by
  exact h.left

theorem o3_action_binding_ok_requires_runtime_binding
    {terminalDAGOK runtimeBindingOK syncWindowOK : Prop}
    (h : O3ActionBindingOK terminalDAGOK runtimeBindingOK syncWindowOK) :
    runtimeBindingOK := by
  exact h.right.left

theorem o3_action_binding_ok_requires_sync_window
    {terminalDAGOK runtimeBindingOK syncWindowOK : Prop}
    (h : O3ActionBindingOK terminalDAGOK runtimeBindingOK syncWindowOK) :
    syncWindowOK := by
  exact h.right.right

theorem o3_action_binding_ok_iff_component_obligations
    {terminalDAGOK runtimeBindingOK syncWindowOK : Prop} :
    O3ActionBindingOK terminalDAGOK runtimeBindingOK syncWindowOK ↔
      terminalDAGOK ∧ runtimeBindingOK ∧ syncWindowOK := by
  constructor
  · intro h
    exact ⟨h.left, h.right.left, h.right.right⟩
  · intro h
    exact ⟨h.left, h.right.left, h.right.right⟩

theorem o3_action_binding_ok_requires_value_bound
    {terminalDAGOK registryRootBound runtimeStateBound valueBound sameConsumerAction syncWindowOK : Prop}
    (h :
      O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction)
        syncWindowOK) :
    valueBound := by
  exact runtime_binding_ok_requires_value_bound h.right.left

theorem o3_action_binding_ok_requires_same_consumer_action
    {terminalDAGOK registryRootBound runtimeStateBound valueBound sameConsumerAction syncWindowOK : Prop}
    (h :
      O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound sameConsumerAction)
        syncWindowOK) :
    sameConsumerAction := by
  exact runtime_binding_ok_requires_same_consumer_action h.right.left

theorem o3_action_binding_sample :
    O3ActionBindingOK
      (TerminalReceiptDAGOK True True True)
      (OracleRuntimeBindingOK True True True True)
      (OracleSyncWindowOK 100 101 1) := by
  norm_num [O3ActionBindingOK, TerminalReceiptDAGOK, OracleRuntimeBindingOK, OracleSyncWindowOK, EpochLag]

theorem o3_action_binding_rejects_duplicate_receipt
    {runtimeBindingOK syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        (TerminalReceiptDAGOK True False True)
        runtimeBindingOK
        syncWindowOK) := by
  intro h
  exact terminal_dag_ok_requires_no_duplicate_receipts h.left

theorem o3_action_binding_rejects_missing_dependency
    {noDuplicateReceipts contentHashesBound runtimeBindingOK syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        (TerminalReceiptDAGOK False noDuplicateReceipts contentHashesBound)
        runtimeBindingOK
        syncWindowOK) := by
  intro h
  exact terminal_dag_ok_requires_dependencies h.left

theorem o3_action_binding_rejects_content_hash_drift
    {depsAvailable noDuplicateReceipts runtimeBindingOK syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        (TerminalReceiptDAGOK depsAvailable noDuplicateReceipts False)
        runtimeBindingOK
        syncWindowOK) := by
  intro h
  exact terminal_dag_ok_requires_content_hashes_bound h.left

theorem o3_action_binding_rejects_registry_root_drift
    {terminalDAGOK runtimeStateBound valueBound sameConsumerAction syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK False runtimeStateBound valueBound sameConsumerAction)
        syncWindowOK) := by
  intro h
  exact runtime_binding_ok_requires_registry_root h.right.left

theorem o3_action_binding_rejects_runtime_state_drift
    {terminalDAGOK registryRootBound valueBound sameConsumerAction syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK registryRootBound False valueBound sameConsumerAction)
        syncWindowOK) := by
  intro h
  exact runtime_binding_ok_requires_runtime_state h.right.left

theorem o3_action_binding_rejects_missing_value_binding
    {terminalDAGOK registryRootBound runtimeStateBound sameConsumerAction syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK registryRootBound runtimeStateBound False sameConsumerAction)
        syncWindowOK) := by
  intro h
  exact o3_action_binding_ok_requires_value_bound h

theorem o3_action_binding_rejects_wrong_consumer_action
    {terminalDAGOK registryRootBound runtimeStateBound valueBound syncWindowOK : Prop} :
    Not
      (O3ActionBindingOK
        terminalDAGOK
        (OracleRuntimeBindingOK registryRootBound runtimeStateBound valueBound False)
        syncWindowOK) := by
  intro h
  exact o3_action_binding_ok_requires_same_consumer_action h

theorem o3_action_binding_rejects_stale_sync_window
    {terminalDAGOK runtimeBindingOK : Prop} :
    Not
      (O3ActionBindingOK
        terminalDAGOK
        runtimeBindingOK
        (OracleSyncWindowOK 100 103 1)) := by
  intro h
  have hSync : OracleSyncWindowOK 100 103 1 :=
    o3_action_binding_ok_requires_sync_window h
  unfold OracleSyncWindowOK at hSync
  norm_num [EpochLag] at hSync

theorem o3_action_binding_preserved_by_sync_window_widening
    {terminalDAGOK runtimeBindingOK : Prop}
    {sourceEpoch targetEpoch oldMaxLag newMaxLag : Nat}
    (h :
      O3ActionBindingOK
        terminalDAGOK
        runtimeBindingOK
        (OracleSyncWindowOK sourceEpoch targetEpoch oldMaxLag))
    (hLe : oldMaxLag <= newMaxLag) :
    O3ActionBindingOK
      terminalDAGOK
      runtimeBindingOK
      (OracleSyncWindowOK sourceEpoch targetEpoch newMaxLag) := by
  exact
    And.intro h.left
      (And.intro h.right.left
        (oracle_sync_window_ok_monotone h.right.right hLe))

theorem o3_action_binding_preserved_by_sync_window_composition
    {terminalDAGOK runtimeBindingOK : Prop}
    {sourceEpoch bridgeEpoch targetEpoch maxLagAB maxLagBC : Nat}
    (h :
      O3ActionBindingOK
        terminalDAGOK
        runtimeBindingOK
        (OracleSyncWindowOK sourceEpoch bridgeEpoch maxLagAB))
    (hBC : OracleSyncWindowOK bridgeEpoch targetEpoch maxLagBC) :
    O3ActionBindingOK
      terminalDAGOK
      runtimeBindingOK
      (OracleSyncWindowOK sourceEpoch targetEpoch (maxLagAB + maxLagBC)) := by
  exact
    And.intro h.left
      (And.intro h.right.left
        (oracle_sync_window_ok_compose h.right.right hBC))

theorem o4_or_o5_use_requires_o3_receipt
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    o3ReceiptOK := by
  exact h.left

theorem o4_or_o5_use_requires_zenoproof_accepted
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    zenoProofAccepted := by
  exact h.right.left

theorem o4_or_o5_use_requires_same_query_value_window
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    sameQueryValueWindow := by
  exact h.right.right.left

theorem o4_or_o5_use_requires_same_consumer_action
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop}
    (h : O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction) :
    sameConsumerAction := by
  exact h.right.right.right

theorem o4_or_o5_use_iff_obligations
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction : Prop} :
    O4OrO5OracleUseOK o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction ↔
      o3ReceiptOK ∧ zenoProofAccepted ∧ sameQueryValueWindow ∧ sameConsumerAction := by
  constructor
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩
  · intro h
    exact ⟨h.left, h.right.left, h.right.right.left, h.right.right.right⟩

theorem o5_independence_witness_requires_distinct_verifiers
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    distinctVerifiers := by
  exact h.right.left

theorem o5_independence_witness_requires_distinct_proof_kinds
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    distinctProofKinds := by
  exact h.right.right.left

theorem o5_independence_witness_requires_same_input_root
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    sameInputRoot := by
  exact h.right.right.right.left

theorem o5_independence_witness_requires_same_output_root
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    sameOutputRoot := by
  exact h.right.right.right.right.left

theorem o5_independence_witness_requires_dag_closed
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (h :
      O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) :
    dagClosed := by
  exact h.right.right.right.right.right

theorem o5_independence_witness_iff_obligations
    {primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop} :
    O5IndependenceWitnessOK
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed ↔
      primaryO5Claim ∧ distinctVerifiers ∧ distinctProofKinds ∧ sameInputRoot ∧
        sameOutputRoot ∧ dagClosed := by
  constructor
  · intro h
    exact
      ⟨h.left, h.right.left, h.right.right.left, h.right.right.right.left,
        h.right.right.right.right.left, h.right.right.right.right.right⟩
  · intro h
    exact
      ⟨h.left, h.right.left, h.right.right.left, h.right.right.right.left,
        h.right.right.right.right.left, h.right.right.right.right.right⟩

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

theorem o5_use_iff_obligations
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop} :
    O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed ↔
      o3ReceiptOK ∧ zenoProofAccepted ∧ sameQueryValueWindow ∧ sameConsumerAction ∧
        primaryO5Claim ∧ distinctVerifiers ∧ distinctProofKinds ∧ sameInputRoot ∧
          sameOutputRoot ∧ dagClosed := by
  constructor
  · intro h
    have hBridge :=
      o4_or_o5_use_iff_obligations.mp h.left
    have hWitness :=
      o5_independence_witness_iff_obligations.mp h.right
    exact
      ⟨hBridge.left, hBridge.right.left, hBridge.right.right.left, hBridge.right.right.right,
        hWitness.left, hWitness.right.left, hWitness.right.right.left,
        hWitness.right.right.right.left, hWitness.right.right.right.right.left,
        hWitness.right.right.right.right.right⟩
  · intro h
    rcases h with
      ⟨hO3, hProof, hWindow, hAction, hPrimary, hVerifiers, hKinds, hInput, hOutput, hDag⟩
    exact
      ⟨
        (o4_or_o5_use_iff_obligations.mpr ⟨hO3, hProof, hWindow, hAction⟩),
        (o5_independence_witness_iff_obligations.mpr
          ⟨hPrimary, hVerifiers, hKinds, hInput, hOutput, hDag⟩)
      ⟩

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

theorem o5_use_rejects_missing_zenoproof_acceptance
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hMissingProof : Not zenoProofAccepted) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hMissingProof (o4_or_o5_use_requires_zenoproof_accepted h.left)

theorem o5_use_rejects_query_value_window_drift
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hWindowDrift : Not sameQueryValueWindow) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hWindowDrift (o4_or_o5_use_requires_same_query_value_window h.left)

theorem o5_use_rejects_missing_distinct_proof_kinds
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hMissingDistinctKinds : Not distinctProofKinds) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hMissingDistinctKinds (o5_independence_witness_requires_distinct_proof_kinds h.right)

theorem o5_use_rejects_input_root_drift
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hInputRootDrift : Not sameInputRoot) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hInputRootDrift (o5_independence_witness_requires_same_input_root h.right)

theorem o5_use_rejects_output_root_drift
    {o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
      primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed : Prop}
    (hOutputRootDrift : Not sameOutputRoot) :
    Not
      (O5OracleUseOK
        o3ReceiptOK zenoProofAccepted sameQueryValueWindow sameConsumerAction
        primaryO5Claim distinctVerifiers distinctProofKinds sameInputRoot sameOutputRoot dagClosed) := by
  intro h
  exact hOutputRootDrift (o5_independence_witness_requires_same_output_root h.right)

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
