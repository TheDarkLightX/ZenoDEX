/-!
# ZenoDEX Proof-Mining Claimability and ZenoProof Reward Gate

Small formal hardening lemmas for the proof-mining status endpoint and the
bounded ZenoProof reward-payout bridge.

The Python runtime exposes these checks as public status fields. These lemmas
record the math-level obligations that matter for the current disaster-search
witnesses: missing verified proof context, stale runtime balance snapshots, and
reward-pool self-payments cannot produce a claimable proof-mining status.
Accepted reward gates require distinct participants and preserve the combined
reward-pool and recipient total. Runtime-to-model field binding and atomic shell
application remain separate executable obligations.
-/

namespace TauSwap

namespace VerifierBackendPolicy

structure Backend where
  proofOk : Bool
  bindingOk : Bool
  policyOk : Bool
  freshnessOk : Bool
  sandboxOk : Bool
  codeIdentityOk : Bool
  deterministicOk : Bool

def contextOk (b : Backend) : Bool :=
  b.proofOk &&
    b.bindingOk &&
    b.policyOk &&
    b.freshnessOk &&
    b.sandboxOk &&
    b.codeIdentityOk &&
    b.deterministicOk

theorem context_ok_iff_obligations (b : Backend) :
    contextOk b = true ↔
      b.proofOk = true ∧
      b.bindingOk = true ∧
      b.policyOk = true ∧
      b.freshnessOk = true ∧
      b.sandboxOk = true ∧
      b.codeIdentityOk = true ∧
      b.deterministicOk = true := by
  simp [contextOk, and_assoc]

theorem context_ok_implies_sandbox_ok
    (b : Backend)
    (h : contextOk b = true) :
    b.sandboxOk = true := by
  exact (context_ok_iff_obligations b).mp h |>.right.right.right.right.left

theorem context_ok_implies_code_identity_ok
    (b : Backend)
    (h : contextOk b = true) :
    b.codeIdentityOk = true := by
  exact (context_ok_iff_obligations b).mp h |>.right.right.right.right.right.left

theorem context_ok_implies_deterministic
    (b : Backend)
    (h : contextOk b = true) :
    b.deterministicOk = true := by
  exact (context_ok_iff_obligations b).mp h |>.right.right.right.right.right.right

theorem not_context_ok_without_determinism
    (b : Backend)
    (hDet : b.deterministicOk = false) :
    contextOk b = false := by
  simp [contextOk, hDet]

end VerifierBackendPolicy

namespace ProofMiningClaimability

structure Status where
  rewardPoolConfigured : Bool
  senderValid : Bool
  claimValid : Bool
  winnerMatchesSender : Bool
  recipientDiffersFromRewardPool : Bool
  proposalHashMatchesContext : Bool
  verifiedContextPresent : Bool
  rewardPoolBalanceNonnegative : Bool
  runtimeStatePresent : Bool
  rewardPoolPubkeyMatchesState : Bool
  rewardPoolBalanceMatchesState : Bool
  managerOk : Bool

def runtimeBindingsOk (s : Status) : Bool :=
  !s.runtimeStatePresent ||
    (s.rewardPoolPubkeyMatchesState && s.rewardPoolBalanceMatchesState)

def claimable (s : Status) : Bool :=
  s.rewardPoolConfigured &&
    s.senderValid &&
    s.claimValid &&
    s.winnerMatchesSender &&
    s.recipientDiffersFromRewardPool &&
    s.proposalHashMatchesContext &&
    s.verifiedContextPresent &&
    s.rewardPoolBalanceNonnegative &&
    runtimeBindingsOk s &&
    s.managerOk

theorem not_claimable_without_verified_context
    (s : Status)
    (hContext : s.verifiedContextPresent = false) :
    claimable s = false := by
  simp [claimable, hContext]

theorem claimable_implies_verified_context
    (s : Status)
    (hClaimable : claimable s = true) :
    s.verifiedContextPresent = true := by
  cases hContext : s.verifiedContextPresent <;>
    simp [claimable, hContext] at hClaimable ⊢

theorem claimable_iff_component_obligations (s : Status) :
    claimable s = true ↔
      s.rewardPoolConfigured = true ∧
      s.senderValid = true ∧
      s.claimValid = true ∧
      s.winnerMatchesSender = true ∧
      s.recipientDiffersFromRewardPool = true ∧
      s.proposalHashMatchesContext = true ∧
      s.verifiedContextPresent = true ∧
      s.rewardPoolBalanceNonnegative = true ∧
      runtimeBindingsOk s = true ∧
      s.managerOk = true := by
  simp [claimable, and_assoc]

theorem claimable_implies_public_status_obligations
    (s : Status)
    (hClaimable : claimable s = true) :
      s.rewardPoolConfigured = true ∧
      s.senderValid = true ∧
      s.claimValid = true ∧
      s.winnerMatchesSender = true ∧
      s.recipientDiffersFromRewardPool = true ∧
      s.proposalHashMatchesContext = true ∧
      s.verifiedContextPresent = true ∧
      s.rewardPoolBalanceNonnegative = true ∧
      runtimeBindingsOk s = true ∧
      s.managerOk = true := by
  exact (claimable_iff_component_obligations s).mp hClaimable

theorem not_claimable_without_reward_pool_configured
    (s : Status)
    (hConfigured : s.rewardPoolConfigured = false) :
    claimable s = false := by
  simp [claimable, hConfigured]

theorem claimable_implies_reward_pool_configured
    (s : Status)
    (hClaimable : claimable s = true) :
    s.rewardPoolConfigured = true := by
  exact (claimable_iff_component_obligations s).mp hClaimable |>.left

theorem not_claimable_with_invalid_sender
    (s : Status)
    (hSender : s.senderValid = false) :
    claimable s = false := by
  simp [claimable, hSender]

theorem claimable_implies_sender_valid
    (s : Status)
    (hClaimable : claimable s = true) :
    s.senderValid = true := by
  cases hSender : s.senderValid <;>
    simp [claimable, hSender] at hClaimable ⊢

theorem not_claimable_with_invalid_claim
    (s : Status)
    (hClaim : s.claimValid = false) :
    claimable s = false := by
  simp [claimable, hClaim]

theorem claimable_implies_claim_valid
    (s : Status)
    (hClaimable : claimable s = true) :
    s.claimValid = true := by
  cases hClaim : s.claimValid <;>
    simp [claimable, hClaim] at hClaimable ⊢

theorem not_claimable_with_winner_mismatch
    (s : Status)
    (hWinner : s.winnerMatchesSender = false) :
    claimable s = false := by
  simp [claimable, hWinner]

theorem claimable_implies_winner_matches_sender
    (s : Status)
    (hClaimable : claimable s = true) :
    s.winnerMatchesSender = true := by
  cases hWinner : s.winnerMatchesSender <;>
    simp [claimable, hWinner] at hClaimable ⊢

theorem reward_pool_self_payment_not_claimable
    (s : Status)
    (hDistinct : s.recipientDiffersFromRewardPool = false) :
    claimable s = false := by
  simp [claimable, hDistinct]

theorem claimable_implies_recipient_differs_from_reward_pool
    (s : Status)
    (hClaimable : claimable s = true) :
    s.recipientDiffersFromRewardPool = true := by
  cases hDistinct : s.recipientDiffersFromRewardPool <;>
    simp [claimable, hDistinct] at hClaimable ⊢

theorem runtime_balance_drift_not_claimable
    (s : Status)
    (hRuntime : s.runtimeStatePresent = true)
    (hPubkey : s.rewardPoolPubkeyMatchesState = true)
    (hBalance : s.rewardPoolBalanceMatchesState = false) :
    claimable s = false := by
  simp [claimable, runtimeBindingsOk, hRuntime, hPubkey, hBalance]

theorem claimable_runtime_present_implies_balance_matches
    (s : Status)
    (hRuntime : s.runtimeStatePresent = true)
    (hClaimable : claimable s = true) :
    s.rewardPoolBalanceMatchesState = true := by
  cases hBalance : s.rewardPoolBalanceMatchesState
  · cases hPubkey : s.rewardPoolPubkeyMatchesState <;>
      simp [claimable, runtimeBindingsOk, hRuntime, hPubkey, hBalance] at hClaimable
  · rfl

theorem claimable_runtime_present_implies_pubkey_matches
    (s : Status)
    (hRuntime : s.runtimeStatePresent = true)
    (hClaimable : claimable s = true) :
    s.rewardPoolPubkeyMatchesState = true := by
  cases hPubkey : s.rewardPoolPubkeyMatchesState <;>
    simp [claimable, runtimeBindingsOk, hRuntime, hPubkey] at hClaimable ⊢

theorem runtime_pubkey_mismatch_not_claimable
    (s : Status)
    (hRuntime : s.runtimeStatePresent = true)
    (hPubkey : s.rewardPoolPubkeyMatchesState = false) :
    claimable s = false := by
  simp [claimable, runtimeBindingsOk, hRuntime, hPubkey]

theorem runtime_bindings_ok_without_runtime_state
    (s : Status)
    (hRuntime : s.runtimeStatePresent = false) :
    runtimeBindingsOk s = true := by
  simp [runtimeBindingsOk, hRuntime]

theorem claimable_implies_runtime_bindings_ok
    (s : Status)
    (hClaimable : claimable s = true) :
    runtimeBindingsOk s = true := by
  rcases (claimable_iff_component_obligations s).mp hClaimable with
    ⟨_, _, _, _, _, _, _, _, hRuntimeBindings, _⟩
  exact hRuntimeBindings

theorem not_claimable_with_wrong_proposal
    (s : Status)
    (hProposal : s.proposalHashMatchesContext = false) :
    claimable s = false := by
  simp [claimable, hProposal]

theorem claimable_implies_proposal_hash_matches_context
    (s : Status)
    (hClaimable : claimable s = true) :
    s.proposalHashMatchesContext = true := by
  cases hProposal : s.proposalHashMatchesContext <;>
    simp [claimable, hProposal] at hClaimable ⊢

theorem not_claimable_with_negative_pool_balance
    (s : Status)
    (hBalance : s.rewardPoolBalanceNonnegative = false) :
    claimable s = false := by
  simp [claimable, hBalance]

theorem claimable_implies_reward_pool_balance_nonnegative
    (s : Status)
    (hClaimable : claimable s = true) :
    s.rewardPoolBalanceNonnegative = true := by
  cases hBalance : s.rewardPoolBalanceNonnegative <;>
    simp [claimable, hBalance] at hClaimable ⊢

theorem not_claimable_when_manager_rejects
    (s : Status)
    (hManager : s.managerOk = false) :
    claimable s = false := by
  simp [claimable, hManager]

theorem claimable_implies_manager_ok
    (s : Status)
    (hClaimable : claimable s = true) :
    s.managerOk = true := by
  cases hManager : s.managerOk <;>
    simp [claimable, hManager] at hClaimable ⊢

end ProofMiningClaimability

namespace ProofMiningStatusApi

structure ApiResult where
  ok : Bool
  statusPresent : Bool
  statusClaimable : Bool

def exitSuccess (r : ApiResult) : Bool :=
  r.ok && r.statusPresent && r.statusClaimable

theorem exit_success_iff_obligations (r : ApiResult) :
    exitSuccess r = true ↔
      r.ok = true ∧
      r.statusPresent = true ∧
      r.statusClaimable = true := by
  simp [exitSuccess, and_assoc]

theorem exit_success_implies_status_present
    (r : ApiResult)
    (hSuccess : exitSuccess r = true) :
    r.statusPresent = true := by
  exact (exit_success_iff_obligations r).mp hSuccess |>.right.left

theorem exit_success_implies_status_claimable
    (r : ApiResult)
    (hSuccess : exitSuccess r = true) :
    r.statusClaimable = true := by
  exact (exit_success_iff_obligations r).mp hSuccess |>.right.right

theorem ok_without_status_not_exit_success
    (r : ApiResult)
    (hOk : r.ok = true)
    (hStatus : r.statusPresent = false) :
    exitSuccess r = false := by
  simp [exitSuccess, hOk, hStatus]

theorem ok_with_rejected_status_not_exit_success
    (r : ApiResult)
    (hOk : r.ok = true)
    (hPresent : r.statusPresent = true)
    (hClaimable : r.statusClaimable = false) :
    exitSuccess r = false := by
  simp [exitSuccess, hOk, hPresent, hClaimable]

end ProofMiningStatusApi

namespace ZenoProofRewardGate

structure Gate where
  proofOk : Bool
  bindingOk : Bool
  policyOk : Bool
  freshnessOk : Bool
  uniqueClaim : Bool
  rewardPoolHasBudget : Bool
  recipientDiffersFromRewardPool : Bool
  rewardPoolBefore : Nat
  rewardAmount : Nat
  rewardPoolAfter : Nat

def hostGuardsOk (g : Gate) : Bool :=
  g.proofOk &&
    g.bindingOk &&
    g.policyOk &&
    g.freshnessOk &&
    g.uniqueClaim &&
    g.recipientDiffersFromRewardPool &&
    g.rewardPoolHasBudget

def conservativeDelta (g : Gate) : Prop :=
  g.rewardPoolBefore = g.rewardAmount + g.rewardPoolAfter

def accepted (g : Gate) : Prop :=
  hostGuardsOk g = true ∧
    0 < g.rewardAmount ∧
    conservativeDelta g

theorem accepted_nonempty : ∃ g : Gate, accepted g := by
  exact ⟨
    { proofOk := true
      bindingOk := true
      policyOk := true
      freshnessOk := true
      uniqueClaim := true
      rewardPoolHasBudget := true
      recipientDiffersFromRewardPool := true
      rewardPoolBefore := 20
      rewardAmount := 4
      rewardPoolAfter := 16 },
    ⟨rfl, Nat.zero_lt_succ 3, rfl⟩
  ⟩

def scheduledReward (baseReward epoch : Nat) : Nat :=
  max 1 (baseReward / (2 ^ epoch))

theorem accepted_implies_host_guards_ok
    (g : Gate)
    (hAccepted : accepted g) :
    hostGuardsOk g = true :=
  hAccepted.1

theorem host_guards_ok_iff_obligations (g : Gate) :
    hostGuardsOk g = true ↔
      g.proofOk = true ∧
      g.bindingOk = true ∧
      g.policyOk = true ∧
      g.freshnessOk = true ∧
      g.uniqueClaim = true ∧
      g.recipientDiffersFromRewardPool = true ∧
      g.rewardPoolHasBudget = true := by
  simp [hostGuardsOk, and_assoc]

theorem accepted_implies_reward_gate_obligations
    (g : Gate)
    (hAccepted : accepted g) :
      g.proofOk = true ∧
      g.bindingOk = true ∧
      g.policyOk = true ∧
      g.freshnessOk = true ∧
      g.uniqueClaim = true ∧
      g.recipientDiffersFromRewardPool = true ∧
      g.rewardPoolHasBudget = true ∧
      0 < g.rewardAmount ∧
      conservativeDelta g := by
  rcases (host_guards_ok_iff_obligations g).mp hAccepted.1 with
    ⟨hProof, hBinding, hPolicy, hFreshness, hUnique, hDistinct, hBudget⟩
  exact ⟨hProof, hBinding, hPolicy, hFreshness, hUnique, hDistinct, hBudget, hAccepted.2.1, hAccepted.2.2⟩

theorem accepted_implies_proof_ok
    (g : Gate)
    (hAccepted : accepted g) :
    g.proofOk = true := by
  exact (accepted_implies_reward_gate_obligations g hAccepted).left

theorem accepted_implies_policy_ok
    (g : Gate)
    (hAccepted : accepted g) :
    g.policyOk = true := by
  cases hPolicy : g.policyOk <;>
    simp [accepted, hostGuardsOk, hPolicy] at hAccepted ⊢

theorem accepted_implies_binding_ok
    (g : Gate)
    (hAccepted : accepted g) :
    g.bindingOk = true := by
  exact (host_guards_ok_iff_obligations g).mp hAccepted.1 |>.right.left

theorem accepted_implies_freshness_ok
    (g : Gate)
    (hAccepted : accepted g) :
    g.freshnessOk = true := by
  rcases (host_guards_ok_iff_obligations g).mp hAccepted.1 with
    ⟨_, _, _, hFreshness, _, _, _⟩
  exact hFreshness

theorem accepted_implies_unique_claim
    (g : Gate)
    (hAccepted : accepted g) :
    g.uniqueClaim = true := by
  exact (host_guards_ok_iff_obligations g).mp hAccepted.1 |>.right.right.right.right.left

theorem accepted_implies_recipient_differs_from_reward_pool
    (g : Gate)
    (hAccepted : accepted g) :
    g.recipientDiffersFromRewardPool = true := by
  exact (host_guards_ok_iff_obligations g).mp hAccepted.1 |>.right.right.right.right.right.left

theorem accepted_implies_reward_pool_has_budget
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolHasBudget = true := by
  rcases (host_guards_ok_iff_obligations g).mp hAccepted.1 with
    ⟨_, _, _, _, _, _, hBudget⟩
  exact hBudget

theorem not_accepted_without_proof
    (g : Gate)
    (hProof : g.proofOk = false) :
    ¬ accepted g := by
  intro hAccepted
  have hProofTrue := accepted_implies_proof_ok g hAccepted
  simp [hProof] at hProofTrue

theorem not_accepted_without_policy
    (g : Gate)
    (hPolicy : g.policyOk = false) :
    ¬ accepted g := by
  intro hAccepted
  have hPolicyTrue := accepted_implies_policy_ok g hAccepted
  simp [hPolicy] at hPolicyTrue

theorem not_accepted_without_binding
    (g : Gate)
    (hBinding : g.bindingOk = false) :
    ¬ accepted g := by
  intro hAccepted
  have hBindingTrue := accepted_implies_binding_ok g hAccepted
  simp [hBinding] at hBindingTrue

theorem not_accepted_without_freshness
    (g : Gate)
    (hFreshness : g.freshnessOk = false) :
    ¬ accepted g := by
  intro hAccepted
  have hFreshnessTrue := accepted_implies_freshness_ok g hAccepted
  simp [hFreshness] at hFreshnessTrue

theorem not_accepted_without_unique_claim
    (g : Gate)
    (hUnique : g.uniqueClaim = false) :
    ¬ accepted g := by
  intro hAccepted
  have hUniqueTrue := accepted_implies_unique_claim g hAccepted
  simp [hUnique] at hUniqueTrue

theorem duplicate_claim_not_accepted
    (g : Gate)
    (hUnique : g.uniqueClaim = false) :
    ¬ accepted g :=
  not_accepted_without_unique_claim g hUnique

theorem reward_pool_self_payment_not_accepted
    (g : Gate)
    (hDistinct : g.recipientDiffersFromRewardPool = false) :
    ¬ accepted g := by
  intro hAccepted
  have hDistinctTrue := accepted_implies_recipient_differs_from_reward_pool g hAccepted
  simp [hDistinct] at hDistinctTrue

theorem not_accepted_without_reward_budget
    (g : Gate)
    (hBudget : g.rewardPoolHasBudget = false) :
    ¬ accepted g := by
  intro hAccepted
  have hBudgetTrue := accepted_implies_reward_pool_has_budget g hAccepted
  simp [hBudget] at hBudgetTrue

theorem accepted_reward_delta_conservative
    (g : Gate)
    (hAccepted : accepted g) :
    conservativeDelta g :=
  hAccepted.2.2

theorem accepted_payout_preserves_pool_recipient_total
    (g : Gate)
    (recipientBalanceBefore : Nat)
    (hAccepted : accepted g) :
    g.rewardPoolAfter + (recipientBalanceBefore + g.rewardAmount) =
      g.rewardPoolBefore + recipientBalanceBefore := by
  rw [accepted_reward_delta_conservative g hAccepted]
  ac_rfl

theorem accepted_reward_positive
    (g : Gate)
    (hAccepted : accepted g) :
    0 < g.rewardAmount :=
  hAccepted.2.1

theorem not_accepted_with_zero_reward
    (g : Gate)
    (hReward : g.rewardAmount = 0) :
    ¬ accepted g := by
  intro hAccepted
  have hPositive : 0 < 0 := by
    simpa [hReward] using accepted_reward_positive g hAccepted
  exact (Nat.lt_irrefl 0) hPositive

theorem accepted_reward_after_le_before
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolAfter ≤ g.rewardPoolBefore := by
  rw [accepted_reward_delta_conservative g hAccepted]
  exact Nat.le_add_left g.rewardPoolAfter g.rewardAmount

theorem accepted_reward_amount_le_before
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardAmount ≤ g.rewardPoolBefore := by
  rw [accepted_reward_delta_conservative g hAccepted]
  exact Nat.le_add_right g.rewardAmount g.rewardPoolAfter

theorem accepted_reward_pool_before_positive
    (g : Gate)
    (hAccepted : accepted g) :
    0 < g.rewardPoolBefore := by
  exact Nat.lt_of_lt_of_le
    (accepted_reward_positive g hAccepted)
    (accepted_reward_amount_le_before g hAccepted)

theorem accepted_reward_after_lt_before
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolAfter < g.rewardPoolBefore := by
  rw [accepted_reward_delta_conservative g hAccepted]
  have h :
      g.rewardPoolAfter + 0 < g.rewardPoolAfter + g.rewardAmount :=
    Nat.add_lt_add_left hAccepted.2.1 g.rewardPoolAfter
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem accepted_reward_after_ne_before
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolAfter ≠ g.rewardPoolBefore := by
  exact Nat.ne_of_lt (accepted_reward_after_lt_before g hAccepted)

theorem accepted_reward_after_eq_before_sub_amount
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolAfter = g.rewardPoolBefore - g.rewardAmount := by
  rw [accepted_reward_delta_conservative g hAccepted]
  exact (Nat.add_sub_cancel_left g.rewardAmount g.rewardPoolAfter).symm

theorem scheduled_reward_positive
    (baseReward epoch : Nat) :
    0 < scheduledReward baseReward epoch := by
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (baseReward / (2 ^ epoch)))

theorem scheduled_reward_le_base_when_positive
    {baseReward epoch : Nat}
    (hBase : 0 < baseReward) :
    scheduledReward baseReward epoch ≤ baseReward := by
  have hOne : 1 ≤ baseReward := Nat.succ_le_iff.mpr hBase
  exact Nat.max_le.mpr ⟨hOne, Nat.div_le_self baseReward (2 ^ epoch)⟩

structure ScheduledGate extends Gate where
  baseReward : Nat
  epoch : Nat
  rewardMatchesSchedule : Bool

def scheduledAccepted (g : ScheduledGate) : Prop :=
  accepted g.toGate ∧
    g.rewardMatchesSchedule = true ∧
    g.rewardAmount = scheduledReward g.baseReward g.epoch

theorem scheduled_accepted_implies_base_gate_accepted
    (g : ScheduledGate)
    (hAccepted : scheduledAccepted g) :
    accepted g.toGate :=
  hAccepted.1

theorem not_scheduled_accepted_when_schedule_flag_false
    (g : ScheduledGate)
    (hSchedule : g.rewardMatchesSchedule = false) :
    ¬ scheduledAccepted g := by
  intro hAccepted
  have hScheduleTrue : g.rewardMatchesSchedule = true := hAccepted.2.1
  simp [hSchedule] at hScheduleTrue

theorem scheduled_accepted_reward_matches_schedule
    (g : ScheduledGate)
    (hAccepted : scheduledAccepted g) :
    g.rewardAmount = scheduledReward g.baseReward g.epoch :=
  hAccepted.2.2

theorem scheduled_accepted_reward_amount_le_base
    (g : ScheduledGate)
    (hBase : 0 < g.baseReward)
    (hAccepted : scheduledAccepted g) :
    g.rewardAmount ≤ g.baseReward := by
  rw [scheduled_accepted_reward_matches_schedule g hAccepted]
  exact scheduled_reward_le_base_when_positive hBase

theorem scheduled_accepted_reward_delta_conservative
    (g : ScheduledGate)
    (hAccepted : scheduledAccepted g) :
    conservativeDelta g.toGate :=
  accepted_reward_delta_conservative g.toGate
    (scheduled_accepted_implies_base_gate_accepted g hAccepted)

theorem scheduled_accepted_reward_after_le_before
    (g : ScheduledGate)
    (hAccepted : scheduledAccepted g) :
    g.rewardPoolAfter ≤ g.rewardPoolBefore :=
  accepted_reward_after_le_before g.toGate
    (scheduled_accepted_implies_base_gate_accepted g hAccepted)

end ZenoProofRewardGate

end TauSwap
