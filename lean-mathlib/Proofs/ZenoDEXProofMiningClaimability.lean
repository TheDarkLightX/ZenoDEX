/-!
# ZenoDEX Proof-Mining Claimability and ZenoProof Reward Gate

Small formal hardening lemmas for the proof-mining status endpoint and the
bounded ZenoProof reward-payout bridge.

The Python runtime exposes these checks as public status fields. These lemmas
record the math-level obligations that matter for the current disaster-search
witnesses: missing verified proof context and stale runtime balance snapshots
cannot produce a claimable proof-mining status, and accepted ZenoProof reward
gates preserve the conservative reward-pool delta.
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
      s.proposalHashMatchesContext = true ∧
      s.verifiedContextPresent = true ∧
      s.rewardPoolBalanceNonnegative = true ∧
      runtimeBindingsOk s = true ∧
      s.managerOk = true := by
  simp [claimable, and_assoc]

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

theorem not_claimable_with_wrong_proposal
    (s : Status)
    (hProposal : s.proposalHashMatchesContext = false) :
    claimable s = false := by
  simp [claimable, hProposal]

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

namespace ZenoProofRewardGate

structure Gate where
  proofOk : Bool
  bindingOk : Bool
  policyOk : Bool
  freshnessOk : Bool
  uniqueClaim : Bool
  rewardPoolHasBudget : Bool
  rewardPoolBefore : Nat
  rewardAmount : Nat
  rewardPoolAfter : Nat

def hostGuardsOk (g : Gate) : Bool :=
  g.proofOk &&
    g.bindingOk &&
    g.policyOk &&
    g.freshnessOk &&
    g.uniqueClaim &&
    g.rewardPoolHasBudget

def conservativeDelta (g : Gate) : Prop :=
  g.rewardPoolBefore = g.rewardAmount + g.rewardPoolAfter

def accepted (g : Gate) : Prop :=
  hostGuardsOk g = true ∧
    0 < g.rewardAmount ∧
    conservativeDelta g

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
      g.rewardPoolHasBudget = true := by
  simp [hostGuardsOk, and_assoc]

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

theorem accepted_implies_unique_claim
    (g : Gate)
    (hAccepted : accepted g) :
    g.uniqueClaim = true := by
  exact (host_guards_ok_iff_obligations g).mp hAccepted.1 |>.right.right.right.right.left

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

theorem not_accepted_without_unique_claim
    (g : Gate)
    (hUnique : g.uniqueClaim = false) :
    ¬ accepted g := by
  intro hAccepted
  have hUniqueTrue := accepted_implies_unique_claim g hAccepted
  simp [hUnique] at hUniqueTrue

theorem accepted_reward_delta_conservative
    (g : Gate)
    (hAccepted : accepted g) :
    conservativeDelta g :=
  hAccepted.2.2

theorem accepted_reward_positive
    (g : Gate)
    (hAccepted : accepted g) :
    0 < g.rewardAmount :=
  hAccepted.2.1

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

theorem accepted_reward_after_lt_before
    (g : Gate)
    (hAccepted : accepted g) :
    g.rewardPoolAfter < g.rewardPoolBefore := by
  rw [accepted_reward_delta_conservative g hAccepted]
  have h :
      g.rewardPoolAfter + 0 < g.rewardPoolAfter + g.rewardAmount :=
    Nat.add_lt_add_left hAccepted.2.1 g.rewardPoolAfter
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

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

end ZenoProofRewardGate

end TauSwap
