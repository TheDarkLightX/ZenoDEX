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

theorem accepted_implies_host_guards_ok
    (g : Gate)
    (hAccepted : accepted g) :
    hostGuardsOk g = true :=
  hAccepted.1

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

end ZenoProofRewardGate

end TauSwap
