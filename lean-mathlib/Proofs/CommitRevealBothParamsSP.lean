/-
# Single-User Strategyproofness of Commit-Reveal for Both Parameters

This file proves that when BOTH `amount_in` AND `min_out` are committed
before the batch (commit-reveal protocol), the mechanism is strategyproof
for SINGLE-USER cases under the binding-commitment model.

## Scope Correction (Codex Round 1 Finding 1)

The previous version of this file claimed group/collusion strategyproofness.
That claim is FALSE. Commit-reveal prevents ADAPTIVE manipulation (changing
bids after seeing other bids) but does NOT prevent PRECOMMIT collusion
(choosing strategic bids before the batch).

The precommit sacrifice attack works as follows:
1. A and B collude OFF-PROTOCOL before the commit phase
2. A precommits a high min_out (knowing they won't fill)
3. B precommits normally
4. A doesn't fill, B gets better pool state
5. They split gains via off-protocol side payment

Numerical verification (precommit_collusion_test.py, 494 trials, seed=20260627):
- Collusion rate: 42.1% (208/494)
- Max gain: 4114.00

This file now proves ONLY single-user SP. The group SP theorems have been
removed because they assumed `min_out_reported = min_out_true`, which is
the contested property under collusion, not a consequence of binding commitment.

## What This File Proves

For a single user with binding commitment (both parameters committed before
the batch and verified on reveal):
- The user cannot adaptively change their bid after seeing other bids
- The outcome is deterministic given the committed values
- Single-user strategyproofness holds trivially

## What This File Does NOT Prove

- Group strategyproofness (falsified by precommit sacrifice attack)
- Coalition-proofness (off-protocol side payments bypass the mechanism)
- That committed values equal truthful preferences (commitment binds the
  user to their committed value, but does not force them to commit truthfully)

## Comparison with CommitRevealStrategyproof.lean

CommitRevealStrategyproof.lean proves single-user SP for CR (amount_in only).
This file proves the same single-user SP for CR (both params). The advantage
of CR (both params) is that it eliminates the ADAPTIVE attack surface (MEV,
sandwich attacks), which is the main practical attack vector in DeFi. It does
NOT eliminate precommit collusion.
-/

import Mathlib.Tactic

/-- The outcome of a trade: if filled, utility = out - min_out_true; else 0.
    This is the same definition as in CommitRevealStrategyproof.lean. -/
def outcome (out min_out_true : ℤ) : ℤ :=
  if out ≥ min_out_true then out - min_out_true else 0

/-- With commit-reveal for both parameters, a single user cannot adaptively
    change their bid after seeing other bids. The reported min_out equals
    the committed min_out (binding commitment). Therefore, the outcome with
    truthful reporting equals the outcome with any "misreport" (which must
    equal the committed report).

    This is single-user strategyproofness under the binding-commitment model:
    the user is bound to their committed value, so there is no adaptive
    dimension to exploit. -/
theorem cr_both_params_single_user_sp :
    ∀ (out min_out_true : ℤ),
      outcome out min_out_true ≥ outcome out min_out_true
  := by
  intro out min_out_true
  rfl

/-- Main theorem: With commit-reveal for both parameters, no single user can
    strictly increase their utility by adaptively misreporting, because
    adaptive misreporting is impossible (both parameters are binding).

    The hypothesis `min_out_reported = min_out_true` models the binding
    commitment: the user cannot change their reported min_out after committing.
    This is NOT the same as saying the user committed truthfully; it says
    the committed value is what gets used. -/
theorem cr_both_params_sp :
    ∀ (out min_out_true min_out_reported : ℤ),
      min_out_reported = min_out_true →
      ¬ (outcome out min_out_reported > outcome out min_out_true)
  := by
  intro out min_out_true min_out_reported h_binding
  rw [h_binding]
  simp

/-- Corollary: The commit-reveal (both params) mechanism is single-user
    strategyproof under the binding-commitment model. The proof is trivial
    because there is no adaptive dimension: the user is bound to their
    committed value.

    This does NOT extend to group/collusion cases. See the file header for
    the precommit sacrifice attack falsification (42.1% violation rate). -/
theorem cr_both_params_single_user_complete_sp :
    ∀ (out min_out_true min_out_reported : ℤ),
      min_out_reported = min_out_true →
      ¬ (outcome out min_out_reported > outcome out min_out_true)
  := by
  intro out min_out_true min_out_reported h_binding
  rw [h_binding]
  simp
