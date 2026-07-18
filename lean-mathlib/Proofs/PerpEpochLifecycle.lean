import Mathlib.Tactic

/-!
# Perpetual Epoch Lifecycle

This module records the small transition contract exposed by the post-audit
functional core.  It is intentionally narrower than the full perps model: it
proves the cross-action lifecycle and Oracle-usability decision only.  State
arithmetic, PnL, liquidation, runtime parsing, authorization, and consensus-time
provenance remain separate refinement obligations.
-/

namespace ZenoDEX.PerpEpochLifecycle

inductive Phase where
  | open
  | pricePublished
  | settled
  deriving DecidableEq, Repr

inductive Action where
  | advanceEpoch
  | settleEpoch
  | other
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  nowEpoch : Nat
  clearingPriceSeen : Bool
  clearingPriceEpoch : Nat
  oracleSeen : Bool
  oracleLastUpdateEpoch : Nat
  indexPriceE8 : Nat
  maxOracleStalenessEpochs : Nat
  deriving DecidableEq, Repr

/-- Settlement may rely on an Oracle snapshot only when it is seen, positive,
not from the future, and no older than the committed staleness bound. -/
def oracleUsable (state : State) : Bool :=
  state.oracleSeen &&
    decide (0 < state.indexPriceE8) &&
    decide (state.oracleLastUpdateEpoch ≤ state.nowEpoch) &&
    decide (
      state.nowEpoch - state.oracleLastUpdateEpoch ≤
        state.maxOracleStalenessEpochs
    )

/-- Cross-action lifecycle admission.  Action-local arithmetic guards compose
with this decision in the implementation. -/
def lifecycleAllowed (state : State) : Action → Bool
  | .advanceEpoch => decide (state.phase ≠ .pricePublished)
  | .settleEpoch =>
      decide (state.phase = .pricePublished) &&
        state.clearingPriceSeen &&
        decide (state.clearingPriceEpoch = state.nowEpoch) &&
        decide (state.oracleLastUpdateEpoch < state.nowEpoch) &&
        oracleUsable state
  | .other => true

theorem published_price_blocks_epoch_advance
    (state : State)
    (published : state.phase = .pricePublished) :
    lifecycleAllowed state .advanceEpoch = false := by
  simp [lifecycleAllowed, published]

theorem open_allows_epoch_advance
    (state : State)
    (openPhase : state.phase = .open) :
    lifecycleAllowed state .advanceEpoch = true := by
  simp [lifecycleAllowed, openPhase]

theorem settled_allows_epoch_advance
    (state : State)
    (settledPhase : state.phase = .settled) :
    lifecycleAllowed state .advanceEpoch = true := by
  simp [lifecycleAllowed, settledPhase]

theorem advance_allowed_iff_not_published (state : State) :
    lifecycleAllowed state .advanceEpoch = true ↔
      state.phase ≠ .pricePublished := by
  cases state.phase <;> simp [lifecycleAllowed]

def baseSettlementState : State :=
  {
    phase := .pricePublished
    nowEpoch := 5
    clearingPriceSeen := true
    clearingPriceEpoch := 5
    oracleSeen := true
    oracleLastUpdateEpoch := 3
    indexPriceE8 := 100000000
    maxOracleStalenessEpochs := 2
  }

theorem unseen_oracle_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with
        oracleSeen := false
        oracleLastUpdateEpoch := 0
        indexPriceE8 := 0 }
      .settleEpoch = false := by
  decide

theorem zero_index_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with indexPriceE8 := 0 }
      .settleEpoch = false := by
  decide

theorem stale_by_one_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with oracleLastUpdateEpoch := 2 }
      .settleEpoch = false := by
  decide

theorem exact_freshness_boundary_allows_settlement :
    lifecycleAllowed baseSettlementState .settleEpoch = true := by
  decide

theorem same_epoch_oracle_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with oracleLastUpdateEpoch := 5 }
      .settleEpoch = false := by
  decide

theorem wrong_clearing_epoch_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with clearingPriceEpoch := 4 }
      .settleEpoch = false := by
  decide

theorem missing_clearing_price_blocks_settlement :
    lifecycleAllowed
      { baseSettlementState with clearingPriceSeen := false }
      .settleEpoch = false := by
  decide

end ZenoDEX.PerpEpochLifecycle
