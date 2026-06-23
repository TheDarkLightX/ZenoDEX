/-!
# Perp live-risk parameter monotonicity

This file records the formal target behind the clearinghouse runtime guard:
while positions are live, market-parameter updates may tighten or preserve risk
controls, but must not loosen oracle movement, oracle staleness, margin,
position-cap, or liquidation-penalty controls.
-/

namespace Proofs

namespace PerpLiveRiskParamMonotonicity

structure RiskParams where
  maxOracleMoveBps : Nat
  maxOracleStalenessEpochs : Nat
  initialMarginBps : Nat
  maintenanceMarginBps : Nat
  maxPositionAbs : Nat
  liquidationPenaltyBps : Nat

/-- `new` does not loosen any live risk knob relative to `old`.

Margins are lower bounds, so non-loosening means they do not decrease. Oracle
movement, staleness, max position, and liquidation penalty are upper bounds, so
non-loosening means they do not increase. -/
def LiveRiskNotLoosened (old new : RiskParams) : Prop :=
  new.maxOracleMoveBps ≤ old.maxOracleMoveBps ∧
  new.maxOracleStalenessEpochs ≤ old.maxOracleStalenessEpochs ∧
  old.initialMarginBps ≤ new.initialMarginBps ∧
  old.maintenanceMarginBps ≤ new.maintenanceMarginBps ∧
  new.maxPositionAbs ≤ old.maxPositionAbs ∧
  new.liquidationPenaltyBps ≤ old.liquidationPenaltyBps

theorem preserves_oracle_move_admissibility
    {old new : RiskParams} {moveBps : Nat}
    (h : LiveRiskNotLoosened old new)
    (hm : moveBps ≤ new.maxOracleMoveBps) :
    moveBps ≤ old.maxOracleMoveBps := by
  exact Nat.le_trans hm h.1

theorem preserves_oracle_staleness_admissibility
    {old new : RiskParams} {stalenessEpochs : Nat}
    (h : LiveRiskNotLoosened old new)
    (hs : stalenessEpochs ≤ new.maxOracleStalenessEpochs) :
    stalenessEpochs ≤ old.maxOracleStalenessEpochs := by
  exact Nat.le_trans hs h.2.1

theorem preserves_initial_margin_floor
    {old new : RiskParams} {requiredMarginBps : Nat}
    (h : LiveRiskNotLoosened old new)
    (hr : requiredMarginBps ≤ old.initialMarginBps) :
    requiredMarginBps ≤ new.initialMarginBps := by
  exact Nat.le_trans hr h.2.2.1

theorem preserves_maintenance_margin_floor
    {old new : RiskParams} {requiredMarginBps : Nat}
    (h : LiveRiskNotLoosened old new)
    (hr : requiredMarginBps ≤ old.maintenanceMarginBps) :
    requiredMarginBps ≤ new.maintenanceMarginBps := by
  exact Nat.le_trans hr h.2.2.2.1

theorem preserves_position_cap_admissibility
    {old new : RiskParams} {positionAbs : Nat}
    (h : LiveRiskNotLoosened old new)
    (hp : positionAbs ≤ new.maxPositionAbs) :
    positionAbs ≤ old.maxPositionAbs := by
  exact Nat.le_trans hp h.2.2.2.2.1

theorem max_oracle_move_increase_contradicts_live_guard
    {old new : RiskParams}
    (h : LiveRiskNotLoosened old new)
    (hincrease : old.maxOracleMoveBps < new.maxOracleMoveBps) :
    False := by
  exact (Nat.not_lt_of_ge h.1) hincrease

theorem witness_live_risk_not_loosened :
    LiveRiskNotLoosened
      { maxOracleMoveBps := 500
        maxOracleStalenessEpochs := 100
        initialMarginBps := 1000
        maintenanceMarginBps := 600
        maxPositionAbs := 2000
        liquidationPenaltyBps := 50 }
      { maxOracleMoveBps := 400
        maxOracleStalenessEpochs := 90
        initialMarginBps := 1100
        maintenanceMarginBps := 700
        maxPositionAbs := 1500
        liquidationPenaltyBps := 40 } := by
  unfold LiveRiskNotLoosened
  decide

end PerpLiveRiskParamMonotonicity

end Proofs
