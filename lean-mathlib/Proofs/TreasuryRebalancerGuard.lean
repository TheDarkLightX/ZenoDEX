import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Treasury Rebalancer Guard

This packet captures the arithmetic safety contract behind the non-live
`treasury_rebalancer_guard_v1` ESSO model.

The result is intentionally narrow: an admitted treasury rebalancer trade
preserves the declared loss and inventory budgets, and missing anti-abuse
flags make admission impossible. It does not prove that a strategy is
profitable or legally deployable.
-/

namespace Proofs
namespace TreasuryRebalancerGuard

/-- Bounded state carried by the treasury rebalancer guard. -/
structure State where
  treasuryBalance : ℕ
  maxDailyLossBudget : ℕ
  dailyLossUsed : ℕ
  liquidityBudget : ℕ
  inventoryExposureBps : ℕ
  maxInventoryBps : ℕ
  cooldownEpochs : ℕ
  lastTradeEpoch : ℕ
  paused : Bool
  admittedCount : ℕ
deriving Repr

/-- Public trade evidence supplied to the guard before a treasury trade. -/
structure Trade where
  nowEpoch : ℕ
  expectedEdge : ℕ
  costs : ℕ
  riskBuffer : ℕ
  tradeNotional : ℕ
  worstCaseLoss : ℕ
  inventoryAfterBps : ℕ
  oracleFresh : Bool
  publicRoute : Bool
  noPrivateOrderflow : Bool
  noUserSandwich : Bool
  noSelfTrade : Bool
deriving Repr

/-- State-level budget invariant. -/
def PolicyInvariant (s : State) : Prop :=
  s.dailyLossUsed ≤ s.maxDailyLossBudget ∧
    s.maxDailyLossBudget ≤ s.treasuryBalance ∧
    s.inventoryExposureBps ≤ s.maxInventoryBps

/-- All anti-abuse flags required for a treasury rebalancer trade. -/
def AntiAbuseFlagsOK (t : Trade) : Prop :=
  t.oracleFresh = true ∧
    t.publicRoute = true ∧
    t.noPrivateOrderflow = true ∧
    t.noUserSandwich = true ∧
    t.noSelfTrade = true

/-- Arithmetic admission checks independent of the anti-abuse booleans. -/
def ArithmeticOK (s : State) (t : Trade) : Prop :=
  0 < t.tradeNotional ∧
    t.tradeNotional ≤ s.liquidityBudget ∧
    t.inventoryAfterBps ≤ s.maxInventoryBps ∧
    t.costs + t.riskBuffer ≤ t.expectedEdge ∧
    s.dailyLossUsed + t.worstCaseLoss ≤ s.maxDailyLossBudget ∧
    s.lastTradeEpoch + s.cooldownEpochs ≤ t.nowEpoch ∧
    s.admittedCount < 100

/-- Full admission predicate for a treasury rebalancer trade. -/
def TradeAdmissible (s : State) (t : Trade) : Prop :=
  s.paused = false ∧ AntiAbuseFlagsOK t ∧ ArithmeticOK s t

/-- The state update performed by an admitted trade. -/
def applyTrade (s : State) (t : Trade) : State :=
  { s with
    dailyLossUsed := s.dailyLossUsed + t.worstCaseLoss
    inventoryExposureBps := t.inventoryAfterBps
    lastTradeEpoch := t.nowEpoch
    admittedCount := s.admittedCount + 1 }

theorem admissible_implies_not_paused
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    s.paused = false := by
  exact h.1

theorem admissible_implies_anti_abuse_flags
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    AntiAbuseFlagsOK t := by
  exact h.2.1

theorem admissible_implies_oracle_fresh
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.oracleFresh = true := by
  exact h.2.1.1

theorem admissible_implies_public_route
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.publicRoute = true := by
  exact h.2.1.2.1

theorem admissible_implies_no_private_orderflow
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.noPrivateOrderflow = true := by
  exact h.2.1.2.2.1

theorem admissible_implies_no_user_sandwich
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.noUserSandwich = true := by
  exact h.2.1.2.2.2.1

theorem admissible_implies_no_self_trade
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.noSelfTrade = true := by
  exact h.2.1.2.2.2.2

theorem admissible_implies_edge_covers_costs
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.costs + t.riskBuffer ≤ t.expectedEdge := by
  exact h.2.2.2.2.2.1

theorem admissible_implies_loss_budget_after
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    s.dailyLossUsed + t.worstCaseLoss ≤ s.maxDailyLossBudget := by
  exact h.2.2.2.2.2.2.1

theorem admissible_implies_inventory_after
    {s : State} {t : Trade} (h : TradeAdmissible s t) :
    t.inventoryAfterBps ≤ s.maxInventoryBps := by
  exact h.2.2.2.2.1

theorem applyTrade_preserves_policyInvariant
    {s : State} {t : Trade}
    (hInv : PolicyInvariant s)
    (hAdm : TradeAdmissible s t) :
    PolicyInvariant (applyTrade s t) := by
  rcases hInv with ⟨_hLoss, hBudget, _hInventory⟩
  exact
    ⟨by
      simpa [applyTrade] using admissible_implies_loss_budget_after hAdm,
     by
      simpa [applyTrade] using hBudget,
     by
      simpa [applyTrade] using admissible_implies_inventory_after hAdm⟩

theorem not_admissible_when_paused
    {s : State} {t : Trade} (hPaused : s.paused = true) :
    ¬ TradeAdmissible s t := by
  intro h
  have hNotPaused := admissible_implies_not_paused h
  rw [hPaused] at hNotPaused
  contradiction

theorem not_admissible_without_oracle
    {s : State} {t : Trade} (hOracle : t.oracleFresh = false) :
    ¬ TradeAdmissible s t := by
  intro h
  have hFresh := admissible_implies_oracle_fresh h
  rw [hOracle] at hFresh
  contradiction

theorem not_admissible_with_private_orderflow
    {s : State} {t : Trade} (hPrivate : t.noPrivateOrderflow = false) :
    ¬ TradeAdmissible s t := by
  intro h
  have hNoPrivate := admissible_implies_no_private_orderflow h
  rw [hPrivate] at hNoPrivate
  contradiction

theorem not_admissible_with_user_sandwich
    {s : State} {t : Trade} (hSandwich : t.noUserSandwich = false) :
    ¬ TradeAdmissible s t := by
  intro h
  have hNoSandwich := admissible_implies_no_user_sandwich h
  rw [hSandwich] at hNoSandwich
  contradiction

theorem not_admissible_with_self_trade
    {s : State} {t : Trade} (hSelfTrade : t.noSelfTrade = false) :
    ¬ TradeAdmissible s t := by
  intro h
  have hNoSelfTrade := admissible_implies_no_self_trade h
  rw [hSelfTrade] at hNoSelfTrade
  contradiction

theorem not_admissible_when_edge_below_cost_and_buffer
    {s : State} {t : Trade}
    (hEdge : t.expectedEdge < t.costs + t.riskBuffer) :
    ¬ TradeAdmissible s t := by
  intro h
  have hCover := admissible_implies_edge_covers_costs h
  omega

/-- A finite sequence of admitted treasury rebalancer trades. -/
inductive Trace : State → State → Prop
  | nil (s : State) : Trace s s
  | cons {s u v : State} (t : Trade)
      (hAdm : TradeAdmissible s t)
      (hRest : Trace (applyTrade s t) v) : Trace s v

theorem trace_preserves_policyInvariant
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    PolicyInvariant u := by
  induction hTrace with
  | nil s =>
      exact hInv
  | cons t hAdm hRest ih =>
      exact ih (applyTrade_preserves_policyInvariant hInv hAdm)

/-- If the initial state respects the policy invariant, every admitted finite
trace ends with reserved loss still inside the daily loss budget. -/
theorem trace_daily_loss_within_budget
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    u.dailyLossUsed ≤ u.maxDailyLossBudget := by
  exact (trace_preserves_policyInvariant hTrace hInv).1

/-- If the initial state respects the policy invariant, every admitted finite
trace ends with inventory exposure still inside the cap. -/
theorem trace_inventory_within_cap
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    u.inventoryExposureBps ≤ u.maxInventoryBps := by
  exact (trace_preserves_policyInvariant hTrace hInv).2.2

/-- Witness: a clean trade with enough edge and budget is admissible. -/
theorem witness_trade_admissible :
    let s : State :=
      { treasuryBalance := 1000
        maxDailyLossBudget := 100
        dailyLossUsed := 10
        liquidityBudget := 50
        inventoryExposureBps := 100
        maxInventoryBps := 1000
        cooldownEpochs := 2
        lastTradeEpoch := 7
        paused := false
        admittedCount := 3 }
    let t : Trade :=
      { nowEpoch := 9
        expectedEdge := 15
        costs := 7
        riskBuffer := 3
        tradeNotional := 25
        worstCaseLoss := 10
        inventoryAfterBps := 200
        oracleFresh := true
        publicRoute := true
        noPrivateOrderflow := true
        noUserSandwich := true
        noSelfTrade := true }
    TradeAdmissible s t := by
  norm_num [TradeAdmissible, AntiAbuseFlagsOK, ArithmeticOK]

end TreasuryRebalancerGuard
end Proofs
