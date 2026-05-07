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

/-- Governance policy update for the rebalancer guard. -/
structure PolicyUpdate where
  newMaxDailyLossBudget : ℕ
  newLiquidityBudget : ℕ
  newMaxInventoryBps : ℕ
  newCooldownEpochs : ℕ
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

/-- Governance may change policy only when the new bounds still cover current
reserved loss and inventory, and the loss budget remains treasury-backed. -/
def PolicyUpdateAdmissible (s : State) (p : PolicyUpdate) : Prop :=
  p.newMaxDailyLossBudget ≤ s.treasuryBalance ∧
    s.dailyLossUsed ≤ p.newMaxDailyLossBudget ∧
    s.inventoryExposureBps ≤ p.newMaxInventoryBps

/-- The state update performed by an admitted trade. -/
def applyTrade (s : State) (t : Trade) : State :=
  { s with
    dailyLossUsed := s.dailyLossUsed + t.worstCaseLoss
    inventoryExposureBps := t.inventoryAfterBps
    lastTradeEpoch := t.nowEpoch
    admittedCount := s.admittedCount + 1 }

/-- The state update performed by an admitted governance policy change. -/
def applyPolicyUpdate (s : State) (p : PolicyUpdate) : State :=
  { s with
    maxDailyLossBudget := p.newMaxDailyLossBudget
    liquidityBudget := p.newLiquidityBudget
    maxInventoryBps := p.newMaxInventoryBps
    cooldownEpochs := p.newCooldownEpochs }

/-- The state update performed by pause/unpause control. -/
def applyPause (s : State) (paused : Bool) : State :=
  { s with paused := paused }

theorem applyTrade_treasuryBalance_eq
    (s : State) (t : Trade) :
    (applyTrade s t).treasuryBalance = s.treasuryBalance := by
  simp [applyTrade]

theorem applyTrade_maxDailyLossBudget_eq
    (s : State) (t : Trade) :
    (applyTrade s t).maxDailyLossBudget = s.maxDailyLossBudget := by
  simp [applyTrade]

theorem applyTrade_maxInventoryBps_eq
    (s : State) (t : Trade) :
    (applyTrade s t).maxInventoryBps = s.maxInventoryBps := by
  simp [applyTrade]

theorem applyTrade_liquidityBudget_eq
    (s : State) (t : Trade) :
    (applyTrade s t).liquidityBudget = s.liquidityBudget := by
  simp [applyTrade]

theorem applyTrade_dailyLossUsed_monotone
    (s : State) (t : Trade) :
    s.dailyLossUsed ≤ (applyTrade s t).dailyLossUsed := by
  simp [applyTrade]

theorem applyTrade_admittedCount_monotone
    (s : State) (t : Trade) :
    s.admittedCount ≤ (applyTrade s t).admittedCount := by
  simp [applyTrade]

theorem applyPolicyUpdate_treasuryBalance_eq
    (s : State) (p : PolicyUpdate) :
    (applyPolicyUpdate s p).treasuryBalance = s.treasuryBalance := by
  simp [applyPolicyUpdate]

theorem applyPolicyUpdate_dailyLossUsed_eq
    (s : State) (p : PolicyUpdate) :
    (applyPolicyUpdate s p).dailyLossUsed = s.dailyLossUsed := by
  simp [applyPolicyUpdate]

theorem applyPolicyUpdate_inventoryExposureBps_eq
    (s : State) (p : PolicyUpdate) :
    (applyPolicyUpdate s p).inventoryExposureBps = s.inventoryExposureBps := by
  simp [applyPolicyUpdate]

theorem applyPolicyUpdate_preserves_policyInvariant
    {s : State} {p : PolicyUpdate}
    (hAdm : PolicyUpdateAdmissible s p) :
    PolicyInvariant (applyPolicyUpdate s p) := by
  rcases hAdm with ⟨hBacked, hLoss, hInventory⟩
  exact
    ⟨by simpa [applyPolicyUpdate] using hLoss,
      by simpa [applyPolicyUpdate] using hBacked,
      by simpa [applyPolicyUpdate] using hInventory⟩

theorem applyPause_preserves_policyInvariant
    {s : State} {paused : Bool}
    (hInv : PolicyInvariant s) :
    PolicyInvariant (applyPause s paused) := by
  simpa [applyPause] using hInv

theorem not_policyUpdateAdmissible_when_budget_unbacked
    {s : State} {p : PolicyUpdate}
    (hBudget : s.treasuryBalance < p.newMaxDailyLossBudget) :
    ¬ PolicyUpdateAdmissible s p := by
  intro h
  exact (not_lt_of_ge h.1) hBudget

theorem not_policyUpdateAdmissible_when_budget_below_reserved_loss
    {s : State} {p : PolicyUpdate}
    (hLoss : p.newMaxDailyLossBudget < s.dailyLossUsed) :
    ¬ PolicyUpdateAdmissible s p := by
  intro h
  exact (not_lt_of_ge h.2.1) hLoss

theorem not_policyUpdateAdmissible_when_cap_below_inventory
    {s : State} {p : PolicyUpdate}
    (hInventory : p.newMaxInventoryBps < s.inventoryExposureBps) :
    ¬ PolicyUpdateAdmissible s p := by
  intro h
  exact (not_lt_of_ge h.2.2) hInventory

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

/-- A finite sequence over the full non-live guard surface:
admitted trades, admitted policy updates, and pause/unpause control. -/
inductive SystemTrace : State → State → Prop
  | nil (s : State) : SystemTrace s s
  | trade {s v : State} (t : Trade)
      (hAdm : TradeAdmissible s t)
      (hRest : SystemTrace (applyTrade s t) v) : SystemTrace s v
  | policy {s v : State} (p : PolicyUpdate)
      (hAdm : PolicyUpdateAdmissible s p)
      (hRest : SystemTrace (applyPolicyUpdate s p) v) : SystemTrace s v
  | pause {s v : State} (paused : Bool)
      (hRest : SystemTrace (applyPause s paused) v) : SystemTrace s v

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

theorem systemTrace_preserves_policyInvariant
    {s u : State}
    (hTrace : SystemTrace s u)
    (hInv : PolicyInvariant s) :
    PolicyInvariant u := by
  induction hTrace with
  | nil s =>
      exact hInv
  | trade t hAdm _hRest ih =>
      exact ih (applyTrade_preserves_policyInvariant hInv hAdm)
  | policy p hAdm _hRest ih =>
      exact ih (applyPolicyUpdate_preserves_policyInvariant hAdm)
  | pause paused _hRest ih =>
      exact ih (applyPause_preserves_policyInvariant hInv)

theorem systemTrace_daily_loss_within_budget
    {s u : State}
    (hTrace : SystemTrace s u)
    (hInv : PolicyInvariant s) :
    u.dailyLossUsed ≤ u.maxDailyLossBudget := by
  exact (systemTrace_preserves_policyInvariant hTrace hInv).1

theorem systemTrace_inventory_within_cap
    {s u : State}
    (hTrace : SystemTrace s u)
    (hInv : PolicyInvariant s) :
    u.inventoryExposureBps ≤ u.maxInventoryBps := by
  exact (systemTrace_preserves_policyInvariant hTrace hInv).2.2

theorem systemTrace_budget_backed_by_treasury
    {s u : State}
    (hTrace : SystemTrace s u)
    (hInv : PolicyInvariant s) :
    u.maxDailyLossBudget ≤ u.treasuryBalance := by
  exact (systemTrace_preserves_policyInvariant hTrace hInv).2.1

theorem trace_treasuryBalance_eq
    {s u : State}
    (hTrace : Trace s u) :
    u.treasuryBalance = s.treasuryBalance := by
  induction hTrace with
  | nil s =>
      rfl
  | cons t _hAdm _hRest ih =>
      simpa [applyTrade] using ih

theorem trace_maxDailyLossBudget_eq
    {s u : State}
    (hTrace : Trace s u) :
    u.maxDailyLossBudget = s.maxDailyLossBudget := by
  induction hTrace with
  | nil s =>
      rfl
  | cons t _hAdm _hRest ih =>
      simpa [applyTrade] using ih

theorem trace_maxInventoryBps_eq
    {s u : State}
    (hTrace : Trace s u) :
    u.maxInventoryBps = s.maxInventoryBps := by
  induction hTrace with
  | nil s =>
      rfl
  | cons t _hAdm _hRest ih =>
      simpa [applyTrade] using ih

theorem trace_liquidityBudget_eq
    {s u : State}
    (hTrace : Trace s u) :
    u.liquidityBudget = s.liquidityBudget := by
  induction hTrace with
  | nil s =>
      rfl
  | cons t _hAdm _hRest ih =>
      simpa [applyTrade] using ih

theorem trace_dailyLossUsed_monotone
    {s u : State}
    (hTrace : Trace s u) :
    s.dailyLossUsed ≤ u.dailyLossUsed := by
  induction hTrace with
  | nil s =>
      exact le_rfl
  | cons t _hAdm _hRest ih =>
      exact (applyTrade_dailyLossUsed_monotone _ t).trans ih

theorem trace_admittedCount_monotone
    {s u : State}
    (hTrace : Trace s u) :
    s.admittedCount ≤ u.admittedCount := by
  induction hTrace with
  | nil s =>
      exact le_rfl
  | cons t _hAdm _hRest ih =>
      exact (applyTrade_admittedCount_monotone _ t).trans ih

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

/-- In a pure admitted-trade trace, the daily loss budget itself is not changed,
so final reserved loss remains bounded by the initial daily loss budget. -/
theorem trace_daily_loss_within_initial_budget
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    u.dailyLossUsed ≤ s.maxDailyLossBudget := by
  have hWithin := trace_daily_loss_within_budget hTrace hInv
  simpa [trace_maxDailyLossBudget_eq hTrace] using hWithin

/-- In a pure admitted-trade trace, the inventory cap itself is not changed,
so final inventory exposure remains bounded by the initial inventory cap. -/
theorem trace_inventory_within_initial_cap
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    u.inventoryExposureBps ≤ s.maxInventoryBps := by
  have hWithin := trace_inventory_within_cap hTrace hInv
  simpa [trace_maxInventoryBps_eq hTrace] using hWithin

/-- Combining monotonic reserved loss with the static budget gives the strongest
pure-trace budget envelope: final reserved loss is between the initial reserved
loss and the initial daily budget. -/
theorem trace_reserved_loss_between_initial_and_budget
    {s u : State}
    (hTrace : Trace s u)
    (hInv : PolicyInvariant s) :
    s.dailyLossUsed ≤ u.dailyLossUsed ∧
      u.dailyLossUsed ≤ s.maxDailyLossBudget := by
  exact
    ⟨trace_dailyLossUsed_monotone hTrace,
      trace_daily_loss_within_initial_budget hTrace hInv⟩

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
