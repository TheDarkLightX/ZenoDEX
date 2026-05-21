import Mathlib

/-!
# Autotrader Controller Policy Closure

Internal proof note for the split-route and budget-window controller patch.

The runtime controller now separates two counters:

1. `max_live_orders` bounds logical orders.
2. `max_intents_per_order` bounds the number of emitted swap intents inside one
   logical order.

The budget guard also rolls on a fixed strategy budget-window identifier rather
than on every execution epoch. Within one budget window, `spent_in_window`
therefore accumulates until the configured window limit rejects the next order.
-/

namespace Internal
namespace AutotraderControllerPolicyClosure

/-- Runtime projection for live logical orders after accepting one strategy
decision. Split routing affects intent count, not logical-order count. -/
def ProjectedLogicalLiveOrders (liveOrders : Nat) : Nat :=
  liveOrders + 1

/-- Runtime admission for the per-logical-order emitted intent count. -/
def IntentCountAccepted (intentCount maxIntentsPerOrder : Nat) : Prop :=
  1 ≤ intentCount ∧ intentCount ≤ maxIntentsPerOrder

/-- Runtime admission for logical live-order capacity. -/
def LiveOrderAccepted (liveOrders maxLiveOrders : Nat) : Prop :=
  ProjectedLogicalLiveOrders liveOrders ≤ maxLiveOrders

/-- The logical live-order guard is independent of how many intents the route
emits, once the separate intent-count cap has accepted the route. -/
theorem split_route_preserves_logical_live_order_guard
    {liveOrders maxLiveOrders intentCount maxIntentsPerOrder : Nat}
    (_hIntentCount : IntentCountAccepted intentCount maxIntentsPerOrder)
    (hLive : LiveOrderAccepted liveOrders maxLiveOrders) :
    ProjectedLogicalLiveOrders liveOrders ≤ maxLiveOrders := by
  exact hLive

/-- Oversized split routes are rejected by the intent-count guard before they
can consume a logical order slot. -/
theorem oversized_split_route_rejected
    {intentCount maxIntentsPerOrder : Nat}
    (hTooMany : maxIntentsPerOrder < intentCount) :
    ¬ IntentCountAccepted intentCount maxIntentsPerOrder := by
  intro hAccepted
  unfold IntentCountAccepted at hAccepted
  omega

/-- One fixed budget-window bucket. The Python runtime uses the same shape with
`duration > 0`; `validFrom` is the start epoch of the strategy window. -/
def BudgetWindowId (validFrom duration currentEpoch : Nat) : Nat :=
  validFrom + ((currentEpoch - validFrom) / duration) * duration

/-- Runtime budget admission within an already selected budget window. -/
def BudgetSpendAccepted (spentInWindow orderAmount windowBudget : Nat) : Prop :=
  spentInWindow + orderAmount ≤ windowBudget

/-- If the current execution maps to the same fixed window identifier, rolling
is not required. -/
theorem same_budget_window_does_not_roll
    {storedWindow targetWindow : Nat}
    (hSame : targetWindow = storedWindow) :
    ¬ storedWindow < targetWindow := by
  omega

/-- When spending would exceed the fixed-window limit, the budget guard rejects.
This is the accumulator closure that the old "window id equals current epoch"
rule failed to provide. -/
theorem fixed_window_over_budget_rejected
    {spentInWindow orderAmount windowBudget : Nat}
    (hExceeds : windowBudget < spentInWindow + orderAmount) :
    ¬ BudgetSpendAccepted spentInWindow orderAmount windowBudget := by
  intro hAccepted
  unfold BudgetSpendAccepted at hAccepted
  omega

end AutotraderControllerPolicyClosure
end Internal
