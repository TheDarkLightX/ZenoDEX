import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Cascade safety for isolated-margin perpetuals

## Main results

* `isolated_margin_independence`: Updating account i preserves account j (i ≠ j).
* `total_conservation_two`: Two-account + fee_pool conservation under zero-net PnL.
* `cascade_impossible_isolated`: Maintenance-safe + bounded PnL → all solvent.
* `post_pnl_lower_bound`: Tighter bound on post-PnL collateral.

## Key insight

Under isolated margin, each account's collateral is independent. Cascading
liquidation requires cross-account state dependency, which isolation prevents.
One account's liquidation cannot worsen another account's collateral.
-/

namespace Proofs

namespace PerpCascadeSafety

/-- Isolated margin independence: updating account i preserves account j (i ≠ j).
    This is the core isolation property: liquidating one position cannot
    affect another position's collateral. -/
theorem isolated_margin_independence
    {n : ℕ} (accounts : Fin n → ℚ) (i j : Fin n) (hij : i ≠ j)
    (f : ℚ → ℚ) (accounts' : Fin n → ℚ)
    (h : ∀ k, accounts' k = if k = i then f (accounts i) else accounts k) :
    accounts' j = accounts j := by
  rw [h j, if_neg (Ne.symm hij)]

/-- Two-account system value conservation: if PnL transfers and fee deltas
    net to zero, total system value is preserved. -/
theorem total_conservation_two
    (coll_a coll_b pnl_a pnl_b fee_pool fee_delta : ℚ)
    (h_net : pnl_a + pnl_b + fee_delta = 0) :
    (coll_a + pnl_a) + (coll_b + pnl_b) + (fee_pool + fee_delta)
    = coll_a + coll_b + fee_pool := by
  linarith

/-- Cascade impossibility under isolated margin: if each account independently
    has collateral ≥ maintenance and PnL loss is bounded by maintenance,
    then every account remains solvent. The bound is LOCAL per account. -/
theorem cascade_impossible_isolated
    {n : ℕ} (colls maint pnls : Fin n → ℚ)
    (h_safe : ∀ i, maint i ≤ colls i)
    (h_bounded : ∀ i, -(maint i) ≤ pnls i) :
    ∀ i, 0 ≤ colls i + pnls i := by
  intro i; linarith [h_safe i, h_bounded i]

/-- Post-PnL lower bound: collateral after PnL ≥ collateral - maintenance. -/
theorem post_pnl_lower_bound
    (coll maint pnl : ℚ)
    (h_bounded : -(maint) ≤ pnl) :
    coll - maint ≤ coll + pnl := by
  linarith

/-! ## Non-vacuity witnesses -/

/-- Witness: isolated margin independence — updating account 0 in a 3-account
    system preserves accounts 1 and 2. -/
theorem witness_isolation :
    let accounts : Fin 3 → ℚ := ![1000, 2000, 3000]
    let accounts' : Fin 3 → ℚ := ![0, 2000, 3000]
    -- Account 1 is preserved after liquidating account 0
    accounts' 1 = accounts 1 ∧ accounts' 2 = accounts 2 := by
  constructor <;> native_decide

/-- Witness: 2-account conservation with concrete values.
    PnL_a=300, PnL_b=-350, fee=50 → net=0, total preserved. -/
theorem witness_conservation :
    let coll_a : ℚ := 1000
    let coll_b : ℚ := 2000
    let pnl_a : ℚ := 300
    let pnl_b : ℚ := -350
    let fee_pool : ℚ := 500
    let fee_delta : ℚ := 50
    (coll_a + pnl_a) + (coll_b + pnl_b) + (fee_pool + fee_delta)
    = coll_a + coll_b + fee_pool := by
  norm_num

/-- Witness: cascade impossible — account with c=100, m=80, pnl=-70 survives. -/
theorem witness_no_cascade :
    let c : ℚ := 100
    let m : ℚ := 80
    let pnl : ℚ := -70
    0 ≤ c + pnl ∧ m ≤ c ∧ -(m) ≤ pnl := by
  norm_num

/-- Witness: post-PnL lower bound — c=100, m=80, pnl=-70 → c-m=20 ≤ c+pnl=30. -/
theorem witness_post_pnl :
    let c : ℚ := 100
    let m : ℚ := 80
    let pnl : ℚ := -70
    c - m ≤ c + pnl ∧ -(m) ≤ pnl := by
  norm_num

end PerpCascadeSafety

end Proofs
