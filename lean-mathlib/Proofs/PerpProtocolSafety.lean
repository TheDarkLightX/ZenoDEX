import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Proofs.PerpMechanismDesign
import Proofs.PerpGameTheory
import Proofs.PerpEpochSafety
import Proofs.SettlementAlgebra

/-!
# Perpetual Protocol Safety — Composition Theorem

Unifies collateral safety (PerpEpochSafety), game-theoretic incentives (PerpGameTheory),
and conservation (SettlementAlgebra) into a single composition theorem.

## Key Results

- `unified_perp_safety`: Four-layer safety proof combining solvency, liquidation profitability,
  budget balance, and individual rationality
- `no_value_creation`: Net value flow across all participants is zero
- `interaction_budget`: Cross-mechanism conservation: total collateral + insurance ≥ 0
- `witness_unified_perp_safety`: Full concrete witness with `norm_num` / `simp`
-/

namespace Proofs

namespace PerpProtocolSafety

open PerpGameTheory PerpEpochSafety PerpMechanismDesign

/-! ## No-Value-Creation (Zero-Sum Property) -/

/-- No value creation: in a two-party perp with long position `pos` and short
    position `−pos`, the net PnL from any price change `δP` is zero.
    Derived structurally from opposite positions via `ring`, not assumed. -/
theorem no_value_creation (pos δP : ℚ) :
    pos * δP + (-pos) * δP = 0 := by ring

/-- Cross-mechanism conservation: when per-account collateral is non-negative
    (as guaranteed by epoch safety) and insurance is non-negative,
    the total system value is non-negative. Monotonicity of addition over ℚ. -/
theorem interaction_budget
    (coll_a coll_b insurance : ℚ)
    (hcoll_a : 0 ≤ coll_a) (hcoll_b : 0 ≤ coll_b) (hins : 0 ≤ insurance) :
    0 ≤ coll_a + coll_b + insurance := by
  linarith

/-- Insurance fund accounting identity: rearranging
    `balance = initial + fee_income − claims_paid` yields
    `balance + claims_paid = initial + fee_income`. -/
theorem insurance_conservation
    (initial fee_income claims_paid balance : ℚ)
    (h : balance = initial + fee_income - claims_paid) :
    balance + claims_paid = initial + fee_income := by
  linarith

/-! ## Unified Protocol Safety Theorem -/

/-- Unified perpetual protocol safety: composition of four layers.

    **Layer 1 (Solvency)**: Collateral ≥ 0 after any bounded oracle move,
    given maintenance margin ≥ oracle move bound. From `PerpEpochSafety`.

    **Layer 2 (Liquidation Profitability)**: Net profit `reward − gas_cost ≥ 0`
    when reward ≥ gas cost. From `PerpGameTheory.liquidation_dominant_strategy`.
    For the formal game-theoretic dominant-strategy proof, see `liquidation_game_dominant`.

    **Layer 3 (Budget Balance)**: Symmetric funding settlements have zero net flow.
    From `PerpGameTheory`.

    **Layer 4 (Individual Rationality)**: Liquidation reward is non-negative,
    so liquidator participation is individually rational. -/
theorem unified_perp_safety
    (pos P P' C m maint penalty_bps gas_cost rate : ℚ)
    (hP : 0 ≤ P)
    (hmaint : m ≤ maint)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hC : |pos| * P * maint / 10000 ≤ C)
    (hpen : 0 ≤ penalty_bps)
    (hgas : gas_cost ≤ liquidation_reward pos P penalty_bps) :
    -- Layer 1: Solvency after oracle move
    (0 ≤ C + pos * (P' - P)) ∧
    -- Layer 2: Liquidation profitability (net profit ≥ 0)
    (0 ≤ liquidation_reward pos P penalty_bps - gas_cost) ∧
    -- Layer 3: Funding budget-balanced
    (let f := symmetric_funding rate pos P
     f.long_payment + f.short_payment = 0) ∧
    -- Layer 4: Liquidation reward non-negative (IR for liquidators)
    (0 ≤ liquidation_reward pos P penalty_bps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact collateral_nonneg_after_bounded_move pos P P' C m maint hP hmaint hmove hC
  · exact liquidation_dominant_strategy pos P penalty_bps gas_cost hgas
  · exact funding_budget_balance rate pos P
  · exact liquidation_reward_nonneg pos P penalty_bps hP hpen

/-- Safety under clamped oracle moves (v1.1): the clamping mechanism enforces
    the bounded-move hypothesis, so all four safety layers hold unconditionally
    given the margin parameter constraint. -/
theorem unified_perp_safety_clamped
    (pos P P_raw C m maint penalty_bps gas_cost rate : ℚ)
    (hP : 0 ≤ P) (hm : 0 ≤ m)
    (hmaint : m ≤ maint)
    (hC : |pos| * P * maint / 10000 ≤ C)
    (hpen : 0 ≤ penalty_bps)
    (hgas : gas_cost ≤ liquidation_reward pos P penalty_bps) :
    -- Layer 1: Solvency after clamped oracle move
    (0 ≤ C + pos * (clamp_move P P_raw m - P)) ∧
    -- Layer 2: Liquidation profitability
    (0 ≤ liquidation_reward pos P penalty_bps - gas_cost) ∧
    -- Layer 3: Funding BB
    (let f := symmetric_funding rate pos P
     f.long_payment + f.short_payment = 0) ∧
    -- Layer 4: Liquidation IR
    (0 ≤ liquidation_reward pos P penalty_bps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact collateral_nonneg_after_clamped_move pos P P_raw C m maint hP hm hmaint hC
  · exact liquidation_dominant_strategy pos P penalty_bps gas_cost hgas
  · exact funding_budget_balance rate pos P
  · exact liquidation_reward_nonneg pos P penalty_bps hP hpen

/-! ## Non-Vacuity Witnesses -/

/-- Witness for unified safety: concrete scenario where all four layers hold.
    pos=10, P=100, P'=104 (4% move), m=500bps, maint=600bps, penalty=50bps, gas=2. -/
theorem witness_unified_perp_safety :
    let pos := (10 : ℚ); let P := 100; let P' := 104
    let C := 60   -- |10|*100*600/10000 = 60 (m=500bps, maint=600bps)
    let penalty_bps := 50; let gas_cost := 2; let rate := 10
    -- Layer 1: 60 + 10*(104-100) = 60 + 40 = 100 ≥ 0
    (0 ≤ C + pos * (P' - P)) ∧
    -- Layer 2: reward = |10|*100*50/10000 = 5, profit = 5 - 2 = 3 ≥ 0
    (0 ≤ liquidation_reward pos P penalty_bps - gas_cost) ∧
    -- Layer 3: funding BB
    (let f := symmetric_funding rate pos P
     f.long_payment + f.short_payment = 0) ∧
    -- Layer 4: reward = 5 ≥ 0
    (0 ≤ liquidation_reward pos P penalty_bps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num
  · simp [liquidation_reward]; norm_num
  · simp [symmetric_funding]
  · simp [liquidation_reward]; norm_num

/-- Witness for no-value-creation: pos=10, δP=50 → long PnL=500, short PnL=−500. -/
theorem witness_no_value_creation :
    let pos := (10 : ℚ); let δP := 50
    pos * δP + (-pos) * δP = 0 := by ring

/-- Witness for interaction budget: all components non-negative. -/
theorem witness_interaction_budget :
    let coll_a := (1000 : ℚ); let coll_b := 2000; let insurance := 500
    0 ≤ coll_a + coll_b + insurance := by
  norm_num

end PerpProtocolSafety

end Proofs
