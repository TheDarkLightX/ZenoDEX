import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Proofs.PerpMechanismDesign
import Proofs.PerpEpochSafety

/-!
# Perpetual Game Theory

Game-theoretic proofs for the epoch-based perpetual protocol. Extends
`PerpEpochSafety.lean` with mechanism design properties from `PerpMechanismDesign.lean`.

## Tier 1 — Algebraic (unconditional)
- `funding_budget_balance`: long + short funding payments sum to zero
- `collateral_conservation`: zero-sum PnL preserves total collateral
- `liquidation_reward_nonneg`: reward ≥ 0 when penalty_bps ≥ 0

## Tier 2 — Arithmetic
- `liquidation_dominant_strategy`: net profit ≥ 0 when reward ≥ gas cost
- `liquidation_ic`: liquidation payoff weakly exceeds any non-positive alternative
- `no_profitable_self_liquidation`: self-liquidation is never profitable
- `liquidation_prevents_insolvency`: composition with PerpEpochSafety

## Tier 3 — Conditional
- `lp_ir_if_fees_exceed_claims`: LP participation is IR when fees ≥ claims

## Tier 4 — Formal Game Models
- `liquidationGame`: 1-player game; formal `DominantStrategy` + `NashEq` + `IndividuallyRational`
- `selfLiquidationGame`: 1-player game; holding is dominant when penalty ≥ 0
- `fundingGame`: 2-player game; `BudgetBalanced₂` at every profile
-/

namespace Proofs

namespace PerpGameTheory

open PerpMechanismDesign

/-! ## Structures -/

/-- Funding settlement: signed payments between long and short sides. -/
structure FundingSettlement where
  long_payment : ℚ
  short_payment : ℚ
  deriving Repr, DecidableEq

/-- Construct a symmetric funding settlement where short pays the negative of long. -/
def symmetric_funding (rate pos price : ℚ) : FundingSettlement where
  long_payment := pos * price * rate / 10000
  short_payment := -(pos * price * rate / 10000)

/-- Liquidation reward: penalty extracted from undercollateralized account. -/
def liquidation_reward (pos price penalty_bps : ℚ) : ℚ :=
  |pos| * price * penalty_bps / 10000

/-! ## Tier 1 — Algebraic Theorems -/

/-- Funding budget balance: in a symmetric funding mechanism, the sum of payments is zero.
    This is the perpetual analogue of the settlement algebra's conservation law. -/
theorem funding_budget_balance (rate pos price : ℚ) :
    let f := symmetric_funding rate pos price
    f.long_payment + f.short_payment = 0 := by
  simp [symmetric_funding]

/-- Collateral conservation: with zero-sum PnL, total collateral equals net deposits.
    In a two-account perp, `pnl_a + pnl_b = 0` ensures no value is created or destroyed. -/
theorem collateral_conservation
    (deposit_a deposit_b withdraw_a withdraw_b coll_a coll_b pnl_a pnl_b : ℚ)
    (hpnl_zero_sum : pnl_a + pnl_b = 0)
    (ha : coll_a = deposit_a - withdraw_a + pnl_a)
    (hb : coll_b = deposit_b - withdraw_b + pnl_b) :
    coll_a + coll_b = (deposit_a + deposit_b) - (withdraw_a + withdraw_b) := by
  linarith

/-- Liquidation reward is non-negative when price and penalty are non-negative. -/
theorem liquidation_reward_nonneg (pos price penalty_bps : ℚ)
    (hp : 0 ≤ price) (hpen : 0 ≤ penalty_bps) :
    0 ≤ liquidation_reward pos price penalty_bps := by
  unfold liquidation_reward
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (abs_nonneg pos) hp) hpen
  · norm_num

/-! ## Tier 2 — Game-Theoretic Theorems -/

/-- Liquidation net profit is non-negative when reward ≥ gas cost.
    For the formal game-theoretic dominant-strategy proof, see `liquidation_game_dominant`. -/
theorem liquidation_dominant_strategy (pos price penalty_bps gas_cost : ℚ)
    (hprof : gas_cost ≤ liquidation_reward pos price penalty_bps) :
    0 ≤ liquidation_reward pos price penalty_bps - gas_cost := by
  linarith

/-- Liquidation payoff weakly exceeds any non-positive alternative: given
    `reward ≥ gas` and `skip_payoff ≤ 0`, we have `skip_payoff ≤ reward − gas`
    (transitivity of ≤). For formal IC via mechanism design, see
    `liquidation_game_dominant` composed with `ic_from_dominant`. -/
theorem liquidation_ic (pos price penalty_bps gas_cost skip_payoff : ℚ)
    (hprof : gas_cost ≤ liquidation_reward pos price penalty_bps)
    (hskip : skip_payoff ≤ 0) :
    skip_payoff ≤ liquidation_reward pos price penalty_bps - gas_cost := by
  linarith

/-- Self-liquidation is never profitable: a trader who triggers their own liquidation
    loses the penalty amount. When `penalty_bps > 0` and position is open,
    the penalty is strictly positive, making self-liquidation strictly worse
    than normal position closure. -/
theorem no_profitable_self_liquidation
    (pos price penalty_bps collateral : ℚ)
    (hp : 0 < price) (hpen : 0 < penalty_bps) (hpos : pos ≠ 0) :
    collateral - liquidation_reward pos price penalty_bps < collateral := by
  have habs : 0 < |pos| := abs_pos.mpr hpos
  have hrew : 0 < liquidation_reward pos price penalty_bps := by
    unfold liquidation_reward
    apply div_pos
    · exact mul_pos (mul_pos habs hp) hpen
    · norm_num
  linarith

/-- Liquidation prevents insolvency: if the liquidation mechanism maintains the invariant
    that collateral ≥ maintenance requirement (enforced by the liquidation trigger), and
    maintenance margin ≥ oracle move bound, then the system stays solvent after any
    bounded oracle move. Composition with `PerpEpochSafety.collateral_nonneg_after_bounded_move`. -/
theorem liquidation_prevents_insolvency
    (pos P P' C m maint : ℚ)
    (hP : 0 ≤ P)
    (hmaint_ge_m : m ≤ maint)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hliq_invariant : |pos| * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (P' - P) :=
  PerpEpochSafety.collateral_nonneg_after_bounded_move
    pos P P' C m maint hP hmaint_ge_m hmove hliq_invariant

/-! ## Tier 3 — Conditional Theorems -/

/-- LP participation is individually rational when cumulative fees exceed claims paid.
    The LP's ending balance exceeds their initial deposit by `fees - claims ≥ 0`. -/
theorem lp_ir_if_fees_exceed_claims
    (initial_deposit fees_earned claims_paid : ℚ)
    (hfees : claims_paid ≤ fees_earned) :
    initial_deposit ≤ initial_deposit + (fees_earned - claims_paid) := by
  linarith

/-! ## Non-Vacuity Witnesses -/

/-- Witness for funding budget balance with concrete values.
    rate=50bps, pos=100, price=2000 → long_payment = 1000, short_payment = -1000. -/
theorem witness_funding_budget_balance :
    let f := symmetric_funding 50 100 2000
    f.long_payment + f.short_payment = 0 ∧
    f.long_payment = 1000 := by
  constructor
  · simp [symmetric_funding]
  · simp [symmetric_funding]; norm_num

/-- Witness for liquidation reward: pos=10, price=100, penalty=50bps → reward=5. -/
theorem witness_liquidation_reward :
    liquidation_reward 10 100 50 = 5 ∧
    0 ≤ liquidation_reward 10 100 50 := by
  constructor
  · simp [liquidation_reward]; norm_num
  · exact liquidation_reward_nonneg 10 100 50 (by norm_num) (by norm_num)

/-- Witness for collateral conservation with concrete two-account scenario. -/
theorem witness_collateral_conservation :
    let dep_a := (1000 : ℚ); let dep_b := 2000
    let wd_a := (100 : ℚ); let wd_b := 200
    let pnl_a := (50 : ℚ); let pnl_b := -50
    let coll_a := dep_a - wd_a + pnl_a  -- 950
    let coll_b := dep_b - wd_b + pnl_b  -- 1750
    pnl_a + pnl_b = 0 ∧
    coll_a + coll_b = (dep_a + dep_b) - (wd_a + wd_b) := by
  constructor <;> norm_num

/-- Witness for no profitable self-liquidation. -/
theorem witness_no_self_liquidation :
    let reward := liquidation_reward 10 100 50
    (1000 : ℚ) - reward < 1000 := by
  simp [liquidation_reward]

/-- Witness for liquidation prevents insolvency: concrete values satisfying
    all hypotheses of the epoch safety theorem. -/
theorem witness_liquidation_prevents_insolvency :
    let pos := (10 : ℚ); let P := 100; let P' := 104
    let C := |pos| * P * 600 / 10000  -- exactly at maintenance (600bps)
    0 ≤ C + pos * (P' - P) := by
  norm_num

/-! ## Tier 4 — Formal Game Models

Concrete `Game` instantiations from `PerpMechanismDesign` that model the
liquidator's decision, the self-liquidation choice, and the funding mechanism.
These connect the ℚ-arithmetic theorems above to the formal game-theory
definitions, establishing `DominantStrategy`, `NashEq`, `IndividuallyRational`,
and `BudgetBalanced₂` in the precise sense of mechanism design. -/

/-- Liquidation game: 1-player, 2-strategy. The liquidator chooses skip (0, payoff 0)
    or liquidate (1, payoff `net_profit`). Models the liquidator's decision problem
    as a formal normal-form game over ℤ. -/
def liquidationGame (net_profit : ℤ) : Game 1 2 where
  payoff σ _i := if σ 0 = 1 then net_profit else 0

/-- When net profit ≥ 0, liquidate (strategy 1) is a formally dominant strategy:
    it weakly dominates skip (strategy 0) in the `Game 1 2` framework. -/
theorem liquidation_game_dominant (p : ℤ) (hp : 0 ≤ p) :
    DominantStrategy (liquidationGame p) 0 1 := by
  intro σ s'
  simp only [liquidationGame, deviate, Function.update_self]
  fin_cases s' <;> simp
  omega

/-- Liquidating forms a Nash equilibrium when profitable.
    Derived from `dominant_implies_nash` applied to `liquidation_game_dominant`. -/
theorem liquidation_game_nash (p : ℤ) (hp : 0 ≤ p) :
    NashEq (liquidationGame p) (fun _ => 1) :=
  dominant_implies_nash _ _ (fun i => by fin_cases i; exact liquidation_game_dominant p hp)

/-- Liquidation is individually rational in the formal sense:
    payoff ≥ reservation value 0 when net profit ≥ 0. -/
theorem liquidation_game_ir (p : ℤ) (hp : 0 ≤ p) :
    IndividuallyRational (liquidationGame p) (fun _ => 1) 0 0 := by
  simp only [IndividuallyRational, liquidationGame]
  exact hp

/-- Liquidation is incentive-compatible in the formal sense: liquidate is a
    dominant strategy, and `IncentiveCompatible ≡ DominantStrategy` by definition.
    Composed from `liquidation_game_dominant` and `ic_from_dominant`. -/
theorem liquidation_game_ic (p : ℤ) (hp : 0 ≤ p) :
    IncentiveCompatible (liquidationGame p) 0 1 :=
  ic_from_dominant _ _ _ (liquidation_game_dominant p hp)

/-- Non-vacuity witness for the liquidation game with net_profit = 3:
    dominant strategy, Nash equilibrium, individually rational, incentive-compatible. -/
theorem witness_liquidation_game :
    DominantStrategy (liquidationGame 3) 0 1 ∧
    NashEq (liquidationGame 3) (fun _ => 1) ∧
    IndividuallyRational (liquidationGame 3) (fun _ => 1) 0 0 ∧
    IncentiveCompatible (liquidationGame 3) 0 1 := by
  native_decide

/-- Self-liquidation game: 1-player, 2-strategy. The trader chooses hold (0, payoff
    `collateral`) or self-liquidate (1, payoff `collateral − penalty`). -/
def selfLiquidationGame (collateral penalty : ℤ) : Game 1 2 where
  payoff σ _i := if σ 0 = 0 then collateral else collateral - penalty

/-- When penalty ≥ 0, holding (strategy 0) is dominant in the self-liquidation game:
    self-liquidation is never a best response. -/
theorem self_liquidation_hold_dominant (c p : ℤ) (hp : 0 ≤ p) :
    DominantStrategy (selfLiquidationGame c p) 0 0 := by
  intro σ s'
  simp only [selfLiquidationGame, deviate, Function.update_self]
  fin_cases s' <;> simp
  omega

/-- Non-vacuity: self-liquidation game with collateral = 10, penalty = 5.
    Holding is dominant, Nash, and individually rational. -/
theorem witness_self_liquidation_game :
    DominantStrategy (selfLiquidationGame 10 5) 0 0 ∧
    NashEq (selfLiquidationGame 10 5) (fun _ => 0) ∧
    IndividuallyRational (selfLiquidationGame 10 5) (fun _ => 0) 0 0 := by
  native_decide

/-- Funding game: 2-player, 2-strategy. Both choose participate (0) or exit (1).
    When both participate, long pays `payment` and short receives it (zero-sum).
    If either exits, both get 0. Models symmetric funding as a zero-sum mechanism. -/
def fundingGame (payment : ℤ) : Game 2 2 where
  payoff σ i :=
    if σ 0 = 0 ∧ σ 1 = 0 then
      if i = 0 then -payment else payment
    else 0

/-- The funding game is budget-balanced at every profile:
    total payoffs are non-negative (in fact exactly 0). -/
theorem funding_game_bb (payment : ℤ) (σ : Fin 2 → Fin 2) :
    BudgetBalanced₂ (fundingGame payment) σ := by
  simp only [BudgetBalanced₂, fundingGame]
  split_ifs <;> omega

/-- Non-vacuity: funding game with payment = 100.
    Budget-balanced and exactly zero-sum at the participate-participate profile. -/
theorem witness_funding_game :
    BudgetBalanced₂ (fundingGame 100) (fun (_ : Fin 2) => (0 : Fin 2)) ∧
    (fundingGame 100).payoff (fun _ => 0) 0 + (fundingGame 100).payoff (fun _ => 0) 1 = 0 := by
  native_decide

end PerpGameTheory

end Proofs
