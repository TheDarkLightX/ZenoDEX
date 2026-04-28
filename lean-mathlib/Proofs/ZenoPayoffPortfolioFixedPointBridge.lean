import Proofs.ZenoPayoffLanguage
import Proofs.FixedPointPortfolioBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# ZPL Portfolio Fixed-Point Bridge

This packet composes three proof layers:

1. ZPL compiler correctness gives each compiled payoff leg a real interval.
2. The fixed-point portfolio bridge lifts one-tick rounding bounds over finite
   bundles.
3. The certified financial object collateral lemma turns the resulting aggregate
   interval into bilateral no-default safety.

The result is a direct theorem for multi-leg FIRE/ZPL delta tables: if every leg
compiles, then a floor- or ceil-rounded runtime portfolio is safe when collateral
is posted against the corresponding aggregate tick-expanded interval.
-/

namespace Proofs
namespace ZenoPayoffPortfolioFixedPointBridge

open CertifiedFinancialMathObjects
open FixedPointIntervalBridge
open FixedPointPortfolioBridge
open ZenoPayoffLanguage

variable {ι Asset : Type _}

noncomputable section

/-- A finite bundle of successfully compiled ZPL legs, rounded down at runtime,
stays inside the aggregate one-tick-per-leg lower expansion. -/
theorem compile_sum_floorDecode_interval
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    S.sum (fun i => (cert i).lower) - (S.card : ℝ) * tick scale ≤
        S.sum (fun i => floorDecode scale (Expr.eval (expr i))) ∧
      S.sum (fun i => floorDecode scale (Expr.eval (expr i))) ≤
        S.sum (fun i => (cert i).upper) := by
  apply sum_floorDecode_mem_card_expanded_interval
  · exact hscale
  · intro i hi
    rcases compile_correct (expr i) (cert i) (hcompile i hi) with ⟨_hv, hl, hu⟩
    exact ⟨hl, hu⟩

/-- A finite bundle of successfully compiled ZPL legs, rounded up at runtime,
stays inside the aggregate one-tick-per-leg upper expansion. -/
theorem compile_sum_ceilDecode_interval
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    S.sum (fun i => (cert i).lower) ≤
        S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) ∧
      S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) ≤
        S.sum (fun i => (cert i).upper) + (S.card : ℝ) * tick scale := by
  apply sum_ceilDecode_mem_card_expanded_interval
  · exact hscale
  · intro i hi
    rcases compile_correct (expr i) (cert i) (hcompile i hi) with ⟨_hv, hl, hu⟩
    exact ⟨hl, hu⟩

/-- Aggregate floor-rounded runtime settlement cannot default if collateral is
posted against the aggregate floor-expanded interval. -/
theorem compile_sum_floorDecode_no_default
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    0 ≤ holderCollateral
          (S.sum (fun i => (cert i).lower) - (S.card : ℝ) * tick scale) +
        S.sum (fun i => floorDecode scale (Expr.eval (expr i))) ∧
      0 ≤ writerCollateral (S.sum fun i => (cert i).upper) -
        S.sum (fun i => floorDecode scale (Expr.eval (expr i))) := by
  exact bilateral_no_default_of_bounds
    (compile_sum_floorDecode_interval S hscale hcompile)

/-- Aggregate ceil-rounded runtime settlement cannot default if collateral is
posted against the aggregate ceil-expanded interval. -/
theorem compile_sum_ceilDecode_no_default
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    0 ≤ holderCollateral (S.sum fun i => (cert i).lower) +
        S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) ∧
      0 ≤ writerCollateral
          (S.sum (fun i => (cert i).upper) + (S.card : ℝ) * tick scale) -
        S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) := by
  exact bilateral_no_default_of_bounds
    (compile_sum_ceilDecode_interval S hscale hcompile)

/-- Posted-collateral version of the aggregate floor-rounded settlement rule. -/
theorem compile_sum_floorDecode_posted_collateral_safe
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i))
    (hHolder :
      holderCollateral
          (S.sum (fun i => (cert i).lower) - (S.card : ℝ) * tick scale) ≤
        holderPosted)
    (hWriter : writerCollateral (S.sum fun i => (cert i).upper) ≤ writerPosted) :
    0 ≤ holderPosted +
        S.sum (fun i => floorDecode scale (Expr.eval (expr i))) ∧
      0 ≤ writerPosted -
        S.sum (fun i => floorDecode scale (Expr.eval (expr i))) := by
  rcases compile_sum_floorDecode_no_default S hscale hcompile with ⟨hh, hw⟩
  constructor <;> linarith

/-- Posted-collateral version of the aggregate ceil-rounded settlement rule. -/
theorem compile_sum_ceilDecode_posted_collateral_safe
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i))
    (hHolder : holderCollateral (S.sum fun i => (cert i).lower) ≤ holderPosted)
    (hWriter :
      writerCollateral
          (S.sum (fun i => (cert i).upper) + (S.card : ℝ) * tick scale) ≤
        writerPosted) :
    0 ≤ holderPosted +
        S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) ∧
      0 ≤ writerPosted -
        S.sum (fun i => ceilDecode scale (Expr.eval (expr i))) := by
  rcases compile_sum_ceilDecode_no_default S hscale hcompile with ⟨hh, hw⟩
  constructor <;> linarith

end

end ZenoPayoffPortfolioFixedPointBridge
end Proofs
