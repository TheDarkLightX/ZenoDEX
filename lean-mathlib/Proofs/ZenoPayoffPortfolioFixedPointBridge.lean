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

/-- A finite bundle of successfully compiled ZPL legs, decoded with per-leg
rounding modes, stays inside the aggregate mode-expanded interval. -/
theorem compile_sum_decodeByMode_interval
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale) ≤
        S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) ∧
      S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) ≤
        S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale) := by
  apply sum_decodeByMode_mem_expanded_interval
  · exact hscale
  · intro i hi
    rcases compile_correct (expr i) (cert i) (hcompile i hi) with ⟨_hv, hl, hu⟩
    exact ⟨hl, hu⟩

/-- Aggregate mixed-rounded runtime settlement cannot default if collateral is
posted against the aggregate mode-expanded interval. -/
theorem compile_sum_decodeByMode_no_default
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    0 ≤ holderCollateral
          (S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale)) +
        S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) ∧
      0 ≤ writerCollateral
          (S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale)) -
        S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) := by
  exact bilateral_no_default_of_bounds
    (compile_sum_decodeByMode_interval S hscale hcompile)

/-- Posted-collateral version of the mixed-rounding settlement rule. -/
theorem compile_sum_decodeByMode_posted_collateral_safe
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i))
    (hHolder :
      holderCollateral
          (S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale)) ≤
        holderPosted)
    (hWriter :
      writerCollateral
          (S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale)) ≤
        writerPosted) :
    0 ≤ holderPosted +
        S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) ∧
      0 ≤ writerPosted -
        S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) := by
  rcases compile_sum_decodeByMode_no_default S hscale hcompile with ⟨hh, hw⟩
  constructor <;> linarith

/-- Integer FIRE settlement deltas conserve exactly when the writer leg is the
runtime negation of the already-rounded holder leg. -/
theorem int_two_party_delta_conserves (holderDelta : Int) :
    holderDelta + (-holderDelta) = 0 := by
  omega

/-- A single compiled ZPL leg decoded with a selected fixed-point rounding mode
conserves exactly when the counterparty leg is the negation of that rounded
runtime value. This captures the implementation rule "round once, then mirror";
it deliberately avoids independently rounding opposite legs. -/
theorem compile_decodeByMode_two_party_delta_conserves
    {a : Asset} {scale : ℝ}
    {mode : RoundingMode}
    {expr : Expr Asset (ValueType.amount a)}
    {cert : CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (_hcompile : compile expr = some cert) :
    let holderDelta := decodeByMode scale mode (Expr.eval expr)
    holderDelta + (-holderDelta) = 0 := by
  simp

/-- A compiled ZPL portfolio decoded with per-leg fixed-point rounding modes
conserves exactly when the writer delta is the negation of the aggregate rounded
holder delta. -/
theorem compile_sum_decodeByMode_two_party_delta_conserves
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (_hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    let holderDelta :=
      S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i)))
    holderDelta + (-holderDelta) = 0 := by
  simp

end

end ZenoPayoffPortfolioFixedPointBridge
end Proofs
