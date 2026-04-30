import Proofs.ZenoPayoffLanguage
import Proofs.FixedPointIntervalBridge
import Mathlib.Tactic

/-!
# ZPL Fixed-Point Runtime Bridge

This packet connects the real-valued Zeno Payoff Language certificate to
fixed-point runtime settlement values.

The compiler proves a real payoff lies in `[lower, upper]`.  The fixed-point
bridge proves floor/ceil encoding and decoding can move that value by less than
one tick.  This file composes those facts into small verifier rules:

* floor-decoded runtime payoffs are safe under `[lower - tick, upper]`;
* ceil-decoded runtime payoffs are safe under `[lower, upper + tick]`;
* posted collateral against those expanded intervals prevents two-party default.
-/

namespace Proofs
namespace ZenoPayoffFixedPointBridge

open CertifiedFinancialMathObjects
open FixedPointIntervalBridge
open ZenoPayoffLanguage

variable {Asset : Type _}

noncomputable section

/-- A compiled ZPL payoff rounded down to fixed point remains inside the
one-tick-expanded lower interval. -/
theorem compiled_floorDecode_interval
    {τ : ValueType Asset} {scale : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale) :
    c.lower - tick scale ≤ floorDecode scale c.value ∧
      floorDecode scale c.value ≤ c.upper := by
  have h := floorDecode_mem_expanded_interval
    (scale := scale) (x := c.value) (L := c.lower) (U := c.upper)
    hscale c.sound
  exact ⟨le_of_lt h.1, h.2⟩

/-- A compiled ZPL payoff rounded up to fixed point remains inside the
one-tick-expanded upper interval. -/
theorem compiled_ceilDecode_interval
    {τ : ValueType Asset} {scale : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale) :
    c.lower ≤ ceilDecode scale c.value ∧
      ceilDecode scale c.value ≤ c.upper + tick scale := by
  have h := ceilDecode_mem_expanded_interval
    (scale := scale) (x := c.value) (L := c.lower) (U := c.upper)
    hscale c.sound
  exact ⟨h.1, le_of_lt h.2⟩

/-- Compiler success plus floor fixed-point decoding yields a runtime interval
certificate for the expression denotation. -/
theorem compile_floorDecode_interval
    {τ : ValueType Asset} {scale : ℝ}
    {e : Expr Asset τ} {c : CompiledExpr (Asset := Asset) τ}
    (hcompile : compile e = some c)
    (hscale : 0 < scale) :
    c.lower - tick scale ≤ floorDecode scale (Expr.eval e) ∧
      floorDecode scale (Expr.eval e) ≤ c.upper := by
  rcases compile_correct e c hcompile with ⟨hv, _hl, _hu⟩
  rw [← hv]
  exact compiled_floorDecode_interval c hscale

/-- Compiler success plus ceil fixed-point decoding yields a runtime interval
certificate for the expression denotation. -/
theorem compile_ceilDecode_interval
    {τ : ValueType Asset} {scale : ℝ}
    {e : Expr Asset τ} {c : CompiledExpr (Asset := Asset) τ}
    (hcompile : compile e = some c)
    (hscale : 0 < scale) :
    c.lower ≤ ceilDecode scale (Expr.eval e) ∧
      ceilDecode scale (Expr.eval e) ≤ c.upper + tick scale := by
  rcases compile_correct e c hcompile with ⟨hv, _hl, _hu⟩
  rw [← hv]
  exact compiled_ceilDecode_interval c hscale

/-- If runtime settles the compiled payoff using floor fixed-point decoding,
collateral posted against `[lower - tick, upper]` prevents bilateral default. -/
theorem compiled_floorDecode_no_default
    {τ : ValueType Asset} {scale : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale) :
    0 ≤ holderCollateral (c.lower - tick scale) + floorDecode scale c.value ∧
      0 ≤ writerCollateral c.upper - floorDecode scale c.value := by
  exact bilateral_no_default_of_bounds (compiled_floorDecode_interval c hscale)

/-- If runtime settles the compiled payoff using ceil fixed-point decoding,
collateral posted against `[lower, upper + tick]` prevents bilateral default. -/
theorem compiled_ceilDecode_no_default
    {τ : ValueType Asset} {scale : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale) :
    0 ≤ holderCollateral c.lower + ceilDecode scale c.value ∧
      0 ≤ writerCollateral (c.upper + tick scale) - ceilDecode scale c.value := by
  exact bilateral_no_default_of_bounds (compiled_ceilDecode_interval c hscale)

/-- Posted collateral version of `compiled_floorDecode_no_default`. -/
theorem compiled_floorDecode_posted_collateral_safe
    {τ : ValueType Asset} {scale holderPosted writerPosted : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale)
    (hHolder : holderCollateral (c.lower - tick scale) ≤ holderPosted)
    (hWriter : writerCollateral c.upper ≤ writerPosted) :
    0 ≤ holderPosted + floorDecode scale c.value ∧
      0 ≤ writerPosted - floorDecode scale c.value := by
  rcases compiled_floorDecode_no_default c hscale with ⟨hh, hw⟩
  constructor <;> linarith

/-- Posted collateral version of `compiled_ceilDecode_no_default`. -/
theorem compiled_ceilDecode_posted_collateral_safe
    {τ : ValueType Asset} {scale holderPosted writerPosted : ℝ}
    (c : CompiledExpr (Asset := Asset) τ)
    (hscale : 0 < scale)
    (hHolder : holderCollateral c.lower ≤ holderPosted)
    (hWriter : writerCollateral (c.upper + tick scale) ≤ writerPosted) :
    0 ≤ holderPosted + ceilDecode scale c.value ∧
      0 ≤ writerPosted - ceilDecode scale c.value := by
  rcases compiled_ceilDecode_no_default c hscale with ⟨hh, hw⟩
  constructor <;> linarith

/-- Full compiler-to-runtime floor rule for a FIRE/ZPL certificate. -/
theorem compile_floorDecode_posted_collateral_safe
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {e : Expr Asset (ValueType.amount a)}
    {c : CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hcompile : compile e = some c)
    (hscale : 0 < scale)
    (hHolder : holderCollateral (c.lower - tick scale) ≤ holderPosted)
    (hWriter : writerCollateral c.upper ≤ writerPosted) :
    0 ≤ holderPosted + floorDecode scale (Expr.eval e) ∧
      0 ≤ writerPosted - floorDecode scale (Expr.eval e) := by
  rcases compile_correct e c hcompile with ⟨hv, _hl, _hu⟩
  rw [← hv]
  exact compiled_floorDecode_posted_collateral_safe c hscale hHolder hWriter

/-- Full compiler-to-runtime ceil rule for a FIRE/ZPL certificate. -/
theorem compile_ceilDecode_posted_collateral_safe
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {e : Expr Asset (ValueType.amount a)}
    {c : CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hcompile : compile e = some c)
    (hscale : 0 < scale)
    (hHolder : holderCollateral c.lower ≤ holderPosted)
    (hWriter : writerCollateral (c.upper + tick scale) ≤ writerPosted) :
    0 ≤ holderPosted + ceilDecode scale (Expr.eval e) ∧
      0 ≤ writerPosted - ceilDecode scale (Expr.eval e) := by
  rcases compile_correct e c hcompile with ⟨hv, _hl, _hu⟩
  rw [← hv]
  exact compiled_ceilDecode_posted_collateral_safe c hscale hHolder hWriter

end

end ZenoPayoffFixedPointBridge
end Proofs
