import Proofs.ZenoPayoffPortfolioFixedPointBridge
import Mathlib

/-!
# FIRE Unified Settlement Theorem

This file packages the FIRE/ZPL fixed-point portfolio settlement theorem into a
single reusable receipt object. The receipt exposes the operational conclusions
that downstream verifier code cares about:

* both parties remain solvent after settlement; and
* the holder and writer deltas conserve exactly.

The theorem does not add new financial assumptions. It reuses the existing
ZPL compiler and fixed-point portfolio bridge, then repackages their conjunction
as a projectable settlement certificate.
-/

namespace Proofs
namespace FIREUnified

open CertifiedFinancialMathObjects
open FixedPointIntervalBridge
open FixedPointPortfolioBridge
open ZenoPayoffLanguage
open ZenoPayoffPortfolioFixedPointBridge

variable {ι Asset : Type _}

noncomputable section

theorem tick_pos {scale : ℝ} (hscale : 0 < scale) : 0 < tick scale := by
  unfold tick
  positivity

/-- A FIRE settlement receipt records deltas plus bilateral solvency and exact
zero-sum conservation. -/
structure FIREPortfolioReceipt where
  holderPosted : ℝ
  writerPosted : ℝ
  holderDelta : ℝ
  writerDelta : ℝ
  holder_solvent : 0 ≤ holderPosted + holderDelta
  writer_solvent : 0 ≤ writerPosted + writerDelta
  conservation : holderDelta + writerDelta = 0

theorem FIREPortfolioReceipt.writerDelta_eq_neg (R : FIREPortfolioReceipt) :
    R.writerDelta = -R.holderDelta := by
  linarith [R.conservation]

theorem FIREPortfolioReceipt.net_zero (R : FIREPortfolioReceipt) :
    (R.holderPosted + R.holderDelta) + (R.writerPosted + R.writerDelta) =
      R.holderPosted + R.writerPosted := by
  linarith [R.conservation]

/-- Unified FIRE portfolio settlement theorem.

If every leg in `S` compiles, the fixed-point scale is positive, and posted
collateral covers the mode-expanded certified interval, the portfolio produces a
receipt with bilateral solvency and exact conservation. -/
def fire_portfolio_settlement
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i))
    (hHolder :
      holderCollateral
        (S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale)) ≤ holderPosted)
    (hWriter :
      writerCollateral
        (S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale)) ≤ writerPosted) :
    FIREPortfolioReceipt where
  holderPosted := holderPosted
  writerPosted := writerPosted
  holderDelta := S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i)))
  writerDelta := -(S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))))
  holder_solvent :=
    (compile_sum_decodeByMode_posted_collateral_safe S hscale hcompile hHolder hWriter).1
  writer_solvent := by
    have h :=
      (compile_sum_decodeByMode_posted_collateral_safe S hscale hcompile hHolder hWriter).2
    linarith
  conservation := by
    ring

/-- Independent FIRE settlement receipts compose by adding posted collateral and
deltas. This captures zero-sum netting across independent books. -/
def FIREPortfolioReceipt.combine (R₁ R₂ : FIREPortfolioReceipt) :
    FIREPortfolioReceipt where
  holderPosted := R₁.holderPosted + R₂.holderPosted
  writerPosted := R₁.writerPosted + R₂.writerPosted
  holderDelta := R₁.holderDelta + R₂.holderDelta
  writerDelta := R₁.writerDelta + R₂.writerDelta
  holder_solvent := by
    linarith [R₁.holder_solvent, R₂.holder_solvent]
  writer_solvent := by
    linarith [R₁.writer_solvent, R₂.writer_solvent]
  conservation := by
    linarith [R₁.conservation, R₂.conservation]

theorem FIREPortfolioReceipt.combine_holderDelta (R₁ R₂ : FIREPortfolioReceipt) :
    (R₁.combine R₂).holderDelta = R₁.holderDelta + R₂.holderDelta := rfl

theorem FIREPortfolioReceipt.combine_writerDelta (R₁ R₂ : FIREPortfolioReceipt) :
    (R₁.combine R₂).writerDelta = R₁.writerDelta + R₂.writerDelta := rfl

/-- The neutral FIRE settlement receipt. It carries no posted collateral and no
delta movement, so it is solvent and conserves exactly. -/
def FIREPortfolioReceipt.zero : FIREPortfolioReceipt where
  holderPosted := 0
  writerPosted := 0
  holderDelta := 0
  writerDelta := 0
  holder_solvent := by norm_num
  writer_solvent := by norm_num
  conservation := by norm_num

def FIREPortfolioReceipt.operationalFields (R : FIREPortfolioReceipt) :
    ℝ × ℝ × ℝ × ℝ :=
  (R.holderPosted, R.writerPosted, R.holderDelta, R.writerDelta)

theorem FIREPortfolioReceipt.combine_zero_operational (R : FIREPortfolioReceipt) :
    (R.combine FIREPortfolioReceipt.zero).operationalFields = R.operationalFields := by
  simp [FIREPortfolioReceipt.combine, FIREPortfolioReceipt.zero,
    FIREPortfolioReceipt.operationalFields]

theorem FIREPortfolioReceipt.zero_combine_operational (R : FIREPortfolioReceipt) :
    (FIREPortfolioReceipt.zero.combine R).operationalFields = R.operationalFields := by
  simp [FIREPortfolioReceipt.combine, FIREPortfolioReceipt.zero,
    FIREPortfolioReceipt.operationalFields]

/-- Receipt composition is associative as an operational settlement receipt:
grouping independent books does not change posted collateral or deltas. -/
theorem FIREPortfolioReceipt.combine_assoc_operational
    (R₁ R₂ R₃ : FIREPortfolioReceipt) :
    ((R₁.combine R₂).combine R₃).operationalFields =
      (R₁.combine (R₂.combine R₃)).operationalFields := by
  simp [FIREPortfolioReceipt.combine, FIREPortfolioReceipt.operationalFields,
    add_assoc]

/-- Receipt composition is commutative as an operational settlement receipt:
swapping two independent books does not change the final combined receipt. -/
theorem FIREPortfolioReceipt.combine_comm_operational (R₁ R₂ : FIREPortfolioReceipt) :
    (R₁.combine R₂).operationalFields = (R₂.combine R₁).operationalFields := by
  simp [FIREPortfolioReceipt.combine, FIREPortfolioReceipt.operationalFields,
    add_comm]

/-- A compiled ZPL portfolio lifts to a generic certified payoff with the
mode-expanded interval. -/
theorem compiled_portfolio_to_certified_payoff
    [DecidableEq ι] (S : Finset ι)
    {a : Asset} {scale : ℝ}
    {mode : ι → RoundingMode}
    {expr : ι → Expr Asset (ValueType.amount a)}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : ∀ i, i ∈ S → compile (expr i) = some (cert i)) :
    ∃ P : CertifiedPayoff Unit,
      P.payoff () = S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))) ∧
      P.lower = S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale) ∧
      P.upper = S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale) := by
  have hbounds := compile_sum_decodeByMode_interval S hscale hcompile (mode := mode)
  exact
    ⟨
      ⟨fun _ => S.sum (fun i => decodeByMode scale (mode i) (Expr.eval (expr i))),
        S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale),
        S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale),
        fun _ => hbounds⟩,
      rfl,
      rfl,
      rfl
    ⟩

/-- Single-leg settlement is the singleton case of portfolio settlement. -/
def fire_single_leg_settlement
    [DecidableEq ι] (i : ι)
    {a : Asset} {scale holderPosted writerPosted : ℝ}
    {mode : RoundingMode}
    {expr : Expr Asset (ValueType.amount a)}
    {cert : CompiledExpr (Asset := Asset) (ValueType.amount a)}
    (hscale : 0 < scale)
    (hcompile : compile expr = some cert)
    (hHolder :
      holderCollateral (cert.lower - mode.lowerBuffer scale) ≤ holderPosted)
    (hWriter :
      writerCollateral (cert.upper + mode.upperBuffer scale) ≤ writerPosted) :
    FIREPortfolioReceipt :=
  fire_portfolio_settlement ({i} : Finset ι) hscale
    (mode := fun _ => mode)
    (expr := fun _ => expr)
    (cert := fun _ => cert)
    (hcompile := by simp [hcompile])
    (hHolder := by simpa using hHolder)
    (hWriter := by simpa using hWriter)

theorem floor_buffer_spec (scale : ℝ) :
    RoundingMode.floor.lowerBuffer scale = tick scale ∧
    RoundingMode.floor.upperBuffer scale = 0 := by
  exact ⟨rfl, rfl⟩

theorem ceil_buffer_spec (scale : ℝ) :
    RoundingMode.ceil.lowerBuffer scale = 0 ∧
    RoundingMode.ceil.upperBuffer scale = tick scale := by
  exact ⟨rfl, rfl⟩

theorem total_buffer_eq_tick (mode : RoundingMode) (scale : ℝ) :
    mode.lowerBuffer scale + mode.upperBuffer scale = tick scale := by
  cases mode <;> simp [RoundingMode.lowerBuffer, RoundingMode.upperBuffer]

theorem holderCollateral_anti {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) :
    holderCollateral L₂ ≤ holderCollateral L₁ := by
  unfold holderCollateral
  exact max_le_max le_rfl (neg_le_neg_iff.mpr h)

theorem writerCollateral_mono {U₁ U₂ : ℝ} (h : U₁ ≤ U₂) :
    writerCollateral U₁ ≤ writerCollateral U₂ := by
  unfold writerCollateral
  exact max_le_max le_rfl h

theorem holderCollateral_nonneg (L : ℝ) : 0 ≤ holderCollateral L := le_max_left _ _

theorem writerCollateral_nonneg (U : ℝ) : 0 ≤ writerCollateral U := le_max_left _ _

theorem two_party_conservation (holderDelta : ℝ) :
    holderDelta + (-holderDelta) = 0 := by
  ring

/-- The mode-expanded portfolio interval is wider than the unexpanded interval by
exactly one tick per leg. -/
theorem portfolio_interval_width_budget
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ}
    {mode : ι → RoundingMode}
    {cert : ι → CompiledExpr (Asset := Asset) (ValueType.amount a)} :
    (S.sum (fun i => (cert i).upper + (mode i).upperBuffer scale)) -
      (S.sum (fun i => (cert i).lower - (mode i).lowerBuffer scale)) =
    (S.sum (fun i => (cert i).upper - (cert i).lower)) +
      (S.card : ℝ) * tick scale := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hBuffer :
      S.sum (fun i => (mode i).lowerBuffer scale) +
        S.sum (fun i => (mode i).upperBuffer scale) =
        (S.card : ℝ) * tick scale := by
    rw [← Finset.sum_add_distrib]
    simp only [total_buffer_eq_tick]
    simp [Finset.sum_const, nsmul_eq_mul]
  linarith

end

end FIREUnified
end Proofs
