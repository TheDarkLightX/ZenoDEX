import Mathlib

/-!
# FIRE Budget Safety

This packet isolates the fail-closed budget rule shared by proof-mining rewards,
rebates, buybacks, bounty auctions, and future FIRE incentive controllers.

The controller may be creative, but a certificate can only authorize spend when:

`spend ≤ verifiedValue + explicitBudget`.

Finite aggregation preserves that rule, so splitting a campaign into batches
cannot create extra spend authority.
-/

namespace Proofs
namespace FIREBudgetSafety

variable {ι κ : Type _}

/-- A minimal reward/buyback/bounty budget certificate.

`verifiedValue` is the value admitted by proofs or audited receipts;
`explicitBudget` is governance or treasury budget; `spend` is what the
controller actually pays out or burns. -/
structure FIREBudgetCertificate where
  verifiedValue : ℝ
  explicitBudget : ℝ
  spend : ℝ
  spend_nonneg : 0 ≤ spend
  explicitBudget_nonneg : 0 ≤ explicitBudget
  spend_le_value_plus_budget : spend ≤ verifiedValue + explicitBudget

namespace FIREBudgetCertificate

/-- Aggregate a finite family of budget certificates componentwise. -/
def aggregate [DecidableEq ι] (S : Finset ι) (B : ι → FIREBudgetCertificate) :
    FIREBudgetCertificate where
  verifiedValue := S.sum fun i => (B i).verifiedValue
  explicitBudget := S.sum fun i => (B i).explicitBudget
  spend := S.sum fun i => (B i).spend
  spend_nonneg := by
    exact Finset.sum_nonneg fun i _hi => (B i).spend_nonneg
  explicitBudget_nonneg := by
    exact Finset.sum_nonneg fun i _hi => (B i).explicitBudget_nonneg
  spend_le_value_plus_budget := by
    calc
      S.sum (fun i => (B i).spend)
          ≤ S.sum (fun i => (B i).verifiedValue + (B i).explicitBudget) :=
            Finset.sum_le_sum fun i _hi => (B i).spend_le_value_plus_budget
      _ = S.sum (fun i => (B i).verifiedValue) +
          S.sum (fun i => (B i).explicitBudget) := by
            rw [Finset.sum_add_distrib]

theorem aggregate_spend_le_value_plus_budget
    [DecidableEq ι] (S : Finset ι) (B : ι → FIREBudgetCertificate) :
    (aggregate S B).spend ≤
      (aggregate S B).verifiedValue + (aggregate S B).explicitBudget :=
  (aggregate S B).spend_le_value_plus_budget

/-- Disjoint budget batches compose additively. Splitting a reward campaign into
batches cannot create extra spend capacity. -/
theorem aggregate_union_disjoint_spend_le
    [DecidableEq ι] {S T : Finset ι}
    (hdisjoint : Disjoint S T) (B : ι → FIREBudgetCertificate) :
    (aggregate (S ∪ T) B).spend ≤
      (aggregate S B).verifiedValue + (aggregate T B).verifiedValue +
      ((aggregate S B).explicitBudget + (aggregate T B).explicitBudget) := by
  have h := aggregate_spend_le_value_plus_budget (S ∪ T) B
  simpa [aggregate, Finset.sum_union hdisjoint, add_assoc, add_left_comm, add_comm] using h

/-- Relabeling budget certificates preserves the operational budget triple. -/
theorem aggregate_equiv_fields
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (S : Finset ι) (B : κ → FIREBudgetCertificate) :
    ((aggregate (S.map e.toEmbedding) B).verifiedValue,
      (aggregate (S.map e.toEmbedding) B).explicitBudget,
      (aggregate (S.map e.toEmbedding) B).spend) =
    ((aggregate S (fun i => B (e i))).verifiedValue,
      (aggregate S (fun i => B (e i))).explicitBudget,
      (aggregate S (fun i => B (e i))).spend) := by
  simp [aggregate]

/-- Binary budget composition. -/
def combine (B₁ B₂ : FIREBudgetCertificate) : FIREBudgetCertificate where
  verifiedValue := B₁.verifiedValue + B₂.verifiedValue
  explicitBudget := B₁.explicitBudget + B₂.explicitBudget
  spend := B₁.spend + B₂.spend
  spend_nonneg := by
    linarith [B₁.spend_nonneg, B₂.spend_nonneg]
  explicitBudget_nonneg := by
    linarith [B₁.explicitBudget_nonneg, B₂.explicitBudget_nonneg]
  spend_le_value_plus_budget := by
    linarith [B₁.spend_le_value_plus_budget, B₂.spend_le_value_plus_budget]

/-- The neutral budget certificate. -/
def zero : FIREBudgetCertificate where
  verifiedValue := 0
  explicitBudget := 0
  spend := 0
  spend_nonneg := by norm_num
  explicitBudget_nonneg := by norm_num
  spend_le_value_plus_budget := by norm_num

/-- Empty aggregation produces the zero budget operationally. -/
theorem aggregate_empty [DecidableEq ι] (B : ι → FIREBudgetCertificate) :
    ((aggregate (∅ : Finset ι) B).verifiedValue,
     (aggregate (∅ : Finset ι) B).explicitBudget,
     (aggregate (∅ : Finset ι) B).spend) =
    (zero.verifiedValue, zero.explicitBudget, zero.spend) := by
  simp [aggregate, zero]

/-- Inserting one budget certificate is operationally binary composition with
the aggregate of the remaining certificates. -/
theorem aggregate_insert [DecidableEq ι] {S : Finset ι} {i : ι}
    (hi : i ∉ S) (B : ι → FIREBudgetCertificate) :
    ((aggregate (insert i S) B).verifiedValue,
     (aggregate (insert i S) B).explicitBudget,
     (aggregate (insert i S) B).spend) =
    ((combine (B i) (aggregate S B)).verifiedValue,
     (combine (B i) (aggregate S B)).explicitBudget,
     (combine (B i) (aggregate S B)).spend) := by
  simp [aggregate, combine, Finset.sum_insert hi]

/-- Combining budgets is associative on the operational triple. -/
theorem combine_assoc (B₁ B₂ B₃ : FIREBudgetCertificate) :
    ((combine (combine B₁ B₂) B₃).verifiedValue,
     (combine (combine B₁ B₂) B₃).explicitBudget,
     (combine (combine B₁ B₂) B₃).spend) =
    ((combine B₁ (combine B₂ B₃)).verifiedValue,
     (combine B₁ (combine B₂ B₃)).explicitBudget,
     (combine B₁ (combine B₂ B₃)).spend) := by
  simp [combine, add_assoc]

/-- Combining with zero is a right identity. -/
theorem combine_zero (B : FIREBudgetCertificate) :
    ((combine B zero).verifiedValue,
     (combine B zero).explicitBudget,
     (combine B zero).spend) =
    (B.verifiedValue, B.explicitBudget, B.spend) := by
  simp [combine, zero]

/-- Combining with zero is a left identity. -/
theorem zero_combine (B : FIREBudgetCertificate) :
    ((combine zero B).verifiedValue,
     (combine zero B).explicitBudget,
     (combine zero B).spend) =
    (B.verifiedValue, B.explicitBudget, B.spend) := by
  simp [combine, zero]

/-- Combining budgets is commutative on the operational triple. -/
theorem combine_comm (B₁ B₂ : FIREBudgetCertificate) :
    ((combine B₁ B₂).verifiedValue,
     (combine B₁ B₂).explicitBudget,
     (combine B₁ B₂).spend) =
    ((combine B₂ B₁).verifiedValue,
     (combine B₂ B₁).explicitBudget,
     (combine B₂ B₁).spend) := by
  simp [combine, add_comm]

/-- The fail-closed law survives binary composition. -/
theorem combine_spend_le (B₁ B₂ : FIREBudgetCertificate) :
    (combine B₁ B₂).spend ≤
      (combine B₁ B₂).verifiedValue + (combine B₁ B₂).explicitBudget :=
  (combine B₁ B₂).spend_le_value_plus_budget

/-- Proportional fail-closed law: if each spend is at most `α` times its
capacity, the aggregate obeys the same proportional cap. -/
theorem aggregate_proportional_bound
    [DecidableEq ι] (S : Finset ι) (B : ι → FIREBudgetCertificate) (α : ℝ)
    (_hα : 0 ≤ α)
    (hprop : ∀ i ∈ S, (B i).spend ≤ α * ((B i).verifiedValue + (B i).explicitBudget)) :
    (aggregate S B).spend ≤
      α * ((aggregate S B).verifiedValue + (aggregate S B).explicitBudget) := by
  convert Finset.sum_le_sum hprop using 1
  simp [aggregate, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Budget aggregation is monotone under pointwise spend refinement. -/
theorem aggregate_spend_mono
    [DecidableEq ι] (S : Finset ι) (B₁ B₂ : ι → FIREBudgetCertificate)
    (hspend : ∀ i ∈ S, (B₂ i).spend ≤ (B₁ i).spend) :
    (aggregate S B₂).spend ≤ (aggregate S B₁).spend := by
  exact Finset.sum_le_sum hspend

end FIREBudgetCertificate

end FIREBudgetSafety
end Proofs
