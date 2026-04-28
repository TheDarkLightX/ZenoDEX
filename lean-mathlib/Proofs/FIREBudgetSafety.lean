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

end FIREBudgetCertificate

end FIREBudgetSafety
end Proofs
