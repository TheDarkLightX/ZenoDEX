import Mathlib

/-!
# ZenoHypergraph Padding And Permutation Invariants

This file formalizes the first proof obligations from the ZenoHypergraph UPBA
design. The model is deliberately small:

* an order-price hyperedge contributes bounded integer score components;
* inactive padded slots contribute zero;
* row scores are computed by commutative summation over hyperedges.

The result supports fixed-shape ZK/FHE/Tau-Table encodings: a batch can be padded
to a maximum size without changing the UPBA row score.
-/

namespace ZenoHypergraph

/-- A local contribution of one order-price hyperedge to one price row. -/
structure EdgeContribution where
  active : Bool
  buyBaseDemand : Nat
  sellBaseSupply : Nat
  surplus : Nat
deriving Repr, DecidableEq

/-- The score carried by one price row after aggregating all incident order edges. -/
structure RowScore where
  buyBaseDemand : Nat
  sellBaseSupply : Nat
  surplus : Nat
deriving Repr, DecidableEq

/-- Canonical inactive padding slot for fixed-shape circuits. -/
def padContribution : EdgeContribution :=
  { active := false, buyBaseDemand := 0, sellBaseSupply := 0, surplus := 0 }

def demandComponent (e : EdgeContribution) : Nat :=
  if e.active then e.buyBaseDemand else 0

def supplyComponent (e : EdgeContribution) : Nat :=
  if e.active then e.sellBaseSupply else 0

def surplusComponent (e : EdgeContribution) : Nat :=
  if e.active then e.surplus else 0

/-- Public row-score evaluator for a finite order-price incidence fiber. -/
def rowScore (edges : List EdgeContribution) : RowScore :=
  {
    buyBaseDemand := (edges.map demandComponent).sum
    sellBaseSupply := (edges.map supplyComponent).sum
    surplus := (edges.map surplusComponent).sum
  }

/-- Fixed-shape padding appends inactive slots to the right. -/
def padRight (edges : List EdgeContribution) (n : Nat) : List EdgeContribution :=
  edges ++ List.replicate n padContribution

@[simp] theorem pad_demand_zero : demandComponent padContribution = 0 := by
  rfl

@[simp] theorem pad_supply_zero : supplyComponent padContribution = 0 := by
  rfl

@[simp] theorem pad_surplus_zero : surplusComponent padContribution = 0 := by
  rfl

/-- Any number of inactive slots has zero aggregate demand. -/
theorem replicate_pad_demand_sum_zero (n : Nat) :
    ((List.replicate n padContribution).map demandComponent).sum = 0 := by
  simp [padContribution, demandComponent]

/-- Any number of inactive slots has zero aggregate supply. -/
theorem replicate_pad_supply_sum_zero (n : Nat) :
    ((List.replicate n padContribution).map supplyComponent).sum = 0 := by
  simp [padContribution, supplyComponent]

/-- Any number of inactive slots has zero aggregate surplus. -/
theorem replicate_pad_surplus_sum_zero (n : Nat) :
    ((List.replicate n padContribution).map surplusComponent).sum = 0 := by
  simp [padContribution, surplusComponent]

/--
Padding neutrality: fixed-shape inactive order slots do not change the UPBA row
score. This is the key bridge lemma for padded ZK/FHE circuits.
-/
theorem rowScore_padRight_neutral (edges : List EdgeContribution) (n : Nat) :
    rowScore (padRight edges n) = rowScore edges := by
  simp [rowScore, padRight]

/--
Permutation invariance: because a row score is just a component-wise sum, the
score depends on the multiset of order-price hyperedges, not their list order.
-/
theorem rowScore_perm_invariant {edges₁ edges₂ : List EdgeContribution}
    (h : List.Perm edges₁ edges₂) :
    rowScore edges₁ = rowScore edges₂ := by
  have hd :
      (edges₁.map demandComponent).sum = (edges₂.map demandComponent).sum :=
    (h.map demandComponent).sum_eq
  have hs :
      (edges₁.map supplyComponent).sum = (edges₂.map supplyComponent).sum :=
    (h.map supplyComponent).sum_eq
  have hu :
      (edges₁.map surplusComponent).sum = (edges₂.map surplusComponent).sum :=
    (h.map surplusComponent).sum_eq
  simp [rowScore, hd, hs, hu]

/-- A minimal hypergraph fiber is the set of order-price hyperedges incident to one row. -/
structure PriceRowFiber where
  priceNum : Nat
  priceDen : Nat
  edges : List EdgeContribution
deriving Repr, DecidableEq

/-- Evaluating a row fiber is exactly the direct row-score evaluator on its edges. -/
def evalFiber (fiber : PriceRowFiber) : RowScore :=
  rowScore fiber.edges

theorem evalFiber_direct_score_equiv (fiber : PriceRowFiber) :
    evalFiber fiber = rowScore fiber.edges := by
  rfl

/--
Padded fiber neutrality: fixed-shape circuit padding preserves evaluation of an
entire price-row fiber.
-/
theorem evalFiber_padRight_neutral (fiber : PriceRowFiber) (n : Nat) :
    evalFiber { fiber with edges := padRight fiber.edges n } = evalFiber fiber := by
  simp [evalFiber, rowScore_padRight_neutral]

end ZenoHypergraph
