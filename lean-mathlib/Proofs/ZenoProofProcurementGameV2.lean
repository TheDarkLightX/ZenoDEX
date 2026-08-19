import Mathlib

/-!
# ZenoProof Procurement Game V2

Restricted arithmetic theorems for the research-only proof-procurement design.
The threshold theorem assumes a fixed bidder set, a bidder-independent critical
threshold, quasilinear utility, objective delivery, and no coalition.  These
theorems grant no auction, payment, proof, or settlement authority.
-/

namespace ZenoProofProcurementGameV2

/-- Utility in a single-parameter reverse auction with an own-bid-independent
critical threshold.  A report at or below the threshold wins and is paid the
threshold. -/
def thresholdUtility (cost threshold report : Int) : Int :=
  if report ≤ threshold then threshold - cost else 0

/-- Truthful cost reporting weakly dominates every unilateral report when the
critical threshold is independent of the bidder's own report. -/
theorem truthful_weakly_dominates_threshold
    (cost threshold report : Int) :
    thresholdUtility cost threshold cost ≥
      thresholdUtility cost threshold report := by
  unfold thresholdUtility
  by_cases hCost : cost ≤ threshold
  · simp [hCost]
    by_cases hReport : report ≤ threshold
    · simp [hReport]
    · simp [hReport]
      omega
  · simp [hCost]
    by_cases hReport : report ≤ threshold
    · simp [hReport]
      omega
    · simp [hReport]

/-- A truthful threshold winner is ex-post individually rational. -/
theorem truthful_threshold_winner_nonnegative
    (cost threshold : Int) (h : cost ≤ threshold) :
    0 ≤ thresholdUtility cost threshold cost := by
  simp [thresholdUtility, h]

/-- Utility for a selected first-price procurement seller. -/
def firstPriceWinnerUtility (cost report : Int) : Int := report - cost

/-- A first-price procurement winner with cost one profits by reporting two
while a competitor remains at three. -/
theorem first_price_truthfulness_counterexample :
    firstPriceWinnerUtility 1 2 > firstPriceWinnerUtility 1 1 := by
  norm_num [firstPriceWinnerUtility]

/-- Joint utility of a selected seller of cost one and an unselected partner
when the selected seller receives the critical payment. -/
def twoMemberCoalitionUtility (criticalPayment : Int) : Int :=
  (criticalPayment - 1) + 0

/-- The two low-cost bidders increase their joint utility when the runner-up
raises a reverse-second-price report from two to four. -/
theorem critical_price_coalition_counterexample :
    twoMemberCoalitionUtility 4 > twoMemberCoalitionUtility 2 := by
  norm_num [twoMemberCoalitionUtility]

/-- One provider identity contributes a nonnegative measured capacity. -/
structure CapacityAlias where
  measuredUnits : Nat

/-- Aggregate owner weight is the sum of all authenticated aliases attributed
to that owner. -/
def ownerTicketWeight (aliases : List CapacityAlias) : Nat :=
  (aliases.map CapacityAlias.measuredUnits).sum

/-- Splitting one owner's measured capacity into two attributed aliases leaves
its aggregate ticket weight unchanged. -/
theorem capacity_ticket_split_preserves_owner_weight (a b : Nat) :
    ownerTicketWeight [{ measuredUnits := a }, { measuredUnits := b }] =
      ownerTicketWeight [{ measuredUnits := a + b }] := by
  simp [ownerTicketWeight]

/-- A posted payment derived only from benchmark, margin, and caps is unchanged
by a current-round acceptance bit. -/
def postedPayment (benchmark margin cap : Nat) : Nat :=
  min cap (benchmark + margin)

/-- A same-occurrence scarcity payment capped no higher than the posted price
cannot pay the seller more than the posted price. -/
def scarcitySellerPayment (bid cap : Nat) : Nat := min bid cap

theorem scarcity_payment_has_no_same_occurrence_uplift
    (posted cap bid : Nat) (hCap : cap ≤ posted) :
    scarcitySellerPayment bid cap ≤ posted := by
  exact le_trans (Nat.min_le_right bid cap) hCap

/-- For three risk-neutral symmetric provers with perfect monitoring,
stationary equal sharing, immediate grim-trigger punishment, and zero
punishment profit, discount factor two-thirds is exactly the boundary where
cooperation and one-shot deviation both have present value three when monopoly
margin is three. -/
theorem three_prover_stationary_equal_share_boundary :
    ((1 : Rat) / (1 - 2 / 3)) = 3 ∧
      (3 : Rat) + (2 / 3) * 0 / (1 - 2 / 3) = 3 := by
  norm_num

/-- A bounded representation of a fully disposed prover-fault bond. -/
structure BondDisposition where
  restitution : Nat
  residualInsurance : Nat

def disposeBond (bond namedRestitution : Nat) : BondDisposition :=
  let restitution := min namedRestitution bond
  { restitution := restitution, residualInsurance := bond - restitution }

def bondDispositionTotal (disposition : BondDisposition) : Nat :=
  disposition.restitution + disposition.residualInsurance

/-- Full disposition conserves the original bond even when the named loss is
larger than the bond.  Separate admission logic requires full loss coverage. -/
theorem full_default_bond_disposition_conserves
    (bond namedRestitution : Nat) :
    bondDispositionTotal (disposeBond bond namedRestitution) = bond := by
  simp [bondDispositionTotal, disposeBond]

end ZenoProofProcurementGameV2
