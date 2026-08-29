import Init.Omega

/-!
Restricted natural-number accounting theorems for one atomic ZDEX buyback.

All fields are nonnegative integer atoms. Quote-denominated fields use one
quote asset and ZDEX-denominated fields use one ZDEX asset. The
`otherAllocations` field is the already-summed value of every disjoint fee
allocation other than `buybackAllocation`. The six equations in
`AtomicBuybackAssumptions` are explicit premises about one atomic occurrence:

* `F = b + sum(other) + r` for fee allocation and carried residue;
* `B1 + q = B0 + b` for the buyback reserve;
* the Spot quote reserve increases by exactly `q`;
* the Spot ZDEX reserve decreases by exactly the purchased amount `p`;
* the purchased amount equals the burned amount; and
* live ZDEX supply decreases by exactly `p`.

The composed theorem cancels the internal fee-to-reserve and reserve-to-Spot
movements. It proves conservation of quote atoms across the represented
locations and exact reduction of both the Spot ZDEX reserve and live ZDEX
supply by the burn amount.

Nonclaims: this file does not prove that a runtime transition establishes the
premises. It does not authenticate the occurrence, assets, pool, profile,
Oracle/TWAP data, receipts, roots, route, terminal obligations, or replay
state. It does not prove CPMM pricing, minimum output, price impact, MEV
resistance, cadence, spend-cap admission, finite machine-width safety,
canonical encoding, atomic publication, hosting policy, or a hyperdeflation
policy. Those remain separate refinement and verifier obligations.
-/

namespace Proofs
namespace ZDEXAtomicBuybackAccountingV1

/-- The buyback fee command has no independent amount parameter. -/
def deriveFeeCommand (committedFeeIngress : Nat) : Nat :=
  committedFeeIngress

/-- Construction from committed ingress removes caller-selected fee budgets. -/
theorem derived_fee_command_equals_committed_ingress
    (committedFeeIngress : Nat) :
    deriveFeeCommand committedFeeIngress = committedFeeIngress := rfl

/-- Amounts observed before and after one proposed atomic buyback occurrence. -/
structure AtomicBuybackAmounts where
  feeTotal : Nat
  buybackAllocation : Nat
  otherAllocations : Nat
  carriedResidue : Nat
  buybackReservePre : Nat
  buybackReservePost : Nat
  quoteSpend : Nat
  spotQuoteReservePre : Nat
  spotQuoteReservePost : Nat
  spotZdexReservePre : Nat
  spotZdexReservePost : Nat
  purchased : Nat
  burned : Nat
  liveSupplyPre : Nat
  liveSupplyPost : Nat

/-- The six accounting equations required from the authenticated transition. -/
structure AtomicBuybackAssumptions (a : AtomicBuybackAmounts) : Prop where
  feeConservation :
    a.feeTotal =
      a.buybackAllocation + a.otherAllocations + a.carriedResidue
  buybackReserveConservation :
    a.buybackReservePost + a.quoteSpend =
      a.buybackReservePre + a.buybackAllocation
  spotQuoteReserveIncrease :
    a.spotQuoteReservePost = a.spotQuoteReservePre + a.quoteSpend
  spotZdexReserveDecrease :
    a.spotZdexReservePost + a.purchased = a.spotZdexReservePre
  exactPurchasedBurned : a.purchased = a.burned
  liveSupplyDecrease : a.liveSupplyPost + a.purchased = a.liveSupplyPre

/-- Quote atoms before equal quote atoms after, after internal flows cancel. -/
def QuoteConserved (a : AtomicBuybackAmounts) : Prop :=
  a.feeTotal + a.buybackReservePre + a.spotQuoteReservePre =
    a.otherAllocations + a.carriedResidue +
      a.buybackReservePost + a.spotQuoteReservePost

theorem quote_conservation
    (a : AtomicBuybackAmounts)
    (h : AtomicBuybackAssumptions a) :
    QuoteConserved a := by
  unfold QuoteConserved
  rcases h with
    ⟨hFee, hReserve, hSpotQuote, _hSpotZdex, _hPurchasedBurned, _hSupply⟩
  omega

theorem spot_zdex_reduction_by_exact_burn
    (a : AtomicBuybackAmounts)
    (h : AtomicBuybackAssumptions a) :
    a.spotZdexReservePost + a.burned = a.spotZdexReservePre := by
  rcases h with
    ⟨_hFee, _hReserve, _hSpotQuote, hSpotZdex, hPurchasedBurned, _hSupply⟩
  omega

theorem live_supply_reduction_by_exact_burn
    (a : AtomicBuybackAmounts)
    (h : AtomicBuybackAssumptions a) :
    a.liveSupplyPost + a.burned = a.liveSupplyPre := by
  rcases h with
    ⟨_hFee, _hReserve, _hSpotQuote, _hSpotZdex, hPurchasedBurned, hSupply⟩
  omega

/-- Subtraction form plus the no-underflow bound implied by exact reduction. -/
theorem live_supply_post_eq_pre_sub_burn
    (a : AtomicBuybackAmounts)
    (h : AtomicBuybackAssumptions a) :
    a.burned ≤ a.liveSupplyPre ∧
      a.liveSupplyPost = a.liveSupplyPre - a.burned := by
  rcases h with
    ⟨_hFee, _hReserve, _hSpotQuote, _hSpotZdex, hPurchasedBurned, hSupply⟩
  constructor <;> omega

/--
All six premises compose into quote conservation, exact purchase-to-burn
equality, exact pool output, and exact live-supply reduction.
-/
theorem atomic_equations_compose
    (a : AtomicBuybackAmounts)
    (h : AtomicBuybackAssumptions a) :
    QuoteConserved a ∧
      a.purchased = a.burned ∧
      a.spotZdexReservePost + a.burned = a.spotZdexReservePre ∧
      a.liveSupplyPost + a.burned = a.liveSupplyPre := by
  exact ⟨quote_conservation a h, h.exactPurchasedBurned,
    spot_zdex_reduction_by_exact_burn a h,
    live_supply_reduction_by_exact_burn a h⟩

/-- A positive concrete occurrence shows that the premise set is satisfiable. -/
def nonvacuityWitness : AtomicBuybackAmounts where
  feeTotal := 10
  buybackAllocation := 4
  otherAllocations := 5
  carriedResidue := 1
  buybackReservePre := 7
  buybackReservePost := 8
  quoteSpend := 3
  spotQuoteReservePre := 20
  spotQuoteReservePost := 23
  spotZdexReservePre := 13
  spotZdexReservePost := 10
  purchased := 3
  burned := 3
  liveSupplyPre := 100
  liveSupplyPost := 97

theorem nonvacuity_witness_satisfies_assumptions :
    AtomicBuybackAssumptions nonvacuityWitness := by
  constructor <;> decide

end ZDEXAtomicBuybackAccountingV1
end Proofs
