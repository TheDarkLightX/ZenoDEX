import Init.Omega
import Init.Data.Order.Lemmas

/-!
Restricted natural-number theorems for governed ZDEX buyback spend selection.

The runtime-aligned selection is

  q = min (B0 + b) (min perCommandCap routeSafeLimit)

where `B0` is the accumulated buyback reserve and `b` is the allocation joined
by the same atomic command. These theorems establish cap safety, the exact
minimum-spend admission condition, deterministic cadence arithmetic, and reserve
conservation.

They do not establish Oracle authenticity, price integrity, minimum output,
pool identity, receipt validity, machine-width admission, route composition, or
publication authority.
-/

namespace Proofs
namespace ZDEXBuybackSpendV1

open Std

/-- The sole governed quote-spend selection rule. -/
def selectedQuoteSpend
    (availableReserve perCommandCap routeSafeLimit : Nat) : Nat :=
  min availableReserve (min perCommandCap routeSafeLimit)

/-- Consensus-height cadence gate used after a prior execution. -/
def cadenceEligible
    (currentHeight lastExecutionHeight minimumIntervalBlocks : Nat) : Prop :=
  lastExecutionHeight + minimumIntervalBlocks ≤ currentHeight

theorem selected_le_available
    (availableReserve perCommandCap routeSafeLimit : Nat) :
    selectedQuoteSpend availableReserve perCommandCap routeSafeLimit ≤
      availableReserve := by
  unfold selectedQuoteSpend
  exact min_le_left

theorem selected_le_per_command_cap
    (availableReserve perCommandCap routeSafeLimit : Nat) :
    selectedQuoteSpend availableReserve perCommandCap routeSafeLimit ≤
      perCommandCap := by
  unfold selectedQuoteSpend
  exact le_trans
    (min_le_right (a := availableReserve) (b := min perCommandCap routeSafeLimit))
    (min_le_left (a := perCommandCap) (b := routeSafeLimit))

theorem selected_le_route_safe_limit
    (availableReserve perCommandCap routeSafeLimit : Nat) :
    selectedQuoteSpend availableReserve perCommandCap routeSafeLimit ≤
      routeSafeLimit := by
  unfold selectedQuoteSpend
  exact le_trans
    (min_le_right (a := availableReserve) (b := min perCommandCap routeSafeLimit))
    (min_le_right (a := perCommandCap) (b := routeSafeLimit))

/-- A minimum spend is accepted exactly when all three limits meet it. -/
theorem minimum_spend_accepted_iff
    (minimumSpend availableReserve perCommandCap routeSafeLimit : Nat) :
    minimumSpend ≤ selectedQuoteSpend availableReserve perCommandCap routeSafeLimit ↔
      minimumSpend ≤ availableReserve ∧
      minimumSpend ≤ perCommandCap ∧
      minimumSpend ≤ routeSafeLimit := by
  simp only [selectedQuoteSpend, le_min_iff]

/-- Debiting the selected amount exactly conserves the accumulated reserve. -/
theorem reserve_conservation
    (availableReserve perCommandCap routeSafeLimit : Nat) :
    availableReserve -
          selectedQuoteSpend availableReserve perCommandCap routeSafeLimit +
        selectedQuoteSpend availableReserve perCommandCap routeSafeLimit =
      availableReserve := by
  have hselected := selected_le_available
    availableReserve perCommandCap routeSafeLimit
  omega

/-- The same-command allocation and selected debit satisfy `B1 + q = B0 + b`. -/
theorem atomic_allocation_reserve_conservation
    (reserveBefore buybackAllocation perCommandCap routeSafeLimit : Nat) :
    let availableReserve := reserveBefore + buybackAllocation
    let selectedSpend :=
      selectedQuoteSpend availableReserve perCommandCap routeSafeLimit
    (availableReserve - selectedSpend) + selectedSpend = availableReserve := by
  exact reserve_conservation
    (reserveBefore + buybackAllocation) perCommandCap routeSafeLimit

/-- The cadence gate accepts the exact governed boundary. -/
theorem cadence_accepts_exact_boundary
    (lastExecutionHeight minimumIntervalBlocks : Nat) :
    cadenceEligible
      (lastExecutionHeight + minimumIntervalBlocks)
      lastExecutionHeight
      minimumIntervalBlocks := by
  simp [cadenceEligible]

/-- One block before a positive cadence boundary remains ineligible. -/
theorem cadence_rejects_predecessor
    (lastExecutionHeight minimumIntervalBlocks : Nat)
    (hinterval : 0 < minimumIntervalBlocks) :
    ¬ cadenceEligible
      (lastExecutionHeight + minimumIntervalBlocks - 1)
      lastExecutionHeight
      minimumIntervalBlocks := by
  simp only [cadenceEligible]
  omega

end ZDEXBuybackSpendV1
end Proofs
