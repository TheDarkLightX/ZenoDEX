import Mathlib.Tactic

/-!
# Atomic-route protocol-fee conservation

Each leg partitions gross input into pool-reserve credit and protocol credit.
Local conservation therefore composes across a finite route.

Non-claims: route optimality, quote authenticity, authorization,
supported-curve coverage, integer-domain bounds, and shell atomicity.
-/

namespace Proofs
namespace RouteProtocolFeeConservation

/-- Value flow for one route leg, expressed in a single asset and unit. -/
structure LegFlow where
  amountIn : Nat
  reserveCredit : Nat
  protocolCredit : Nat
  deriving DecidableEq, Repr

/-- A leg conserves when its gross input is fully partitioned. -/
def LegFlow.Conserves (leg : LegFlow) : Prop :=
  leg.amountIn = leg.reserveCredit + leg.protocolCredit

/-- Canonical fee split used after proving the fee is bounded. -/
def canonicalLegFlow (amountIn protocolCredit : Nat) : LegFlow :=
  {
    amountIn := amountIn
    reserveCredit := amountIn - protocolCredit
    protocolCredit := protocolCredit
  }

theorem canonical_leg_conserves
    {amountIn protocolCredit : Nat}
    (hBounded : protocolCredit ≤ amountIn) :
    (canonicalLegFlow amountIn protocolCredit).Conserves := by
  unfold canonicalLegFlow LegFlow.Conserves
  exact (Nat.sub_add_cancel hBounded).symm

def totalAmountIn : List LegFlow → Nat
  | [] => 0
  | leg :: rest => leg.amountIn + totalAmountIn rest

def totalReserveCredit : List LegFlow → Nat
  | [] => 0
  | leg :: rest => leg.reserveCredit + totalReserveCredit rest

def totalProtocolCredit : List LegFlow → Nat
  | [] => 0
  | leg :: rest => leg.protocolCredit + totalProtocolCredit rest

/-- Local conservation composes across an arbitrary finite route. -/
theorem route_conserves_of_legs
    (legs : List LegFlow)
    (hLegs : ∀ leg ∈ legs, leg.Conserves) :
    totalAmountIn legs =
      totalReserveCredit legs + totalProtocolCredit legs := by
  induction legs with
  | nil =>
      rfl
  | cons leg rest ih =>
      have hLeg : leg.Conserves := hLegs leg (by simp)
      have hRest : ∀ tailLeg ∈ rest, tailLeg.Conserves := by
        intro tailLeg hTailLeg
        exact hLegs tailLeg (by simp [hTailLeg])
      have hTail := ih hRest
      unfold LegFlow.Conserves at hLeg
      simp only [totalAmountIn, totalReserveCredit, totalProtocolCredit]
      omega

/-- Build the runtime-shaped route from gross-input/protocol-credit pairs. -/
def canonicalRoute (flows : List (Nat × Nat)) : List LegFlow :=
  flows.map fun flow => canonicalLegFlow flow.1 flow.2

/-- Bounded canonical fee splits conserve for the complete finite route. -/
theorem canonical_route_conserves
    (flows : List (Nat × Nat))
    (hBounded : ∀ flow ∈ flows, flow.2 ≤ flow.1) :
    totalAmountIn (canonicalRoute flows) =
      totalReserveCredit (canonicalRoute flows) +
        totalProtocolCredit (canonicalRoute flows) := by
  apply route_conserves_of_legs
  intro leg hLeg
  unfold canonicalRoute at hLeg
  rw [List.mem_map] at hLeg
  obtain ⟨flow, hFlow, rfl⟩ := hLeg
  exact canonical_leg_conserves (hBounded flow hFlow)

end RouteProtocolFeeConservation
end Proofs
