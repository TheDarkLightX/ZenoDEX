import Mathlib

/-!
# zUSD protocol-fee claim realization algebra

This file proves the local equations used by the Python
`ZUSDProtocolFeeClaimRealizationV1` candidate. Realization moves one exact
amount from the current claim into issued ledger supply and protocol escrow.

It does not prove U256 refinement, E8 codec parity, caller authentication,
complete ledger inventory, fee distribution, atomic publication, mounting, or
no-bypass.
-/

namespace ZUSDProtocolFeeClaimRealization

/-- Abstract monetary and custody slice needed by one realization. -/
structure State where
  debt : Nat
  ledgerSupply : Nat
  outstandingClaim : Nat
  accruedCumulative : Nat
  protocolEscrow : Nat
  deriving DecidableEq, Repr

/-- Debt is partitioned between issued supply and the exact unissued claim. -/
def Balanced (s : State) : Prop :=
  s.debt = s.ledgerSupply + s.outstandingClaim

/-- The current claim is a suffix of cumulative protocol-fee accrual. -/
def ClaimValid (s : State) : Prop :=
  s.outstandingClaim ≤ s.accruedCumulative

/-- Protocol escrow contains only value already represented in ledger supply. -/
def EscrowBacked (s : State) : Prop :=
  s.protocolEscrow ≤ s.ledgerSupply

/-- Exact realization credits supply and escrow while reducing the claim. -/
def realize (s : State) (amount : Nat) : State :=
  { s with
    ledgerSupply := s.ledgerSupply + amount
    outstandingClaim := s.outstandingClaim - amount
    protocolEscrow := s.protocolEscrow + amount }

/-- Realization preserves debt partitioning when the amount is outstanding. -/
theorem realize_preserves_balanced
    (s : State)
    (amount : Nat)
    (hbalanced : Balanced s)
    (hle : amount ≤ s.outstandingClaim) :
    Balanced (realize s amount) := by
  simp [Balanced, realize] at *
  omega

/-- Realization preserves the historical accrual bound. -/
theorem realize_preserves_claim_valid
    (s : State)
    (amount : Nat)
    (hvalid : ClaimValid s) :
    ClaimValid (realize s amount) := by
  simp [ClaimValid, realize] at *
  omega

/-- Crediting escrow and ledger supply equally preserves escrow backing. -/
theorem realize_preserves_escrow_backed
    (s : State)
    (amount : Nat)
    (hbacked : EscrowBacked s) :
    EscrowBacked (realize s amount) := by
  simp [EscrowBacked, realize] at *
  omega

/-- The local supply-plus-claim quantity is unchanged by realization. -/
theorem realize_preserves_supply_claim_sum
    (s : State)
    (amount : Nat)
    (hle : amount ≤ s.outstandingClaim) :
    (realize s amount).ledgerSupply + (realize s amount).outstandingClaim =
      s.ledgerSupply + s.outstandingClaim := by
  simp [realize]
  omega

/-- Protocol escrow increases by exactly the realized amount. -/
theorem realize_escrow_delta_exact
    (s : State)
    (amount : Nat) :
    (realize s amount).protocolEscrow = s.protocolEscrow + amount := by
  rfl

/-- Whole-unit scaling does not change the realization conservation law. -/
theorem realize_scaled_units_preserves_supply_claim_sum
    (s : State)
    (amountUnits scale : Nat)
    (hle : amountUnits * scale ≤ s.outstandingClaim) :
    (realize s (amountUnits * scale)).ledgerSupply +
        (realize s (amountUnits * scale)).outstandingClaim =
      s.ledgerSupply + s.outstandingClaim := by
  exact realize_preserves_supply_claim_sum s (amountUnits * scale) hle

#print axioms realize_preserves_balanced
#print axioms realize_preserves_escrow_backed
#print axioms realize_scaled_units_preserves_supply_claim_sum

end ZUSDProtocolFeeClaimRealization
