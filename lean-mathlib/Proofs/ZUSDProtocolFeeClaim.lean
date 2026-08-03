import Mathlib

/-!
# zUSD current protocol-fee claim algebra

This file proves the abstract state equations used by the Python
`ZUSDProtocolFeeClaimV1` and V2 supply-claim delta certificate.

It does not prove U256 refinement, claimant authentication, complete custody,
fee-router semantics, runtime mounting, or atomic publication.
-/

namespace ZUSDProtocolFeeClaim

/-- Abstract global slice needed by the current-claim accounting relation. -/
structure State where
  debt : Nat
  ledgerSupply : Nat
  outstandingClaim : Nat
  accruedCumulative : Nat
  deriving DecidableEq, Repr

/-- Current debt equals issued ledger supply plus the exact unissued claim. -/
def Balanced (s : State) : Prop :=
  s.debt = s.ledgerSupply + s.outstandingClaim

/-- The current claim cannot exceed all fees accrued historically. -/
def ClaimValid (s : State) : Prop :=
  s.outstandingClaim ≤ s.accruedCumulative

/-- Historically realized fee value is derived rather than stored independently. -/
def realizedCumulative (s : State) : Nat :=
  s.accruedCumulative - s.outstandingClaim

/-- Collateral-backed mint: principal becomes supply and fee becomes a claim. -/
def mint (s : State) (principal fee : Nat) : State :=
  { s with
    debt := s.debt + principal + fee
    ledgerSupply := s.ledgerSupply + principal
    outstandingClaim := s.outstandingClaim + fee
    accruedCumulative := s.accruedCumulative + fee }

/-- Claim settlement: exact claim value becomes ledger supply without new debt. -/
def settle (s : State) (amount : Nat) : State :=
  { s with
    ledgerSupply := s.ledgerSupply + amount
    outstandingClaim := s.outstandingClaim - amount }

/-- Repayment burns issued ledger supply and debt equally. -/
def repay (s : State) (amount : Nat) : State :=
  { s with
    debt := s.debt - amount
    ledgerSupply := s.ledgerSupply - amount }

/-- The cumulative fee history partitions into realized and outstanding value. -/
theorem realized_add_outstanding_eq_accrued
    (s : State)
    (hvalid : ClaimValid s) :
    realizedCumulative s + s.outstandingClaim = s.accruedCumulative := by
  simp [realizedCumulative, ClaimValid] at *
  omega

/-- Mint preserves the debt/supply/current-claim equation. -/
theorem mint_preserves_balanced
    (s : State)
    (principal fee : Nat)
    (hbalanced : Balanced s) :
    Balanced (mint s principal fee) := by
  simp [Balanced, mint] at *
  omega

/-- Mint preserves the current-claim bound. -/
theorem mint_preserves_claim_valid
    (s : State)
    (principal fee : Nat)
    (hvalid : ClaimValid s) :
    ClaimValid (mint s principal fee) := by
  simp [ClaimValid, mint] at *
  omega

/-- Exact settlement preserves the debt/supply/current-claim equation. -/
theorem settle_preserves_balanced
    (s : State)
    (amount : Nat)
    (hbalanced : Balanced s)
    (hle : amount ≤ s.outstandingClaim) :
    Balanced (settle s amount) := by
  simp [Balanced, settle] at *
  omega

/-- Exact settlement preserves the current-claim bound. -/
theorem settle_preserves_claim_valid
    (s : State)
    (amount : Nat)
    (hvalid : ClaimValid s) :
    ClaimValid (settle s amount) := by
  simp [ClaimValid, settle] at *
  omega

/-- Repayment from issued ledger supply preserves the accounting equation. -/
theorem repay_preserves_balanced
    (s : State)
    (amount : Nat)
    (hbalanced : Balanced s)
    (hle : amount ≤ s.ledgerSupply) :
    Balanced (repay s amount) := by
  simp [Balanced, repay] at *
  omega

/-- Signed transition-local deltas used by the V2 runtime certificate. -/
structure Delta where
  debt : Int
  ledgerSupply : Int
  outstandingClaim : Int
  deriving DecidableEq, Repr

/-- A delta is exact when debt change equals supply plus current-claim change. -/
def Delta.Exact (d : Delta) : Prop :=
  d.debt = d.ledgerSupply + d.outstandingClaim

/-- Derive the signed delta between two natural-number states. -/
def delta (pre post : State) : Delta where
  debt := Int.ofNat post.debt - Int.ofNat pre.debt
  ledgerSupply := Int.ofNat post.ledgerSupply - Int.ofNat pre.ledgerSupply
  outstandingClaim :=
    Int.ofNat post.outstandingClaim - Int.ofNat pre.outstandingClaim

/-- Any two balanced endpoints induce an exact V2 supply-claim delta. -/
theorem delta_exact_of_balanced
    (pre post : State)
    (hpre : Balanced pre)
    (hpost : Balanced post) :
    (delta pre post).Exact := by
  simp [Delta.Exact, delta, Balanced] at *
  omega

/-- Exact signed deltas compose additively. -/
theorem exact_add
    (a b : Delta)
    (ha : a.Exact)
    (hb : b.Exact) :
    (Delta.mk
      (a.debt + b.debt)
      (a.ledgerSupply + b.ledgerSupply)
      (a.outstandingClaim + b.outstandingClaim)).Exact := by
  simp [Delta.Exact] at *
  omega

/-- Delta composition agrees with the direct endpoint delta. -/
theorem delta_compose
    (a b c : State) :
    delta a c =
      Delta.mk
        ((delta a b).debt + (delta b c).debt)
        ((delta a b).ledgerSupply + (delta b c).ledgerSupply)
        ((delta a b).outstandingClaim + (delta b c).outstandingClaim) := by
  simp [delta]

#print axioms delta_exact_of_balanced
#print axioms exact_add

end ZUSDProtocolFeeClaim
