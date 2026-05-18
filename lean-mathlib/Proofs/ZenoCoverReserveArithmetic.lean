import Mathlib

/-!
# ZenoCover Reserve Arithmetic

This file promotes the Aristotle-checked natural-number reserve-floor lemmas
for the internal ZenoCover research track. It proves that verified sequential
claim settlement cannot spend below a declared reserve floor when each claim is
capped by the current spendable reserve.

It does not model insurance law, claim truth, oracle honesty, custody, live
reserve operations, or any promise to pay.
-/

namespace Proofs
namespace ZenoCoverReserveArithmetic

/-- Minimal claim input carried by the arithmetic verifier. -/
structure ClaimRequest where
  covered : Bool
  requested : Nat
  loss : Nat
  coverageLimit : Nat
  perClaimCap : Nat
deriving DecidableEq, Repr

/-- Covered payout capped by request, loss, policy limit, per-claim cap, and spendable reserve. -/
def authorizedPayout
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Nat) : Nat :=
  min requested
    (min loss
      (min coverageLimit
        (min perClaimCap (reserveAvailable - minReserve))))

/-- The verifier pays zero for an uncovered event. -/
def verifiedPayout
    (covered : Bool)
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Nat) : Nat :=
  if covered then
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve
  else
    0

/-- Verify a claim using the current reserve as the spendable-reserve input. -/
def ClaimRequest.verifiedAmount
    (claim : ClaimRequest)
    (reserveAvailable minReserve : Nat) : Nat :=
  verifiedPayout claim.covered claim.requested claim.loss claim.coverageLimit claim.perClaimCap
    reserveAvailable minReserve

/-- Apply one verified claim to the current reserve. -/
def settleOne (reserveAvailable minReserve : Nat) (claim : ClaimRequest) : Nat :=
  reserveAvailable - claim.verifiedAmount reserveAvailable minReserve

/-- Apply a list of verified claims in order, using the post-claim reserve each time. -/
def settleClaims (reserveAvailable minReserve : Nat) : List ClaimRequest -> Nat
  | [] => reserveAvailable
  | claim :: rest => settleClaims (settleOne reserveAvailable minReserve claim) minReserve rest

/-- Total paid by sequential settlement from the starting reserve. -/
def totalPaid (reserveAvailable minReserve : Nat) (claims : List ClaimRequest) : Nat :=
  reserveAvailable - settleClaims reserveAvailable minReserve claims

theorem authorizedPayout_le_spendable
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Nat) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      reserveAvailable - minReserve := by
  unfold authorizedPayout
  exact
    Nat.le_trans (Nat.min_le_right _ _)
      (Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)))

theorem verifiedPayout_le_spendable
    (covered : Bool)
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Nat) :
    verifiedPayout covered requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      reserveAvailable - minReserve := by
  simp [verifiedPayout]
  split
  · exact authorizedPayout_le_spendable _ _ _ _ _ _
  · omega

theorem claim_verifiedAmount_le_spendable
    (claim : ClaimRequest)
    (reserveAvailable minReserve : Nat) :
    claim.verifiedAmount reserveAvailable minReserve ≤ reserveAvailable - minReserve := by
  exact verifiedPayout_le_spendable _ _ _ _ _ _ _

theorem settleOne_preserves_floor
    (claim : ClaimRequest)
    {reserveAvailable minReserve : Nat}
    (hReserve : minReserve ≤ reserveAvailable) :
    minReserve ≤ settleOne reserveAvailable minReserve claim := by
  simp [settleOne]
  have hVerified := claim_verifiedAmount_le_spendable claim reserveAvailable minReserve
  omega

theorem settleOne_le_reserve
    (claim : ClaimRequest)
    (reserveAvailable minReserve : Nat) :
    settleOne reserveAvailable minReserve claim ≤ reserveAvailable := by
  exact Nat.sub_le _ _

theorem settleClaims_preserves_floor
    (claims : List ClaimRequest)
    {reserveAvailable minReserve : Nat}
    (hReserve : minReserve ≤ reserveAvailable) :
    minReserve ≤ settleClaims reserveAvailable minReserve claims := by
  induction claims generalizing reserveAvailable with
  | nil =>
      simpa [settleClaims] using hReserve
  | cons claim rest ih =>
      simp [settleClaims]
      exact ih (settleOne_preserves_floor claim hReserve)

theorem settleClaims_le_reserve
    (claims : List ClaimRequest)
    (reserveAvailable minReserve : Nat) :
    settleClaims reserveAvailable minReserve claims ≤ reserveAvailable := by
  induction claims generalizing reserveAvailable with
  | nil =>
      simp [settleClaims]
  | cons claim rest ih =>
      simp [settleClaims]
      exact Nat.le_trans (ih _) (settleOne_le_reserve claim reserveAvailable minReserve)

theorem totalPaid_le_spendable
    (claims : List ClaimRequest)
    {reserveAvailable minReserve : Nat}
    (hReserve : minReserve ≤ reserveAvailable) :
    totalPaid reserveAvailable minReserve claims ≤ reserveAvailable - minReserve := by
  simp [totalPaid]
  have hSettled := settleClaims_preserves_floor claims hReserve
  omega

end ZenoCoverReserveArithmetic
end Proofs
