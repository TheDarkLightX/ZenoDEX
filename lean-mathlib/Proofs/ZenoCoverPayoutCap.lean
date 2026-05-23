import Mathlib

/-!
# ZenoCover Payout Cap

This file proves the small integer cap used by the internal ZenoCover
claim-verifier model. It does not model insurance law, oracle truth, or live
reserve operations. It only states the arithmetic guard: a covered claim's
authorized payout is capped by each declared bound, and an uncovered claim pays
zero. The sequential lemmas at the end show that repeatedly applying this
verifier against the current reserve cannot push the reserve below the declared
floor.
-/

namespace Proofs
namespace ZenoCoverPayoutCap

/-- Bounded payout for a covered claim.

The result is nonnegative and capped by requested payout, loss, policy coverage,
per-claim policy cap, and spendable reserve. -/
def authorizedPayout
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int) : Int :=
  max 0
    (min requested
      (min loss
        (min coverageLimit
          (min perClaimCap (reserveAvailable - minReserve)))))

/-- The verifier pays zero for an uncovered event. -/
def verifiedPayout
    (covered : Bool)
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int) : Int :=
  if covered then
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve
  else
    0

/-- Minimal claim input carried by the arithmetic verifier. -/
structure ClaimRequest where
  covered : Bool
  requested : Int
  loss : Int
  coverageLimit : Int
  perClaimCap : Int
deriving DecidableEq, Repr

/-- Verify a claim using the current reserve as the spendable-reserve input. -/
def ClaimRequest.verifiedAmount (claim : ClaimRequest) (reserveAvailable minReserve : Int) : Int :=
  verifiedPayout claim.covered claim.requested claim.loss claim.coverageLimit claim.perClaimCap
    reserveAvailable minReserve

/-- Apply one verified claim to the current reserve. -/
def settleOne (reserveAvailable minReserve : Int) (claim : ClaimRequest) : Int :=
  reserveAvailable - claim.verifiedAmount reserveAvailable minReserve

/-- Apply a list of verified claims in order, using the post-claim reserve each time. -/
def settleClaims (reserveAvailable minReserve : Int) : List ClaimRequest -> Int
  | [] => reserveAvailable
  | claim :: rest => settleClaims (settleOne reserveAvailable minReserve claim) minReserve rest

theorem authorizedPayout_nonneg
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int) :
    0 ≤
      authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve := by
  unfold authorizedPayout
  exact le_max_left 0 _

theorem verifiedPayout_nonneg
    (covered : Bool)
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int) :
    0 ≤ verifiedPayout covered requested loss coverageLimit perClaimCap reserveAvailable minReserve := by
  cases covered <;> simp [verifiedPayout, authorizedPayout_nonneg]

theorem authorizedPayout_le_requested
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hRequested : 0 ≤ requested) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      requested := by
  unfold authorizedPayout
  apply max_le hRequested
  exact min_le_left _ _

theorem authorizedPayout_le_loss
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hLoss : 0 ≤ loss) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      loss := by
  unfold authorizedPayout
  apply max_le hLoss
  exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem authorizedPayout_le_coverageLimit
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hCoverage : 0 ≤ coverageLimit) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      coverageLimit := by
  unfold authorizedPayout
  apply max_le hCoverage
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

theorem authorizedPayout_le_perClaimCap
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hPerClaimCap : 0 ≤ perClaimCap) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      perClaimCap := by
  unfold authorizedPayout
  apply max_le hPerClaimCap
  exact
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))

theorem authorizedPayout_le_spendableReserve
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hSpendable : 0 ≤ reserveAvailable - minReserve) :
    authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      reserveAvailable - minReserve := by
  unfold authorizedPayout
  apply max_le hSpendable
  exact
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))

theorem authorizedPayout_preserves_reserve_floor
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hSpendable : 0 ≤ reserveAvailable - minReserve) :
    minReserve ≤
      reserveAvailable -
        authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve := by
  have hCap :
      authorizedPayout requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
        reserveAvailable - minReserve :=
    authorizedPayout_le_spendableReserve (requested := requested) (loss := loss)
      (coverageLimit := coverageLimit) (perClaimCap := perClaimCap)
      (reserveAvailable := reserveAvailable) (minReserve := minReserve) hSpendable
  linarith

theorem verifiedPayout_zero_when_uncovered
    (requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int) :
    verifiedPayout false requested loss coverageLimit perClaimCap reserveAvailable minReserve = 0 := by
  rfl

theorem verifiedPayout_le_coverageLimit
    {covered : Bool}
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hCoverage : 0 ≤ coverageLimit) :
    verifiedPayout covered requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      coverageLimit := by
  cases covered <;> simp [verifiedPayout]
  · exact hCoverage
  · exact authorizedPayout_le_coverageLimit (requested := requested) (loss := loss)
      (coverageLimit := coverageLimit) (perClaimCap := perClaimCap)
      (reserveAvailable := reserveAvailable) (minReserve := minReserve) hCoverage

theorem verifiedPayout_le_spendableReserve
    {covered : Bool}
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hSpendable : 0 ≤ reserveAvailable - minReserve) :
  verifiedPayout covered requested loss coverageLimit perClaimCap reserveAvailable minReserve ≤
      reserveAvailable - minReserve := by
  cases covered <;> simp [verifiedPayout]
  · linarith
  · exact authorizedPayout_le_spendableReserve (requested := requested) (loss := loss)
      (coverageLimit := coverageLimit) (perClaimCap := perClaimCap)
      (reserveAvailable := reserveAvailable) (minReserve := minReserve) hSpendable

theorem verifiedPayout_preserves_reserve_floor
    {covered : Bool}
    {requested loss coverageLimit perClaimCap reserveAvailable minReserve : Int}
    (hReserve : minReserve ≤ reserveAvailable)
    (hSpendable : 0 ≤ reserveAvailable - minReserve) :
    minReserve ≤
      reserveAvailable -
        verifiedPayout covered requested loss coverageLimit perClaimCap reserveAvailable minReserve := by
  cases covered <;> simp [verifiedPayout]
  · exact hReserve
  · exact authorizedPayout_preserves_reserve_floor (requested := requested) (loss := loss)
      (coverageLimit := coverageLimit) (perClaimCap := perClaimCap)
      (reserveAvailable := reserveAvailable) (minReserve := minReserve) hSpendable

theorem claimRequest_verifiedAmount_nonneg
    (claim : ClaimRequest)
    (reserveAvailable minReserve : Int) :
    0 ≤ claim.verifiedAmount reserveAvailable minReserve := by
  cases claim
  simp [ClaimRequest.verifiedAmount, verifiedPayout_nonneg]

theorem claimRequest_verifiedAmount_le_spendableReserve
    {claim : ClaimRequest}
    {reserveAvailable minReserve : Int}
    (hSpendable : 0 ≤ reserveAvailable - minReserve) :
    claim.verifiedAmount reserveAvailable minReserve ≤ reserveAvailable - minReserve := by
  cases claim
  simp [ClaimRequest.verifiedAmount]
  exact verifiedPayout_le_spendableReserve hSpendable

theorem settleOne_preserves_reserve_floor
    {reserveAvailable minReserve : Int}
    (claim : ClaimRequest)
    (hReserve : minReserve ≤ reserveAvailable) :
    minReserve ≤ settleOne reserveAvailable minReserve claim := by
  unfold settleOne
  have hSpendable : 0 ≤ reserveAvailable - minReserve := by
    linarith
  exact verifiedPayout_preserves_reserve_floor
    (covered := claim.covered)
    (requested := claim.requested)
    (loss := claim.loss)
    (coverageLimit := claim.coverageLimit)
    (perClaimCap := claim.perClaimCap)
    (reserveAvailable := reserveAvailable)
    (minReserve := minReserve)
    hReserve
    hSpendable

theorem settleOne_le_reserve
    {reserveAvailable minReserve : Int}
    (claim : ClaimRequest) :
    settleOne reserveAvailable minReserve claim ≤ reserveAvailable := by
  unfold settleOne
  have hNonneg : 0 ≤ claim.verifiedAmount reserveAvailable minReserve :=
    claimRequest_verifiedAmount_nonneg claim reserveAvailable minReserve
  linarith

theorem settleClaims_preserves_reserve_floor
    (claims : List ClaimRequest)
    {reserveAvailable minReserve : Int}
    (hReserve : minReserve ≤ reserveAvailable) :
    minReserve ≤ settleClaims reserveAvailable minReserve claims := by
  induction claims generalizing reserveAvailable with
  | nil =>
      simpa [settleClaims] using hReserve
  | cons claim rest ih =>
      simp [settleClaims]
      exact ih (settleOne_preserves_reserve_floor claim hReserve)

end ZenoCoverPayoutCap
end Proofs
