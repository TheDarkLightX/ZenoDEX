/-!
# Proof Market Safety

Minimal proof-market safety lemmas for the ZenoProof sale gate.

The theorem surface mirrors the Python `proof_market_policy` gate:
seller payment requires a verified, bound, non-vacuous, unclaimed proof with
the required buyer signoff and escrow funding. Reputation is advisory and cannot
replace verifier acceptance.
-/

namespace Proofs
namespace ProofMarketSafety

structure ProofMarketChecks where
  verifierAccepts : Prop
  theoremBindingMatches : Prop
  artifactHashMatches : Prop
  publicInputsHashMatches : Prop
  assumptionsHashMatches : Prop
  nonVacuityWitness : Prop
  proposalHashUnclaimed : Prop
  buyerSignoffOk : Prop
  escrowFunded : Prop
  revealRequested : Prop
  paymentFinalizedOrEscrowLocked : Prop

def SellerPayable (c : ProofMarketChecks) : Prop :=
  c.verifierAccepts ∧
  c.theoremBindingMatches ∧
  c.artifactHashMatches ∧
  c.publicInputsHashMatches ∧
  c.assumptionsHashMatches ∧
  c.nonVacuityWitness ∧
  c.proposalHashUnclaimed ∧
  c.buyerSignoffOk ∧
  c.escrowFunded

def FullPayloadReleasable (c : ProofMarketChecks) : Prop :=
  SellerPayable c ∧ c.revealRequested ∧ c.paymentFinalizedOrEscrowLocked

theorem payable_implies_verifier_accepts
    {c : ProofMarketChecks} (h : SellerPayable c) :
    c.verifierAccepts :=
  h.left

theorem payable_implies_non_vacuous
    {c : ProofMarketChecks} (h : SellerPayable c) :
    c.nonVacuityWitness :=
  h.right.right.right.right.right.left

theorem payable_implies_unclaimed
    {c : ProofMarketChecks} (h : SellerPayable c) :
    c.proposalHashUnclaimed :=
  h.right.right.right.right.right.right.left

theorem payable_implies_escrow_funded
    {c : ProofMarketChecks} (h : SellerPayable c) :
    c.escrowFunded :=
  h.right.right.right.right.right.right.right.right

theorem reveal_implies_payable
    {c : ProofMarketChecks} (h : FullPayloadReleasable c) :
    SellerPayable c :=
  h.left

theorem reveal_implies_payment_locked
    {c : ProofMarketChecks} (h : FullPayloadReleasable c) :
    c.paymentFinalizedOrEscrowLocked :=
  h.right.right

theorem verifier_rejection_blocks_payment
    {c : ProofMarketChecks} (hReject : ¬ c.verifierAccepts) :
    ¬ SellerPayable c := by
  intro hPay
  exact hReject (payable_implies_verifier_accepts hPay)

theorem vacuity_blocks_payment
    {c : ProofMarketChecks} (hVacuous : ¬ c.nonVacuityWitness) :
    ¬ SellerPayable c := by
  intro hPay
  exact hVacuous (payable_implies_non_vacuous hPay)

theorem duplicate_proposal_blocks_payment
    {c : ProofMarketChecks} (hDuplicate : ¬ c.proposalHashUnclaimed) :
    ¬ SellerPayable c := by
  intro hPay
  exact hDuplicate (payable_implies_unclaimed hPay)

theorem reputation_cannot_substitute_for_verifier
    {c : ProofMarketChecks} (sellerReputationMeetsThreshold : Prop)
    (hReject : ¬ c.verifierAccepts) :
    sellerReputationMeetsThreshold → ¬ SellerPayable c := by
  intro _hRep
  exact verifier_rejection_blocks_payment hReject

end ProofMarketSafety
end Proofs
