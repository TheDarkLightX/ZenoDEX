import Mathlib

/-!
# Disaster Potential Safety

Small algebraic facts for the disaster-potential chaos-morphism model.

The file proves only the generic guard shape:

* if a safe transition is defined as risk nonincrease or a recovery
  certificate, then an accepted risk-increasing transition must have the
  recovery certificate.

It does not prove that a concrete risk vector is complete or that runtime
receipts are truthful.
-/

namespace Proofs
namespace DisasterPotentialSafety

/-- A transition is accepted when risk does not increase, or when the transition
carries the required recovery certificate. -/
def SafeTransition (preRisk postRisk : ℕ) (recoveryCertificate : Prop) : Prop :=
  postRisk ≤ preRisk ∨ recoveryCertificate

/-- If a transition accepted by `SafeTransition` strictly increases risk, it must
have been accepted through the recovery-certificate branch. -/
theorem risk_increase_requires_recovery_certificate
    {preRisk postRisk : ℕ} {recoveryCertificate : Prop}
    (hok : SafeTransition preRisk postRisk recoveryCertificate)
    (hincrease : preRisk < postRisk) :
    recoveryCertificate := by
  rcases hok with hnonincrease | hcert
  · omega
  · exact hcert

/-- A certified recovery that is required to stay under a cap indeed has
post-transition risk bounded by that cap. -/
theorem certified_recovery_post_risk_le_cap
    {postRisk recoveryCap : ℕ}
    (_recoveryCertificate : Prop)
    (hcap : postRisk ≤ recoveryCap) :
    postRisk ≤ recoveryCap := hcap

end DisasterPotentialSafety
end Proofs
