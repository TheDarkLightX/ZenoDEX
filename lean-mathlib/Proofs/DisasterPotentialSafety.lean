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

/-! ## Bounded recovery under strict descent

`SafeTransition` permits indefinite dwell at high risk: a trajectory may sit
at `postRisk = preRisk` above any danger threshold forever without ever
needing a recovery certificate.  The lemmas below upgrade the guard shape:
if the controller enforces STRICT descent while above a threshold `θ` (each
accepted step strictly reduces the ℕ-valued risk whenever risk exceeds `θ`),
then any trajectory provably re-enters the `≤ θ` zone within
`initial risk − θ` steps (`strict_descent_reaches_threshold`).

This converts "disaster potential never worsens" into "disaster dwell time is
bounded by the initial excess" — a quantitatively stronger containment claim
with the same fail-closed shape.  Each strict step still satisfies
`SafeTransition` (`strict_descent_step_is_safe`), so the upgrade refines the
existing guard rather than replacing it.
-/

/-- A risk trajectory (list of consecutive risk readings) descends strictly
    while above the threshold `θ`: at every adjacent pair, if the earlier
    reading exceeds `θ`, the later reading is strictly smaller. -/
def StrictDescentAbove (θ : ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (θ < a → b < a) ∧ StrictDescentAbove θ (b :: rest)

/-- A strict-descent step is in particular a `SafeTransition` (no recovery
    certificate needed): strict decrease implies non-increase. -/
theorem strict_descent_step_is_safe
    {θ preRisk postRisk : ℕ} (recoveryCertificate : Prop)
    (hstep : θ < preRisk → postRisk < preRisk)
    (hcase : θ < preRisk ∨ postRisk ≤ preRisk) :
    SafeTransition preRisk postRisk recoveryCertificate := by
  rcases hcase with hhigh | hle
  · exact Or.inl (Nat.le_of_lt (hstep hhigh))
  · exact Or.inl hle

/-- **Bounded recovery.**  On a strict-descent trajectory that runs for at
    least `a − θ` further steps, some reading is `≤ θ`: the dwell time above
    the danger threshold is bounded by the initial excess.  Proof by
    induction: each step above `θ` reduces risk by at least 1. -/
theorem strict_descent_reaches_threshold (θ a : ℕ) (l : List ℕ)
    (hdesc : StrictDescentAbove θ (a :: l))
    (hlen : a - θ ≤ l.length) :
    ∃ x ∈ a :: l, x ≤ θ := by
  induction l generalizing a with
  | nil =>
      have ha_le : a ≤ θ := by
        simp only [List.length_nil, Nat.le_zero] at hlen
        omega
      exact ⟨a, by simp, ha_le⟩
  | cons b rest ih =>
      by_cases ha : a ≤ θ
      · exact ⟨a, by simp, ha⟩
      · push_neg at ha
        obtain ⟨hstep, htail⟩ := hdesc
        have hb : b < a := hstep ha
        have hlen' : b - θ ≤ rest.length := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨x, hx, hxle⟩ := ih b htail hlen'
        exact ⟨x, List.mem_cons_of_mem a hx, hxle⟩

/-- Non-vacuity: the trajectory `[5, 4, 3, 2, 9]` strictly descends above
    threshold `θ = 2` (the final pair is unconstrained because `2 ≤ θ`),
    its length budget `5 - 2 = 3 ≤ 4` is met, and it indeed reaches the
    threshold zone. -/
theorem witness_strict_descent :
    StrictDescentAbove 2 [5, 4, 3, 2, 9] ∧ (∃ x ∈ [5, 4, 3, 2, 9], x ≤ 2) := by
  constructor
  · refine ⟨by omega, by omega, by omega, by omega, trivial⟩
  · exact ⟨2, by simp, by omega⟩

end DisasterPotentialSafety
end Proofs
