/-!
ZenoLedger transport-auth admission boundary.

The runtime node can require a bearer token before serving node status, live
artifacts, peer-follow state, or testnet submission routes. This model captures
the strict admission fact used by that boundary.
-/

namespace Proofs.ZenoLedgerTransportAuthAdmission

structure TransportRequestAdmission where
  authRequired : Bool
  bearerTokenMatches : Bool
deriving DecidableEq, Repr

def Admitted (a : TransportRequestAdmission) : Prop :=
  if a.authRequired then a.bearerTokenMatches = true else True

/--
When transport auth is required, an admitted request has the matching bearer
token.
-/
theorem required_admission_token_matches
    (a : TransportRequestAdmission)
    (hrequire : a.authRequired = true)
    (hadmit : Admitted a) :
    a.bearerTokenMatches = true := by
  unfold Admitted at hadmit
  simp [hrequire] at hadmit
  exact hadmit

/--
When transport auth is required, a request with a missing or wrong bearer token
cannot be admitted.
-/
theorem required_rejects_token_mismatch
    (a : TransportRequestAdmission)
    (hrequire : a.authRequired = true)
    (hmismatch : a.bearerTokenMatches = false) :
    ¬ Admitted a := by
  intro hadmit
  have hmatches := required_admission_token_matches a hrequire hadmit
  rw [hmismatch] at hmatches
  cases hmatches

end Proofs.ZenoLedgerTransportAuthAdmission
