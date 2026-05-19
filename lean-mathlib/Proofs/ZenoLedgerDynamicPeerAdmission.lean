/-!
ZenoLedger dynamic peer admission boundary.

Dynamic peer exchange is useful only when it remains locally checked and bounded.
The runtime admission path is opt-in. Candidate URLs are accepted into the local
peer set only after canonical URL validation, network/chain matching, a passing
local peer-status check, and a configured peer-count cap.
-/

namespace Proofs.ZenoLedgerDynamicPeerAdmission

structure DynamicPeerAdmission where
  routeEnabled : Bool
  candidateHashMatches : Bool
  urlsCanonical : Bool
  networkMatches : Bool
  chainMatches : Bool
  localPeerCheckPassed : Bool
  peerCheckUrlsMatchCandidate : Bool
  finalPeerCountWithinCap : Bool
deriving DecidableEq, Repr

def Safe (a : DynamicPeerAdmission) : Prop :=
  a.routeEnabled = true ∧
  a.candidateHashMatches = true ∧
  a.urlsCanonical = true ∧
  a.networkMatches = true ∧
  a.chainMatches = true ∧
  a.localPeerCheckPassed = true ∧
  a.peerCheckUrlsMatchCandidate = true ∧
  a.finalPeerCountWithinCap = true

def Admitted (a : DynamicPeerAdmission) : Prop :=
  Safe a

theorem admitted_safe
    (a : DynamicPeerAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_peer_check_passed
    (a : DynamicPeerAdmission)
    (hadmit : Admitted a) :
    a.localPeerCheckPassed = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.1

theorem admitted_final_peer_count_within_cap
    (a : DynamicPeerAdmission)
    (hadmit : Admitted a) :
    a.finalPeerCountWithinCap = true := by
  exact (admitted_safe a hadmit).2.2.2.2.2.2.2

theorem rejects_disabled_route
    (a : DynamicPeerAdmission)
    (hdisabled : a.routeEnabled = false) :
    ¬ Admitted a := by
  intro hadmit
  have henabled := (admitted_safe a hadmit).1
  rw [hdisabled] at henabled
  cases henabled

theorem rejects_failed_peer_check
    (a : DynamicPeerAdmission)
    (hfailed : a.localPeerCheckPassed = false) :
    ¬ Admitted a := by
  intro hadmit
  have hpassed := admitted_peer_check_passed a hadmit
  rw [hfailed] at hpassed
  cases hpassed

theorem rejects_cap_overflow
    (a : DynamicPeerAdmission)
    (hoverflow : a.finalPeerCountWithinCap = false) :
    ¬ Admitted a := by
  intro hadmit
  have hcap := admitted_final_peer_count_within_cap a hadmit
  rw [hoverflow] at hcap
  cases hcap

theorem admits_safe_dynamic_peer_candidate
    (a : DynamicPeerAdmission)
    (henabled : a.routeEnabled = true)
    (hhash : a.candidateHashMatches = true)
    (hurls : a.urlsCanonical = true)
    (hnetwork : a.networkMatches = true)
    (hchain : a.chainMatches = true)
    (hpeerCheck : a.localPeerCheckPassed = true)
    (hpeerUrls : a.peerCheckUrlsMatchCandidate = true)
    (hcap : a.finalPeerCountWithinCap = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨henabled, hhash, hurls, hnetwork, hchain, hpeerCheck, hpeerUrls, hcap⟩

end Proofs.ZenoLedgerDynamicPeerAdmission
