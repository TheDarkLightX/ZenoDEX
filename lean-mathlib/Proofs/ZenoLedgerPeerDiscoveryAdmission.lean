/-!
ZenoLedger peer-discovery admission boundary.

The runtime public network config derives a canonical peer registry from the
configured writer and peer URLs. This model captures the narrow admission fact:
an accepted registry has at least one writer, the peer registry hash matches the
derived entries, the admission hash matches the registry, and the registry was
derived from the same URL set carried by the public config.
-/

namespace Proofs.ZenoLedgerPeerDiscoveryAdmission

structure PeerDiscoveryAdmission where
  hasWriter : Bool
  urlsCanonical : Bool
  registryDerivedFromConfigUrls : Bool
  peerRegistryHashMatches : Bool
  admissionHashMatches : Bool
deriving DecidableEq, Repr

def Safe (a : PeerDiscoveryAdmission) : Prop :=
  a.hasWriter = true ∧
  a.urlsCanonical = true ∧
  a.registryDerivedFromConfigUrls = true ∧
  a.peerRegistryHashMatches = true ∧
  a.admissionHashMatches = true

def Admitted (a : PeerDiscoveryAdmission) : Prop :=
  Safe a

theorem admitted_safe
    (a : PeerDiscoveryAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_derived_from_config_urls
    (a : PeerDiscoveryAdmission)
    (hadmit : Admitted a) :
    a.registryDerivedFromConfigUrls = true := by
  exact (admitted_safe a hadmit).2.2.1

theorem admitted_has_writer
    (a : PeerDiscoveryAdmission)
    (hadmit : Admitted a) :
    a.hasWriter = true := by
  exact (admitted_safe a hadmit).1

theorem rejects_config_url_mismatch
    (a : PeerDiscoveryAdmission)
    (hmismatch : a.registryDerivedFromConfigUrls = false) :
    ¬ Admitted a := by
  intro hadmit
  have hderived := admitted_derived_from_config_urls a hadmit
  rw [hmismatch] at hderived
  cases hderived

theorem rejects_missing_writer
    (a : PeerDiscoveryAdmission)
    (hwriter : a.hasWriter = false) :
    ¬ Admitted a := by
  intro hadmit
  have hhas := admitted_has_writer a hadmit
  rw [hwriter] at hhas
  cases hhas

theorem admits_safe_registry
    (a : PeerDiscoveryAdmission)
    (hwriter : a.hasWriter = true)
    (hurls : a.urlsCanonical = true)
    (hderived : a.registryDerivedFromConfigUrls = true)
    (hregistry : a.peerRegistryHashMatches = true)
    (hadmission : a.admissionHashMatches = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨hwriter, hurls, hderived, hregistry, hadmission⟩

end Proofs.ZenoLedgerPeerDiscoveryAdmission
