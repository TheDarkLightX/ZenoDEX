/-!
ZenoLedger public-network config admission boundary.

The runtime object is a JSON config with a hash-bound writer/peer URL list plus
optional signer-registry quorum evidence. This Lean model captures the narrow
release invariant for the strict path: when config quorum is required, admitted
configs must satisfy the hash, registry-hash, and threshold-quorum checks.
-/

namespace Proofs.ZenoLedgerPublicNetworkConfigAdmission

structure PublicNetworkConfigAdmission where
  requireConfigQuorum : Bool
  configHashMatches : Bool
  registryHashMatches : Bool
  quorumSatisfied : Bool
deriving DecidableEq, Repr

def Safe (a : PublicNetworkConfigAdmission) : Prop :=
  a.configHashMatches = true ∧
  a.registryHashMatches = true ∧
  a.quorumSatisfied = true

def Admitted (a : PublicNetworkConfigAdmission) : Prop :=
  if a.requireConfigQuorum then Safe a else True

/--
Strict public-network config admission implies all local quorum obligations.
-/
theorem required_admission_safe
    (a : PublicNetworkConfigAdmission)
    (hrequire : a.requireConfigQuorum = true)
    (hadmit : Admitted a) :
    Safe a := by
  unfold Admitted at hadmit
  simp [hrequire] at hadmit
  exact hadmit

/--
A required public-network config with a mismatched config hash cannot be
admitted.
-/
theorem required_rejects_config_hash_mismatch
    (a : PublicNetworkConfigAdmission)
    (hrequire : a.requireConfigQuorum = true)
    (hhash : a.configHashMatches = false) :
    ¬ Admitted a := by
  intro hadmit
  have hsafe := required_admission_safe a hrequire hadmit
  have hcfg := hsafe.1
  rw [hhash] at hcfg
  cases hcfg

/--
A required public-network config with the wrong signer registry hash cannot be
admitted.
-/
theorem required_rejects_registry_hash_mismatch
    (a : PublicNetworkConfigAdmission)
    (hrequire : a.requireConfigQuorum = true)
    (hregistry : a.registryHashMatches = false) :
    ¬ Admitted a := by
  intro hadmit
  have hsafe := required_admission_safe a hrequire hadmit
  have hregistry_ok := hsafe.2.1
  rw [hregistry] at hregistry_ok
  cases hregistry_ok

/--
A required public-network config without threshold signer quorum cannot be
admitted.
-/
theorem required_rejects_missing_quorum
    (a : PublicNetworkConfigAdmission)
    (hrequire : a.requireConfigQuorum = true)
    (hquorum : a.quorumSatisfied = false) :
    ¬ Admitted a := by
  intro hadmit
  have hsafe := required_admission_safe a hrequire hadmit
  have hquorum_ok := hsafe.2.2
  rw [hquorum] at hquorum_ok
  cases hquorum_ok

theorem required_admits_safe
    (a : PublicNetworkConfigAdmission)
    (hrequire : a.requireConfigQuorum = true)
    (hhash : a.configHashMatches = true)
    (hregistry : a.registryHashMatches = true)
    (hquorum : a.quorumSatisfied = true) :
    Admitted a := by
  unfold Admitted Safe
  simp [hrequire, hhash, hregistry, hquorum]

end Proofs.ZenoLedgerPublicNetworkConfigAdmission
