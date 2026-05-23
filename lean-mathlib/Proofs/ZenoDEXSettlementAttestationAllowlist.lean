import Proofs.ZenoDEXSettlementEndToEndCertificatePacket

/-!
# ZenoDEX Settlement Attestation Allowlist

Small formal hardening lemmas for the settlement attestation runtime gate.

The Python runtime turns signer/source allowlist failures into
`attestationOk = false`. These lemmas prove that, in attestation mode, the
end-to-end settlement certificate packet cannot be accepted when that
attestation guard is false.
-/

namespace TauSwap
namespace SettlementEndToEndCertificatePacket

theorem attestationMode_packetOk_false_of_attestation_not_ok
    (inputs : Inputs)
    (hMode : inputs.attestationMode = true)
    (hAttestation : inputs.attestationOk = false) :
    (buildPacket inputs).packetOk = false := by
  simp [buildPacket, hMode, hAttestation]

theorem accepted_attested_packet_has_attestation_ok
    (inputs : Inputs)
    (hMode : inputs.attestationMode = true)
    (hPacketOk : (buildPacket inputs).packetOk = true) :
    inputs.attestationOk = true := by
  by_cases hAttestation : inputs.attestationOk = true
  · exact hAttestation
  · have hAttestationFalse : inputs.attestationOk = false :=
      Bool.eq_false_iff.mpr hAttestation
    have hPacketFalse :
        (buildPacket inputs).packetOk = false :=
      attestationMode_packetOk_false_of_attestation_not_ok inputs hMode hAttestationFalse
    rw [hPacketFalse] at hPacketOk
    cases hPacketOk

end SettlementEndToEndCertificatePacket
end TauSwap
