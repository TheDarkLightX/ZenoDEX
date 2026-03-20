/-!
# ZenoDEX Settlement End-To-End Certificate Packet

Deterministic shell for the replayable end-to-end settlement certificate packet.

It proves:
- verifier success is equality with the canonical rebuilt packet
- `packetOk` is exactly the conjunction of the strong-certificate and value-lane
  gate bits
-/

namespace TauSwap
namespace SettlementEndToEndCertificatePacket

structure Inputs where
  attestationMode : Bool
  endogenousLpMode : Bool
  strongCertificateOk : Bool
  featureExtensionPacketOk : Bool
  moduleBundleOk : Bool
  fullPriceRailsOk : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  attestationMode : Bool
  endogenousLpMode : Bool
  strongCertificateOk : Bool
  featureExtensionPacketOk : Bool
  moduleBundleOk : Bool
  fullPriceRailsOk : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    attestationMode := inputs.attestationMode
    endogenousLpMode := inputs.endogenousLpMode
    strongCertificateOk := inputs.strongCertificateOk
    featureExtensionPacketOk := inputs.featureExtensionPacketOk
    moduleBundleOk := inputs.moduleBundleOk
    fullPriceRailsOk := inputs.fullPriceRailsOk
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.strongCertificateOk &&
      inputs.featureExtensionPacketOk &&
      inputs.moduleBundleOk &&
      inputs.fullPriceRailsOk &&
      inputs.priceProvenanceOk &&
      inputs.assetConservationOk &&
      inputs.valueConservationOk &&
      inputs.lpLiabilityBalancedOk &&
      (if inputs.attestationMode then inputs.attestationOk else true)
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

theorem verifyPacket_of_build (inputs : Inputs) :
    verifyPacket inputs (buildPacket inputs) := by
  rfl

theorem verifyingPacket_unique (inputs : Inputs) {packet : Packet}
    (hVerify : verifyPacket inputs packet) :
    packet = buildPacket inputs := by
  exact hVerify

theorem packetOk_iff (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      inputs.strongCertificateOk = true ∧
      inputs.featureExtensionPacketOk = true ∧
      inputs.moduleBundleOk = true ∧
      inputs.fullPriceRailsOk = true ∧
      inputs.priceProvenanceOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.valueConservationOk = true ∧
      inputs.lpLiabilityBalancedOk = true ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  cases inputs with
  | mk attestationMode endogenousLpMode strongCertificateOk featureExtensionPacketOk moduleBundleOk fullPriceRailsOk priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases attestationMode <;>
        cases endogenousLpMode <;>
        cases strongCertificateOk <;>
        cases featureExtensionPacketOk <;>
        cases moduleBundleOk <;>
        cases fullPriceRailsOk <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

end SettlementEndToEndCertificatePacket
end TauSwap
