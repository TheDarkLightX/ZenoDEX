/-!
# ZenoDEX Settlement Value Packet

This file formalizes the deterministic shell around the replayable settlement
value packet used by the integration/API boundary.

It proves:

- the packet is a deterministic rebuild from the boolean acceptance surface,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk` is exactly the conjunction of provenance, attestation, asset,
  LP-liability, and value conditions under the selected mode.
-/

namespace TauSwap
namespace SettlementValuePacket

structure Inputs where
  lpMode : Bool
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  lpMode : Bool
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    lpMode := inputs.lpMode
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.priceProvenanceOk &&
      inputs.assetConservationOk &&
      inputs.valueConservationOk &&
      (if inputs.lpMode then inputs.lpLiabilityBalancedOk else true) &&
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
      inputs.priceProvenanceOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.valueConservationOk = true ∧
      (inputs.lpMode = false ∨ inputs.lpLiabilityBalancedOk = true) ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  cases inputs with
  | mk lpMode attestationMode priceProvenanceOk attestationOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases lpMode <;>
        cases attestationMode <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

end SettlementValuePacket
end TauSwap
