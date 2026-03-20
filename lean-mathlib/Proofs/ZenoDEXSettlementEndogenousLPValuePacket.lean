/-!
# ZenoDEX Settlement Endogenous LP Value Packet

Deterministic shell for the replayable endogenous LP settlement value packet.

It proves:
- verifier success is equality with the canonical rebuilt packet
- `packetOk` is exactly the conjunction of the declared boolean gate
-/

namespace TauSwap
namespace SettlementEndogenousLPValuePacket

structure Inputs where
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  uniquePoolIdsOk : Bool
  allPositiveLpSupplyOk : Bool
  allAssetsPricedOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  attestationMode : Bool
  priceProvenanceOk : Bool
  attestationOk : Bool
  uniquePoolIdsOk : Bool
  allPositiveLpSupplyOk : Bool
  allAssetsPricedOk : Bool
  assetConservationOk : Bool
  lpLiabilityBalancedOk : Bool
  valueConservationOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    attestationMode := inputs.attestationMode
    priceProvenanceOk := inputs.priceProvenanceOk
    attestationOk := inputs.attestationOk
    uniquePoolIdsOk := inputs.uniquePoolIdsOk
    allPositiveLpSupplyOk := inputs.allPositiveLpSupplyOk
    allAssetsPricedOk := inputs.allAssetsPricedOk
    assetConservationOk := inputs.assetConservationOk
    lpLiabilityBalancedOk := inputs.lpLiabilityBalancedOk
    valueConservationOk := inputs.valueConservationOk
    packetOk :=
      inputs.priceProvenanceOk &&
      inputs.uniquePoolIdsOk &&
      inputs.allPositiveLpSupplyOk &&
      inputs.allAssetsPricedOk &&
      inputs.assetConservationOk &&
      inputs.lpLiabilityBalancedOk &&
      inputs.valueConservationOk &&
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
      inputs.uniquePoolIdsOk = true ∧
      inputs.allPositiveLpSupplyOk = true ∧
      inputs.allAssetsPricedOk = true ∧
      inputs.assetConservationOk = true ∧
      inputs.lpLiabilityBalancedOk = true ∧
      inputs.valueConservationOk = true ∧
      (inputs.attestationMode = false ∨ inputs.attestationOk = true) := by
  cases inputs with
  | mk attestationMode priceProvenanceOk attestationOk uniquePoolIdsOk allPositiveLpSupplyOk allAssetsPricedOk assetConservationOk lpLiabilityBalancedOk valueConservationOk =>
      cases attestationMode <;>
        cases priceProvenanceOk <;>
        cases attestationOk <;>
        cases uniquePoolIdsOk <;>
        cases allPositiveLpSupplyOk <;>
        cases allAssetsPricedOk <;>
        cases assetConservationOk <;>
        cases lpLiabilityBalancedOk <;>
        cases valueConservationOk <;>
        decide

end SettlementEndogenousLPValuePacket
end TauSwap
