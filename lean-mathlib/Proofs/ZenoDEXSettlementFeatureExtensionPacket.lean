/-!
# ZenoDEX Settlement Feature Extension Packet

Deterministic shell for the replayable settlement feature-extension packet.

It proves:
- verifier success is equality with the canonical rebuilt packet
- `packetOk` is exactly the conjunction of the four feature-extension checks
-/

namespace TauSwap
namespace SettlementFeatureExtensionPacket

structure Inputs where
  buybackFloorOk : Bool
  buybackFloorFixedpointOk : Bool
  rebateOk : Bool
  lockWeightOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  buybackFloorOk : Bool
  buybackFloorFixedpointOk : Bool
  rebateOk : Bool
  lockWeightOk : Bool
  featureExtensionOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    buybackFloorOk := inputs.buybackFloorOk
    buybackFloorFixedpointOk := inputs.buybackFloorFixedpointOk
    rebateOk := inputs.rebateOk
    lockWeightOk := inputs.lockWeightOk
    featureExtensionOk :=
      inputs.buybackFloorOk &&
      inputs.buybackFloorFixedpointOk &&
      inputs.rebateOk &&
      inputs.lockWeightOk
    packetOk :=
      inputs.buybackFloorOk &&
      inputs.buybackFloorFixedpointOk &&
      inputs.rebateOk &&
      inputs.lockWeightOk
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
      inputs.buybackFloorOk = true ∧
      inputs.buybackFloorFixedpointOk = true ∧
      inputs.rebateOk = true ∧
      inputs.lockWeightOk = true := by
  cases inputs with
  | mk buybackFloorOk buybackFloorFixedpointOk rebateOk lockWeightOk =>
      cases buybackFloorOk <;>
        cases buybackFloorFixedpointOk <;>
        cases rebateOk <;>
        cases lockWeightOk <;>
        decide

end SettlementFeatureExtensionPacket
end TauSwap
