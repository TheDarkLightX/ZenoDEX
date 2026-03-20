import Proofs.ZenoDEXExactOutManyPoolKeyCoverBridge

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Key-Cover Packet

Deterministic shell for the witness-preserving repaired key-cover packet on the
many-pool exact-out advisory lane.

This file proves only the packet shell:

- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the packet carries the exact conjunction required by the
  current runtime boundary,
- the verifying packet is unique for fixed inputs.

It does **not** prove that the runtime witness data really satisfies the
semantic `KeyCover` theorem. It only proves the replayable shell around the
packet that preserves those witness surfaces.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedKeyCoverPacket

structure Inputs where
  selectedDomainContractOk : Bool
  repairedFullDomainPacketOk : Bool
  selectedKeysSubsetFullKeys : Bool
  keyCoverHolds : Bool
  selectedDomainCanonicalMatchesFullDomainCanonical : Bool
deriving DecidableEq, Repr

structure Packet where
  selectedDomainContractOk : Bool
  repairedFullDomainPacketOk : Bool
  selectedKeysSubsetFullKeys : Bool
  keyCoverHolds : Bool
  selectedDomainCanonicalMatchesFullDomainCanonical : Bool
  packetOk : Bool
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    selectedDomainContractOk := inputs.selectedDomainContractOk
    repairedFullDomainPacketOk := inputs.repairedFullDomainPacketOk
    selectedKeysSubsetFullKeys := inputs.selectedKeysSubsetFullKeys
    keyCoverHolds := inputs.keyCoverHolds
    selectedDomainCanonicalMatchesFullDomainCanonical :=
      inputs.selectedDomainCanonicalMatchesFullDomainCanonical
    packetOk :=
      inputs.selectedDomainContractOk &&
      inputs.repairedFullDomainPacketOk &&
      inputs.selectedKeysSubsetFullKeys &&
      inputs.keyCoverHolds &&
      inputs.selectedDomainCanonicalMatchesFullDomainCanonical
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

theorem verifyPacket_iff
    (inputs : Inputs)
    (packet : Packet) :
    verifyPacket inputs packet ↔
      packet = buildPacket inputs := by
  rfl

theorem verifyPacket_of_build
    (inputs : Inputs) :
    verifyPacket inputs (buildPacket inputs) := by
  rfl

theorem verifyingPacket_unique
    (inputs : Inputs)
    {packet : Packet}
    (hVerify : verifyPacket inputs packet) :
    packet = buildPacket inputs := by
  exact hVerify

theorem packetOk_iff
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      inputs.selectedDomainContractOk = true ∧
      inputs.repairedFullDomainPacketOk = true ∧
      inputs.selectedKeysSubsetFullKeys = true ∧
      inputs.keyCoverHolds = true ∧
      inputs.selectedDomainCanonicalMatchesFullDomainCanonical = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem packetOk_iff_fields_true
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      (buildPacket inputs).selectedDomainContractOk = true ∧
      (buildPacket inputs).repairedFullDomainPacketOk = true ∧
      (buildPacket inputs).selectedKeysSubsetFullKeys = true ∧
      (buildPacket inputs).keyCoverHolds = true ∧
      (buildPacket inputs).selectedDomainCanonicalMatchesFullDomainCanonical = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

end ExactOutManyPoolRepairedKeyCoverPacket
end Routing
end TauSwap
