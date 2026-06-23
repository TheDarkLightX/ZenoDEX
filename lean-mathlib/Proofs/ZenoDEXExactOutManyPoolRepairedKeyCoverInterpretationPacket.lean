/-!
# ZenoDEX Exact-Out Many-Pool Repaired Key-Cover Interpretation Packet

Deterministic shell for the witness-interpretation packet layered on top of the
repaired key-cover packet.

This file proves only the packet shell:

- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the packet carries the exact conjunction required by the
  current runtime interpretation boundary,
- the verifying packet is unique for fixed inputs.

It does **not** prove that these booleans already constitute a semantic proof of
`KeyCover`; it only packages the replayable shell around the interpretation
artifact.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedKeyCoverInterpretationPacket

structure Inputs where
  keyCoverPacketOk : Bool
  selectedWinnerIndexInRange : Bool
  selectedWinnerMatchesCertificate : Bool
  selectedWinnerKeyMinimal : Bool
  dominationWitnessIndicesInRange : Bool
  dominationWitnessesCoverFullCandidates : Bool
  dominationWitnessKeysMatchCandidates : Bool
  dominationWitnessesDominate : Bool
deriving DecidableEq, Repr

structure Packet where
  keyCoverPacketOk : Bool
  selectedWinnerIndexInRange : Bool
  selectedWinnerMatchesCertificate : Bool
  selectedWinnerKeyMinimal : Bool
  dominationWitnessIndicesInRange : Bool
  dominationWitnessesCoverFullCandidates : Bool
  dominationWitnessKeysMatchCandidates : Bool
  dominationWitnessesDominate : Bool
  packetOk : Bool
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    keyCoverPacketOk := inputs.keyCoverPacketOk
    selectedWinnerIndexInRange := inputs.selectedWinnerIndexInRange
    selectedWinnerMatchesCertificate := inputs.selectedWinnerMatchesCertificate
    selectedWinnerKeyMinimal := inputs.selectedWinnerKeyMinimal
    dominationWitnessIndicesInRange := inputs.dominationWitnessIndicesInRange
    dominationWitnessesCoverFullCandidates := inputs.dominationWitnessesCoverFullCandidates
    dominationWitnessKeysMatchCandidates := inputs.dominationWitnessKeysMatchCandidates
    dominationWitnessesDominate := inputs.dominationWitnessesDominate
    packetOk :=
      inputs.keyCoverPacketOk &&
      inputs.selectedWinnerIndexInRange &&
      inputs.selectedWinnerMatchesCertificate &&
      inputs.selectedWinnerKeyMinimal &&
      inputs.dominationWitnessIndicesInRange &&
      inputs.dominationWitnessesCoverFullCandidates &&
      inputs.dominationWitnessKeysMatchCandidates &&
      inputs.dominationWitnessesDominate
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
      inputs.keyCoverPacketOk = true ∧
      inputs.selectedWinnerIndexInRange = true ∧
      inputs.selectedWinnerMatchesCertificate = true ∧
      inputs.selectedWinnerKeyMinimal = true ∧
      inputs.dominationWitnessIndicesInRange = true ∧
      inputs.dominationWitnessesCoverFullCandidates = true ∧
      inputs.dominationWitnessKeysMatchCandidates = true ∧
      inputs.dominationWitnessesDominate = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem packetOk_iff_fields_true
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      (buildPacket inputs).keyCoverPacketOk = true ∧
      (buildPacket inputs).selectedWinnerIndexInRange = true ∧
      (buildPacket inputs).selectedWinnerMatchesCertificate = true ∧
      (buildPacket inputs).selectedWinnerKeyMinimal = true ∧
      (buildPacket inputs).dominationWitnessIndicesInRange = true ∧
      (buildPacket inputs).dominationWitnessesCoverFullCandidates = true ∧
      (buildPacket inputs).dominationWitnessKeysMatchCandidates = true ∧
      (buildPacket inputs).dominationWitnessesDominate = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

end ExactOutManyPoolRepairedKeyCoverInterpretationPacket
end Routing
end TauSwap
