/-!
# ZenoDEX Exact-In Route True-Key Interpretation Packet

Deterministic shell for the witness-preserving exact-in packet layered on top of
the rank-projection packet and exact-in certificate.

This file proves only the packet shell:

- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the packet carries the exact conjunction required by the
  current runtime interpretation boundary,
- the verifying packet is unique for fixed inputs.

It does **not** prove full routing arithmetic or candidate generation semantics.
It packages the replayable shell around the concrete true-key witness surface.
-/

namespace TauSwap
namespace Routing
namespace ExactInRouteTrueKeyInterpretationPacket

structure Inputs where
  rankProjectionPacketOk : Bool
  winnerIndexInRange : Bool
  candidateIndicesMatchStream : Bool
  candidateRouteKeysMatchQuotes : Bool
  winnerMatchesCertificateCandidate : Bool
  winnerTrueKeyMinimal : Bool
deriving DecidableEq, Repr

structure Packet where
  rankProjectionPacketOk : Bool
  winnerIndexInRange : Bool
  candidateIndicesMatchStream : Bool
  candidateRouteKeysMatchQuotes : Bool
  winnerMatchesCertificateCandidate : Bool
  winnerTrueKeyMinimal : Bool
  packetOk : Bool
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    rankProjectionPacketOk := inputs.rankProjectionPacketOk
    winnerIndexInRange := inputs.winnerIndexInRange
    candidateIndicesMatchStream := inputs.candidateIndicesMatchStream
    candidateRouteKeysMatchQuotes := inputs.candidateRouteKeysMatchQuotes
    winnerMatchesCertificateCandidate := inputs.winnerMatchesCertificateCandidate
    winnerTrueKeyMinimal := inputs.winnerTrueKeyMinimal
    packetOk :=
      inputs.rankProjectionPacketOk &&
      inputs.winnerIndexInRange &&
      inputs.candidateIndicesMatchStream &&
      inputs.candidateRouteKeysMatchQuotes &&
      inputs.winnerMatchesCertificateCandidate &&
      inputs.winnerTrueKeyMinimal
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
      inputs.rankProjectionPacketOk = true ∧
      inputs.winnerIndexInRange = true ∧
      inputs.candidateIndicesMatchStream = true ∧
      inputs.candidateRouteKeysMatchQuotes = true ∧
      inputs.winnerMatchesCertificateCandidate = true ∧
      inputs.winnerTrueKeyMinimal = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem packetOk_implies_winnerTrueKeyMinimal
    (inputs : Inputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    (buildPacket inputs).winnerTrueKeyMinimal = true := by
  exact (packetOk_iff inputs).1 hOk |>.2.2.2.2.2

end ExactInRouteTrueKeyInterpretationPacket
end Routing
end TauSwap
