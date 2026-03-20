/-!
# ZenoDEX Exact-In Route Rank Projection Packet

Deterministic shell for the explicit exact-in route-key projection packet.

This file proves only the packet shell:

- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the packet carries the exact conjunction of the
  declared ordered-key and rank-projection facts,
- the verifying packet is unique for fixed inputs.

It does **not** prove the full Python route-key semantics. It makes the
projection boundary explicit and replayable so the remaining semantic bridge is
smaller than "the whole certificate stack".
-/

namespace TauSwap
namespace Routing
namespace ExactInRouteRankProjectionPacket

structure Inputs where
  orderedUniqueKeysSortedUnique : Bool
  candidateRanksMatchProjection : Bool
  rankOrderPreservesTrueKeyOrder : Bool
deriving DecidableEq, Repr

structure Packet where
  orderedUniqueKeysSortedUnique : Bool
  candidateRanksMatchProjection : Bool
  rankOrderPreservesTrueKeyOrder : Bool
  packetOk : Bool
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    orderedUniqueKeysSortedUnique := inputs.orderedUniqueKeysSortedUnique
    candidateRanksMatchProjection := inputs.candidateRanksMatchProjection
    rankOrderPreservesTrueKeyOrder := inputs.rankOrderPreservesTrueKeyOrder
    packetOk :=
      inputs.orderedUniqueKeysSortedUnique &&
      inputs.candidateRanksMatchProjection &&
      inputs.rankOrderPreservesTrueKeyOrder
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
      inputs.orderedUniqueKeysSortedUnique = true ∧
      inputs.candidateRanksMatchProjection = true ∧
      inputs.rankOrderPreservesTrueKeyOrder = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem packetOk_iff_fields_true
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      (buildPacket inputs).orderedUniqueKeysSortedUnique = true ∧
      (buildPacket inputs).candidateRanksMatchProjection = true ∧
      (buildPacket inputs).rankOrderPreservesTrueKeyOrder = true := by
  simp [buildPacket, Bool.and_eq_true, and_assoc]

theorem packetOk_implies_rankOrderPreservesTrueKeyOrder
    (inputs : Inputs)
    (hOk : (buildPacket inputs).packetOk = true) :
    (buildPacket inputs).rankOrderPreservesTrueKeyOrder = true := by
  exact (packetOk_iff_fields_true inputs).1 hOk |>.2.2

end ExactInRouteRankProjectionPacket
end Routing
end TauSwap
