import Proofs.ZenoDEXExactOutManyPoolRepairedAdvisoryQuotePacket

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Full-Domain Certified Packet

Deterministic shell for the advisory packet that certifies the repaired many-pool
exact-out quote against the full bounded feasible-domain canonical winner.

This file proves only the packet shell:

- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the repaired advisory packet is OK and the repaired quote
  equals the full bounded canonical winner,
- the verifying packet is unique for fixed inputs.

It does **not** prove the semantics of the repaired prefilter or global
generator completeness.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedFullDomainCertifiedPacket

structure Inputs where
  repairedPacketOk : Bool
  repairedMatchesFullCanonical : Bool
deriving DecidableEq, Repr

structure Packet where
  repairedPacketOk : Bool
  repairedMatchesFullCanonical : Bool
  packetOk : Bool
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    repairedPacketOk := inputs.repairedPacketOk
    repairedMatchesFullCanonical := inputs.repairedMatchesFullCanonical
    packetOk := inputs.repairedPacketOk && inputs.repairedMatchesFullCanonical
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
      inputs.repairedPacketOk = true ∧
      inputs.repairedMatchesFullCanonical = true := by
  simp [buildPacket, Bool.and_eq_true]

theorem packetOk_iff_repairedPacketOk_and_repairedMatchesFullCanonical
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      (buildPacket inputs).repairedPacketOk = true ∧
      (buildPacket inputs).repairedMatchesFullCanonical = true := by
  simp [buildPacket, Bool.and_eq_true]

end ExactOutManyPoolRepairedFullDomainCertifiedPacket
end Routing
end TauSwap
