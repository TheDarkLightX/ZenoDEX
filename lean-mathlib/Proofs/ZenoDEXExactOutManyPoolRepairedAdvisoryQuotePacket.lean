import Proofs.ZenoDEXExactOutManyPoolRepairedPrefilterContract

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Advisory Quote Packet

This file formalizes the deterministic shell around the repaired many-pool
exact-out advisory quote packet used at the integration/API boundary.

It proves:

- the packet is a deterministic rebuild from the repaired-prefilter contract
  status and the advisory/runtime equality bit,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `packetOk = true` iff the repaired-prefilter contract is OK,
- `advisoryQuote` is present iff the repaired-prefilter contract is OK,
- the verifying packet is unique for fixed inputs.

This proof does **not** claim runtime adoption or repaired-prefilter
completeness. It only proves the replayable shell around the advisory packet.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedAdvisoryQuotePacket

inductive AdvisoryError where
  | repairedPrefilterContractNotOk
deriving DecidableEq, Repr

structure Inputs where
  repairedContractOk : Bool
  runtimeMatchesAdvisory : Bool
deriving DecidableEq, Repr

structure Packet where
  packetOk : Bool
  advisoryQuotePresent : Bool
  runtimeMatchesAdvisory : Bool
  error : Option AdvisoryError
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  if inputs.repairedContractOk = true then
    {
      packetOk := true
      advisoryQuotePresent := true
      runtimeMatchesAdvisory := inputs.runtimeMatchesAdvisory
      error := none
    }
  else
    {
      packetOk := false
      advisoryQuotePresent := false
      runtimeMatchesAdvisory := false
      error := some AdvisoryError.repairedPrefilterContractNotOk
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
      inputs.repairedContractOk = true := by
  by_cases h : inputs.repairedContractOk = true
  · simp [buildPacket, h]
  · constructor
    · intro hOk
      have : False := by
        simp [buildPacket, h] at hOk
      exact False.elim this
    · intro hTrue
      exact False.elim (h hTrue)

theorem advisoryQuotePresent_iff
    (inputs : Inputs) :
    (buildPacket inputs).advisoryQuotePresent = true ↔
      inputs.repairedContractOk = true := by
  by_cases h : inputs.repairedContractOk = true
  · simp [buildPacket, h]
  · constructor
    · intro hOk
      have : False := by
        simp [buildPacket, h] at hOk
      exact False.elim this
    · intro hTrue
      exact False.elim (h hTrue)

theorem runtimeMatchesAdvisory_iff_packetOk
    (inputs : Inputs) :
    (buildPacket inputs).packetOk = true →
      (buildPacket inputs).runtimeMatchesAdvisory = inputs.runtimeMatchesAdvisory := by
  intro hOk
  have hContract : inputs.repairedContractOk = true :=
    (packetOk_iff inputs).1 hOk
  simp [buildPacket, hContract]

theorem errorPresent_iff_not_packetOk
    (inputs : Inputs) :
    (buildPacket inputs).error.isSome = true ↔
      (buildPacket inputs).packetOk = false := by
  by_cases h : inputs.repairedContractOk = true
  · simp [buildPacket, h]
  · have hFalse : inputs.repairedContractOk = false := by
      cases hVal : inputs.repairedContractOk <;> simp [hVal] at h ⊢
    simp [buildPacket, hFalse]

end ExactOutManyPoolRepairedAdvisoryQuotePacket
end Routing
end TauSwap
