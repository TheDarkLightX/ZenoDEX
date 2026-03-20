import Proofs.ZenoDEXExactInRouteOracleContract

/-!
# ZenoDEX Exact-In Route Guarded Quote Packet

This file formalizes the deterministic shell around the guarded exact-in
quote packet used by the integration/API boundary.

It proves:

- the packet is a deterministic rebuild from the exact-in oracle inputs,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `guardOk = true` iff the runtime choice equals the canonical winner,
- `quote.isSome = true` iff the guard succeeds,
- the verifying packet is unique for fixed inputs.

This proof does **not** claim end-to-end equivalence between the Python route
search and the abstract candidate model. It only proves the shell that either
returns the runtime quote or returns a replayable mismatch packet.
-/

namespace TauSwap
namespace Routing
namespace ExactInRouteGuardedQuotePacket

open ExactInRouteOracleContract

abbrev Inputs := ExactInRouteOracleContract.Inputs
abbrev Candidate := ExactInRouteCertificate.Candidate

inductive GuardError where
  | runtimeNotCanonical
  deriving DecidableEq, Repr

structure Packet where
  guardOk : Bool
  quote : Option Candidate
  error : Option GuardError
  contract : Contract
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  let contract := buildContract inputs
  if contract.runtimeMatchesCanonical = true then
    {
      guardOk := true
      quote := some contract.runtimeChoice
      error := none
      contract := contract
    }
  else
    {
      guardOk := false
      quote := none
      error := some GuardError.runtimeNotCanonical
      contract := contract
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

theorem guardOk_iff
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = true ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · simp [buildPacket, h]
    simpa [runtimeMatchesCanonical_iff] using h
  · constructor
    · intro hTrue
      have : False := by
        simp [buildPacket, h] at hTrue
      exact False.elim this
    · intro hCanon
      have hContr : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hCanon
      exact False.elim (h hContr)

theorem guardFails_iff
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = false ↔
      inputs.runtimeChoice ≠ canonicalWinner inputs := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs := by
      simpa [runtimeMatchesCanonical_iff] using h
    simp [buildPacket, h, hEq]
  · have hNe : inputs.runtimeChoice ≠ canonicalWinner inputs := by
      intro hEq
      have hTrue : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hEq
      contradiction
    simp [buildPacket, h, hNe]

theorem quote_isSome_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote.isSome = true ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · simp [buildPacket, h]
    simpa [runtimeMatchesCanonical_iff] using h
  · constructor
    · intro hSome
      have hContr : (buildContract inputs).runtimeMatchesCanonical = true := by
        simp [buildPacket, h] at hSome
      exact False.elim (h hContr)
    · intro hCanon
      have hContr : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hCanon
      exact False.elim (h hContr)

theorem mismatch_error_iff
    (inputs : Inputs) :
    (buildPacket inputs).error = some GuardError.runtimeNotCanonical ↔
      inputs.runtimeChoice ≠ canonicalWinner inputs := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs := by
      simpa [runtimeMatchesCanonical_iff] using h
    simp [buildPacket, h, hEq]
  · have hNe : inputs.runtimeChoice ≠ canonicalWinner inputs := by
      intro hEq
      have hTrue : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hEq
      contradiction
    simp [buildPacket, h, hNe]

end ExactInRouteGuardedQuotePacket
end Routing
end TauSwap
