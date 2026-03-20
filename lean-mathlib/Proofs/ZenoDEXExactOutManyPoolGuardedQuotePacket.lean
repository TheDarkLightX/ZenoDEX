import Proofs.ZenoDEXExactOutManyPoolOracleContract

/-!
# ZenoDEX Exact-Out Many-Pool Guarded Quote Packet

This file formalizes the deterministic shell around the guarded many-pool
exact-out quote packet used by the integration/API boundary.

It proves:

- the packet is a deterministic rebuild from the many-pool oracle inputs,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `guardOk = true` iff the runtime choice equals the bounded canonical winner,
- `quote = some runtimeChoice` iff the guard succeeds,
- the verifying packet is unique for fixed inputs.

This proof does **not** claim that the runtime is already canonical. It only
proves the shell that either returns the runtime quote or returns a bounded
replayable mismatch packet.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolGuardedQuotePacket

open ExactOutManyPoolOracleContract
open ExactOutRouteCertificate

abbrev Inputs := ExactOutManyPoolOracleContract.Inputs
abbrev Candidate := ExactOutRouteCertificate.Candidate

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

theorem guardOk_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = true ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
  constructor
  · intro hGuard
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (guardOk_iff inputs).1 hGuard
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · intro x hx
      simpa [hEq] using canonicalWinner_keyLe_all inputs hx
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2
    exact (guardOk_iff inputs).2 hEq

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

theorem guardFails_iff_not_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = false ↔
      ¬ (inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
          ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) := by
  constructor
  · intro hFail hMin
    have hOk : (buildPacket inputs).guardOk = true :=
      (guardOk_iff_mem_and_keyLe_all inputs).2 hMin
    have : false = true := hFail.symm.trans hOk
    exact False.elim (Bool.false_ne_true this)
  · intro hNotMin
    by_cases hOk : (buildPacket inputs).guardOk = true
    · have hMin :
          inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
            ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x :=
        (guardOk_iff_mem_and_keyLe_all inputs).1 hOk
      exact False.elim (hNotMin hMin)
    · cases hVal : (buildPacket inputs).guardOk <;> simp [hVal] at hOk ⊢

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

theorem quote_eq_some_runtimeChoice_iff_guardOk
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      (buildPacket inputs).guardOk = true := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · have hPacket :
        buildPacket inputs =
          {
            guardOk := true
            quote := some (buildContract inputs).runtimeChoice
            error := none
            contract := buildContract inputs
          } := by
        simp [buildPacket, h]
    simp [hPacket, buildContract]
  · have hFalse : (buildContract inputs).runtimeMatchesCanonical = false := by
      cases hVal : (buildContract inputs).runtimeMatchesCanonical <;> simp [hVal] at h ⊢
    have hPacket :
        buildPacket inputs =
          {
            guardOk := false
            quote := none
            error := some GuardError.runtimeNotCanonical
            contract := buildContract inputs
          } := by
        simp [buildPacket, hFalse]
    simp [hPacket]

theorem quote_eq_some_runtimeChoice_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  calc
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
        (buildPacket inputs).guardOk = true :=
      quote_eq_some_runtimeChoice_iff_guardOk inputs
    _ ↔ inputs.runtimeChoice = canonicalWinner inputs :=
      guardOk_iff inputs

theorem quote_eq_some_canonicalWinner_iff_guardOk
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      (buildPacket inputs).guardOk = true := by
  by_cases h : (buildContract inputs).runtimeMatchesCanonical = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs := by
      simpa [runtimeMatchesCanonical_iff] using h
    have hBuildEq : (buildContract inputs).runtimeChoice = canonicalWinner inputs := by
      simpa [buildContract] using hEq
    simp [buildPacket, h, hBuildEq]
  · have hNe : inputs.runtimeChoice ≠ canonicalWinner inputs := by
      intro hEq
      have hContr : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hEq
      exact h hContr
    simp [buildPacket, h]

theorem quote_eq_some_canonicalWinner_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  calc
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
        (buildPacket inputs).guardOk = true :=
      quote_eq_some_canonicalWinner_iff_guardOk inputs
    _ ↔ inputs.runtimeChoice = canonicalWinner inputs :=
      guardOk_iff inputs

theorem quote_isSome_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote.isSome = true ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
  constructor
  · intro hSome
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (quote_isSome_iff inputs).1 hSome
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · intro x hx
      simpa [hEq] using canonicalWinner_keyLe_all inputs hx
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2
    exact (quote_isSome_iff inputs).2 hEq

theorem quote_eq_some_runtimeChoice_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
  constructor
  · intro hQuote
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (quote_eq_some_runtimeChoice_iff inputs).1 hQuote
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · intro x hx
      simpa [hEq] using canonicalWinner_keyLe_all inputs hx
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2
    exact (quote_eq_some_runtimeChoice_iff inputs).2 hEq

theorem quote_eq_some_canonicalWinner_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
  calc
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
        inputs.runtimeChoice = canonicalWinner inputs :=
      quote_eq_some_canonicalWinner_iff inputs
    _ ↔
        inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
          ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
      constructor
      · intro hEq
        constructor
        · simpa [hEq] using canonicalWinner_mem inputs
        · intro x hx
          simpa [hEq] using canonicalWinner_keyLe_all inputs hx
      · intro hMin
        exact canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2

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

end ExactOutManyPoolGuardedQuotePacket
end Routing
end TauSwap
