import Proofs.ZenoDEXExactOutManyPoolOracleContract

/-!
# ZenoDEX Exact-Out Many-Pool Guarded Quote Packet

This file formalizes the deterministic shell around the guarded many-pool
exact-out quote packet used by the integration/API boundary.

It proves:

- the packet is a deterministic rebuild from the many-pool oracle inputs,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- `guardOk = true` iff the runtime choice equals the bounded canonical winner
  and the selected-domain projection cover is verified,
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
  | projectionCoverNotVerified
deriving DecidableEq, Repr

structure Packet where
  guardOk : Bool
  quote : Option Candidate
  error : Option GuardError
  contract : Contract
deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  let contract := buildContract inputs
  if contract.contractOk = true then
    {
      guardOk := true
      quote := some contract.runtimeChoice
      error := none
      contract := contract
    }
  else if contract.runtimeMatchesCanonical = true then
    {
      guardOk := false
      quote := none
      error := some GuardError.projectionCoverNotVerified
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
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true := by
  by_cases h : (buildContract inputs).contractOk = true
  · simp [buildPacket, h]
    exact (contractOk_iff inputs).1 h
  · constructor
    · intro hTrue
      cases hRuntime : (buildContract inputs).runtimeMatchesCanonical <;>
        simp [buildPacket, h, hRuntime] at hTrue
    · intro hContract
      have hContr : (buildContract inputs).contractOk = true :=
        (contractOk_iff inputs).2 hContract
      exact False.elim (h hContr)

theorem guardOk_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = true ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
        inputs.projectionCoverHolds = true := by
  constructor
  · intro hGuard
    rcases (guardOk_iff inputs).1 hGuard with ⟨hEq, hCover⟩
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · constructor
      · intro x hx
        simpa [hEq] using canonicalWinner_keyLe_all inputs hx
      · exact hCover
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2.1
    exact (guardOk_iff inputs).2 ⟨hEq, hMin.2.2⟩

theorem guardOk_implies_projectionCoverHolds
    (inputs : Inputs)
    (hGuard : (buildPacket inputs).guardOk = true) :
    inputs.projectionCoverHolds = true :=
  (guardOk_iff inputs).1 hGuard |>.2

theorem guardOk_implies_runtimeMatchesCanonical
    (inputs : Inputs)
    (hGuard : (buildPacket inputs).guardOk = true) :
    (buildContract inputs).runtimeMatchesCanonical = true := by
  have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (guardOk_iff inputs).1 hGuard
        |>.1
  exact (runtimeMatchesCanonical_iff inputs).2 hEq

theorem guardFails_iff
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = false ↔
      ¬ (inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true) := by
  constructor
  · intro hFail hOkInputs
    have hOk : (buildPacket inputs).guardOk = true :=
      (guardOk_iff inputs).2 hOkInputs
    have : false = true := hFail.symm.trans hOk
    exact False.elim (Bool.false_ne_true this)
  · intro hNot
    by_cases hOk : (buildPacket inputs).guardOk = true
    · exact False.elim (hNot ((guardOk_iff inputs).1 hOk))
    · cases hVal : (buildPacket inputs).guardOk <;> simp [hVal] at hOk ⊢

theorem guardFails_iff_not_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).guardOk = false ↔
      ¬ (inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
          (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
          inputs.projectionCoverHolds = true) := by
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
            (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
            inputs.projectionCoverHolds = true :=
        (guardOk_iff_mem_and_keyLe_all inputs).1 hOk
      exact False.elim (hNotMin hMin)
    · cases hVal : (buildPacket inputs).guardOk <;> simp [hVal] at hOk ⊢

theorem quote_isSome_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote.isSome = true ↔
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true := by
  by_cases h : (buildContract inputs).contractOk = true
  · simp [buildPacket, h]
    exact (contractOk_iff inputs).1 h
  · have hNot :
        ¬ (inputs.runtimeChoice = canonicalWinner inputs ∧
          inputs.projectionCoverHolds = true) := by
      intro hInputs
      exact h ((contractOk_iff inputs).2 hInputs)
    cases hRuntime : (buildContract inputs).runtimeMatchesCanonical <;>
      simp [buildPacket, h, hRuntime, hNot]

theorem quote_eq_some_runtimeChoice_iff_guardOk
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      (buildPacket inputs).guardOk = true := by
  by_cases h : (buildContract inputs).contractOk = true
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
  · cases hRuntime : (buildContract inputs).runtimeMatchesCanonical <;>
      simp [buildPacket, h, hRuntime]

theorem quote_eq_some_runtimeChoice_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true := by
  calc
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
        (buildPacket inputs).guardOk = true :=
      quote_eq_some_runtimeChoice_iff_guardOk inputs
    _ ↔ inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true :=
      guardOk_iff inputs

theorem quote_eq_some_canonicalWinner_iff_guardOk
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      (buildPacket inputs).guardOk = true := by
  by_cases h : (buildContract inputs).contractOk = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (contractOk_iff inputs).1 h |>.1
    have hBuildEq : (buildContract inputs).runtimeChoice = canonicalWinner inputs := by
      simpa [buildContract] using hEq
    simp [buildPacket, h, hBuildEq]
  · cases hRuntime : (buildContract inputs).runtimeMatchesCanonical <;>
      simp [buildPacket, h, hRuntime]

theorem quote_eq_some_canonicalWinner_iff
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true := by
  calc
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
        (buildPacket inputs).guardOk = true :=
      quote_eq_some_canonicalWinner_iff_guardOk inputs
    _ ↔ inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true :=
      guardOk_iff inputs

theorem quote_isSome_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote.isSome = true ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
        inputs.projectionCoverHolds = true := by
  constructor
  · intro hSome
    rcases (quote_isSome_iff inputs).1 hSome with ⟨hEq, hCover⟩
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · constructor
      · intro x hx
        simpa [hEq] using canonicalWinner_keyLe_all inputs hx
      · exact hCover
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2.1
    exact (quote_isSome_iff inputs).2 ⟨hEq, hMin.2.2⟩

theorem quote_eq_some_runtimeChoice_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote = some inputs.runtimeChoice ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
        inputs.projectionCoverHolds = true := by
  constructor
  · intro hQuote
    rcases (quote_eq_some_runtimeChoice_iff inputs).1 hQuote with ⟨hEq, hCover⟩
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · constructor
      · intro x hx
        simpa [hEq] using canonicalWinner_keyLe_all inputs hx
      · exact hCover
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2.1
    exact (quote_eq_some_runtimeChoice_iff inputs).2 ⟨hEq, hMin.2.2⟩

theorem quote_eq_some_canonicalWinner_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
        inputs.projectionCoverHolds = true := by
  calc
    (buildPacket inputs).quote = some (canonicalWinner inputs) ↔
        inputs.runtimeChoice = canonicalWinner inputs ∧
          inputs.projectionCoverHolds = true :=
      quote_eq_some_canonicalWinner_iff inputs
    _ ↔
        inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
          (∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) ∧
          inputs.projectionCoverHolds = true := by
      constructor
      · intro hContract
        rcases hContract with ⟨hEq, hCover⟩
        constructor
        · simpa [hEq] using canonicalWinner_mem inputs
        · constructor
          · intro x hx
            simpa [hEq] using canonicalWinner_keyLe_all inputs hx
          · exact hCover
      · intro hMin
        exact
          ⟨canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2.1,
            hMin.2.2⟩

theorem mismatch_error_iff
    (inputs : Inputs) :
    (buildPacket inputs).error = some GuardError.runtimeNotCanonical ↔
      inputs.runtimeChoice ≠ canonicalWinner inputs := by
  by_cases hMatch : (buildContract inputs).runtimeMatchesCanonical = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs := by
      simpa [runtimeMatchesCanonical_iff] using hMatch
    by_cases hOk : (buildContract inputs).contractOk = true
    · simp [buildPacket, hOk, hEq]
    · simp [buildPacket, hOk, hMatch, hEq]
  · have hMatchFalse : (buildContract inputs).runtimeMatchesCanonical = false := by
      cases hVal : (buildContract inputs).runtimeMatchesCanonical <;> simp [hVal] at hMatch ⊢
    have hNe : inputs.runtimeChoice ≠ canonicalWinner inputs := by
      intro hEq
      have hTrue : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hEq
      exact hMatch hTrue
    have hOkFalse : (buildContract inputs).contractOk = false :=
      not_contractOk_without_runtime_canonicality inputs hNe
    simp [buildPacket, hOkFalse, hMatchFalse, hNe]

theorem projection_cover_error_iff
    (inputs : Inputs) :
    (buildPacket inputs).error = some GuardError.projectionCoverNotVerified ↔
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = false := by
  by_cases hMatch : (buildContract inputs).runtimeMatchesCanonical = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs := by
      simpa [runtimeMatchesCanonical_iff] using hMatch
    by_cases hCover : inputs.projectionCoverHolds = true
    · have hOk : (buildContract inputs).contractOk = true :=
        (contractOk_iff inputs).2 ⟨hEq, hCover⟩
      simp [buildPacket, hOk, hCover]
    · have hCoverFalse : inputs.projectionCoverHolds = false := by
        cases hVal : inputs.projectionCoverHolds <;> simp [hVal] at hCover ⊢
      have hOkFalse : (buildContract inputs).contractOk = false :=
        not_contractOk_without_projection_cover inputs hCoverFalse
      simp [buildPacket, hOkFalse, hMatch, hEq, hCoverFalse]
  · have hMatchFalse : (buildContract inputs).runtimeMatchesCanonical = false := by
      cases hVal : (buildContract inputs).runtimeMatchesCanonical <;> simp [hVal] at hMatch ⊢
    have hNe : inputs.runtimeChoice ≠ canonicalWinner inputs := by
      intro hEq
      have hTrue : (buildContract inputs).runtimeMatchesCanonical = true := by
        simpa [runtimeMatchesCanonical_iff] using hEq
      exact hMatch hTrue
    have hOkFalse : (buildContract inputs).contractOk = false :=
      not_contractOk_without_runtime_canonicality inputs hNe
    simp [buildPacket, hOkFalse, hMatchFalse, hNe]

end ExactOutManyPoolGuardedQuotePacket
end Routing
end TauSwap
