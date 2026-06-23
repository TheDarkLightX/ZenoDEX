import Proofs.ZenoDEXExactOutRouteCertificate

/-!
# ZenoDEX Exact-Out Many-Pool Oracle Contract

This file formalizes the deterministic shell around the bounded many-pool
exact-out oracle contract used by the integration audit surface.

It proves:

- the oracle contract is a deterministic rebuild from
  `(candidate stream, binding bit, runtime choice, audit metadata)`,
- verifier success is equivalent to equality with the canonical rebuilt
  contract,
- the `runtimeMatchesCanonical` bit is exactly the statement that the runtime
  choice equals the bounded canonical winner,
- the `contractOk` bit additionally requires the projection-cover witness,
- the verifying contract is unique for fixed inputs.

This proof does **not** claim that the shipped many-pool runtime already equals
the canonical winner. It only proves the shell around the bounded oracle
contract that reports that agreement or disagreement.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolOracleContract

open ExactOutRouteCertificate

structure Inputs where
  amountOutTotal : Nat
  maxLegs : Nat
  maxCandidatePools : Nat
  first : Candidate
  rest : List Candidate
  bindingOk : Bool
  runtimeChoice : Candidate
  projectionCoverHolds : Bool
deriving DecidableEq, Repr

def canonicalWinner (inputs : Inputs) : Candidate :=
  let certificate := buildCertificate inputs.first inputs.rest inputs.bindingOk
  {
    candidateIndex := certificate.winnerIndex
    routeKeyRank := certificate.winnerKey
  }

structure Contract where
  amountOutTotal : Nat
  maxLegs : Nat
  maxCandidatePools : Nat
  runtimeChoice : Candidate
  canonicalWinner : Candidate
  runtimeMatchesCanonical : Bool
  projectionCoverHolds : Bool
  contractOk : Bool
  certificate : Certificate
deriving DecidableEq, Repr

def buildContract (inputs : Inputs) : Contract :=
  let certificate := buildCertificate inputs.first inputs.rest inputs.bindingOk
  let winner : Candidate :=
    {
      candidateIndex := certificate.winnerIndex
      routeKeyRank := certificate.winnerKey
    }
  {
    amountOutTotal := inputs.amountOutTotal
    maxLegs := inputs.maxLegs
    maxCandidatePools := inputs.maxCandidatePools
    runtimeChoice := inputs.runtimeChoice
    canonicalWinner := winner
    runtimeMatchesCanonical := decide (inputs.runtimeChoice = winner)
    projectionCoverHolds := inputs.projectionCoverHolds
    contractOk := decide (inputs.runtimeChoice = winner) && inputs.projectionCoverHolds
    certificate := certificate
  }

def verifyContract (inputs : Inputs) (contract : Contract) : Prop :=
  contract = buildContract inputs

theorem chooseBetter_eq_best_or_cand (best cand : Candidate) :
    chooseBetter best cand = best ∨ chooseBetter best cand = cand := by
  unfold chooseBetter
  by_cases h₁ : cand.routeKeyRank < best.routeKeyRank
  · simp [h₁]
  · by_cases h₂ : best.routeKeyRank < cand.routeKeyRank
    · simp [h₁, h₂]
    · by_cases h₃ : cand.candidateIndex < best.candidateIndex
      · simp [h₁, h₂, h₃]
      · simp [h₁, h₂, h₃]

theorem foldl_chooseBetter_eq_best_or_mem :
    ∀ (best0 : Candidate) (xs : List Candidate),
      xs.foldl chooseBetter best0 = best0 ∨ xs.foldl chooseBetter best0 ∈ xs := by
  intro best0 xs
  induction xs generalizing best0 with
  | nil =>
      exact Or.inl rfl
  | cons a xs ih =>
      have hCases :
          xs.foldl chooseBetter (chooseBetter best0 a) = chooseBetter best0 a ∨
            xs.foldl chooseBetter (chooseBetter best0 a) ∈ xs :=
        ih (best0 := chooseBetter best0 a)
      cases hCases with
      | inl hEq =>
          rcases chooseBetter_eq_best_or_cand best0 a with hBest | hCand
          · left
            calc
              List.foldl chooseBetter best0 (a :: xs)
                  = List.foldl chooseBetter (chooseBetter best0 a) xs := by rfl
              _ = chooseBetter best0 a := hEq
              _ = best0 := hBest
          · right
            have hFoldA : List.foldl chooseBetter best0 (a :: xs) = a := by
              calc
                List.foldl chooseBetter best0 (a :: xs)
                    = List.foldl chooseBetter (chooseBetter best0 a) xs := by rfl
                _ = chooseBetter best0 a := hEq
                _ = a := hCand
            simp [hFoldA]
      | inr hTail =>
          right
          exact List.mem_cons_of_mem a (by simpa [List.foldl] using hTail)

theorem keyLe_antisymm {a b : Candidate} :
    keyLe a b → keyLe b a → a = b := by
  intro hAB hBA
  cases a with
  | mk aIdx aKey =>
    cases b with
    | mk bIdx bKey =>
      simp [keyLe] at hAB hBA
      rcases hAB with hAB | ⟨hKeyAB, hIdxAB⟩
      · rcases hBA with hBA | ⟨hKeyBA, _⟩
        · exact False.elim (Nat.lt_asymm hAB hBA)
        · have : False := by
            simp [hKeyBA] at hAB
          exact False.elim this
      · rcases hBA with hBA | ⟨_hKeyBA, hIdxBA⟩
        · have : False := by
            simp [hKeyAB] at hBA
          exact False.elim this
        · have hIdx : aIdx = bIdx := Nat.le_antisymm hIdxAB hIdxBA
          cases hKeyAB
          cases hIdx
          rfl

theorem verifyContract_iff
    (inputs : Inputs)
    (contract : Contract) :
    verifyContract inputs contract ↔
      contract = buildContract inputs := by
  rfl

theorem verifyContract_of_build
    (inputs : Inputs) :
    verifyContract inputs (buildContract inputs) := by
  rfl

theorem verifyingContract_unique
    (inputs : Inputs)
    {contract : Contract}
    (hVerify : verifyContract inputs contract) :
    contract = buildContract inputs := by
  exact hVerify

theorem canonicalWinner_mem
    (inputs : Inputs) :
    canonicalWinner inputs ∈ inputs.first :: inputs.rest := by
  simpa [canonicalWinner, buildCertificate] using
    (foldl_chooseBetter_eq_best_or_mem inputs.first inputs.rest)

theorem canonicalWinner_keyLe_all
    (inputs : Inputs)
    {cand : Candidate}
    (hMem : cand ∈ inputs.first :: inputs.rest) :
    keyLe (canonicalWinner inputs) cand := by
  simpa [canonicalWinner, buildCertificate] using
    buildCertificate_winner_keyLe_all inputs.first inputs.rest inputs.bindingOk hMem

theorem canonicalWinner_eq_of_mem_of_keyLe_all
    (inputs : Inputs)
    {cand : Candidate}
    (hMem : cand ∈ inputs.first :: inputs.rest)
    (hMin : ∀ x ∈ inputs.first :: inputs.rest, keyLe cand x) :
    cand = canonicalWinner inputs := by
  have hCandWinner : keyLe cand (canonicalWinner inputs) :=
    hMin (canonicalWinner inputs) (canonicalWinner_mem inputs)
  have hWinnerCand : keyLe (canonicalWinner inputs) cand :=
    canonicalWinner_keyLe_all inputs hMem
  exact keyLe_antisymm hCandWinner hWinnerCand

theorem canonicalWinner_eq
    (inputs : Inputs) :
    (buildContract inputs).canonicalWinner = canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem runtimeMatchesCanonical_iff
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = true ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem contractOk_iff
    (inputs : Inputs) :
    (buildContract inputs).contractOk = true ↔
      inputs.runtimeChoice = canonicalWinner inputs ∧
        inputs.projectionCoverHolds = true := by
  simp [buildContract, canonicalWinner, Bool.and_eq_true]

theorem contractOk_implies_runtimeMatchesCanonical
    (inputs : Inputs)
    (hOk : (buildContract inputs).contractOk = true) :
    (buildContract inputs).runtimeMatchesCanonical = true := by
  have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
    (contractOk_iff inputs).1 hOk |>.1
  exact (runtimeMatchesCanonical_iff inputs).2 hEq

theorem contractOk_implies_projectionCoverHolds
    (inputs : Inputs)
    (hOk : (buildContract inputs).contractOk = true) :
    inputs.projectionCoverHolds = true :=
  (contractOk_iff inputs).1 hOk |>.2

theorem not_contractOk_without_projection_cover
    (inputs : Inputs)
    (hCover : inputs.projectionCoverHolds = false) :
    (buildContract inputs).contractOk = false := by
  simp [buildContract, hCover]

theorem not_contractOk_without_runtime_canonicality
    (inputs : Inputs)
    (hMismatch : inputs.runtimeChoice ≠ canonicalWinner inputs) :
    (buildContract inputs).contractOk = false := by
  by_cases hOk : (buildContract inputs).contractOk = true
  · have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (contractOk_iff inputs).1 hOk |>.1
    exact False.elim (hMismatch hEq)
  · cases hVal : (buildContract inputs).contractOk <;> simp [hVal] at hOk ⊢

theorem runtimeMatchesCanonical_iff_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = true ↔
      inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
        ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x := by
  constructor
  · intro hMatch
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      (runtimeMatchesCanonical_iff inputs).1 hMatch
    constructor
    · simpa [hEq] using canonicalWinner_mem inputs
    · intro x hx
      simpa [hEq] using canonicalWinner_keyLe_all inputs hx
  · intro hMin
    have hEq : inputs.runtimeChoice = canonicalWinner inputs :=
      canonicalWinner_eq_of_mem_of_keyLe_all inputs hMin.1 hMin.2
    exact (runtimeMatchesCanonical_iff inputs).2 hEq

theorem runtimeMismatch_iff
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = false ↔
      inputs.runtimeChoice ≠ canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem runtimeMismatch_iff_not_mem_and_keyLe_all
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = false ↔
      ¬ (inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
          ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x) := by
  constructor
  · intro hMismatch hMin
    have hMatch : (buildContract inputs).runtimeMatchesCanonical = true :=
      (runtimeMatchesCanonical_iff_mem_and_keyLe_all inputs).2 hMin
    have : false = true := hMismatch.symm.trans hMatch
    exact False.elim (Bool.false_ne_true this)
  · intro hNotMin
    by_cases hMatch : (buildContract inputs).runtimeMatchesCanonical = true
    · have hMin :
          inputs.runtimeChoice ∈ inputs.first :: inputs.rest ∧
            ∀ x ∈ inputs.first :: inputs.rest, keyLe inputs.runtimeChoice x :=
        (runtimeMatchesCanonical_iff_mem_and_keyLe_all inputs).1 hMatch
      exact False.elim (hNotMin hMin)
    · simp [buildContract] at hMatch ⊢
      exact hMatch

theorem certificate_eq_route_certificate_build
    (inputs : Inputs) :
    (buildContract inputs).certificate =
      buildCertificate inputs.first inputs.rest inputs.bindingOk := by
  simp [buildContract]

end ExactOutManyPoolOracleContract
end Routing
end TauSwap
