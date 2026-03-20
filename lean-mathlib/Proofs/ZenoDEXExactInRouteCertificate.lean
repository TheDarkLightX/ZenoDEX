/-!
# ZenoDEX Exact-In Route Certificate

This file formalizes the deterministic shell around the exact-in route
canonical certificate.

It proves:

- the certificate winner is the lexicographically minimal
  `(routeKeyRank, candidateIndex)` pair among the non-empty candidate stream,
- verifier success is equivalent to equality with the canonical rebuilt
  certificate,
- the verifying certificate is unique for a fixed candidate stream and binding
  bit.

This proof models the Tau-visible key ranks, not the full Python route-key
construction. The shipped runtime is still responsible for mapping the exact
route key

`(-amount_out, hop_count, leg_count, pool_sequence, intermediate_asset, asset_out)`

into those deterministic ranks.
-/

namespace TauSwap
namespace Routing
namespace ExactInRouteCertificate

structure Candidate where
  candidateIndex : Nat
  routeKeyRank : Nat
deriving DecidableEq, Repr

def keyLe (a b : Candidate) : Prop :=
  a.routeKeyRank < b.routeKeyRank ∨
    (a.routeKeyRank = b.routeKeyRank ∧ a.candidateIndex ≤ b.candidateIndex)

instance (a b : Candidate) : Decidable (keyLe a b) := by
  unfold keyLe
  infer_instance

def chooseBetter (best cand : Candidate) : Candidate :=
  if cand.routeKeyRank < best.routeKeyRank then
    cand
  else if best.routeKeyRank < cand.routeKeyRank then
    best
  else if cand.candidateIndex < best.candidateIndex then
    cand
  else
    best

theorem keyLe_trans {a b c : Candidate} :
    keyLe a b → keyLe b c → keyLe a c := by
  intro hAB hBC
  rcases hAB with hAB | ⟨hRankAB, hIdxAB⟩
  · rcases hBC with hBC | ⟨hRankBC, _hIdxBC⟩
    · exact Or.inl (Nat.lt_trans hAB hBC)
    · exact Or.inl (by simpa [hRankBC] using hAB)
  · rcases hBC with hBC | ⟨hRankBC, hIdxBC⟩
    · exact Or.inl (by simpa [hRankAB] using hBC)
    · exact Or.inr ⟨hRankAB.trans hRankBC, Nat.le_trans hIdxAB hIdxBC⟩

theorem chooseBetter_keyLe_best (best cand : Candidate) :
    keyLe (chooseBetter best cand) best := by
  by_cases h₁ : cand.routeKeyRank < best.routeKeyRank
  · simp [chooseBetter, keyLe, h₁]
  · by_cases h₂ : best.routeKeyRank < cand.routeKeyRank
    · simp [chooseBetter, h₁, h₂, keyLe]
    · have hrEq : cand.routeKeyRank = best.routeKeyRank := by
        exact Nat.le_antisymm
          (Nat.le_of_not_lt h₂)
          (Nat.le_of_not_lt h₁)
      by_cases h₃ : cand.candidateIndex < best.candidateIndex
      · simpa [chooseBetter, h₁, h₂, h₃, keyLe] using
          (Or.inr ⟨hrEq, Nat.le_of_lt h₃⟩ : keyLe cand best)
      · simp [chooseBetter, h₁, h₂, h₃, keyLe]

theorem chooseBetter_keyLe_cand (best cand : Candidate) :
    keyLe (chooseBetter best cand) cand := by
  by_cases h₁ : cand.routeKeyRank < best.routeKeyRank
  · simp [chooseBetter, h₁, keyLe]
  · by_cases h₂ : best.routeKeyRank < cand.routeKeyRank
    · simp [chooseBetter, h₁, h₂, keyLe]
    · have hrEq : cand.routeKeyRank = best.routeKeyRank := by
        exact Nat.le_antisymm
          (Nat.le_of_not_lt h₂)
          (Nat.le_of_not_lt h₁)
      by_cases h₃ : cand.candidateIndex < best.candidateIndex
      · simp [chooseBetter, h₃, keyLe, hrEq]
      · have hidx : best.candidateIndex ≤ cand.candidateIndex := by
          exact Nat.le_of_not_lt h₃
        simpa [chooseBetter, h₁, h₂, h₃, keyLe, hrEq] using
          (Or.inr ⟨hrEq.symm, hidx⟩ : keyLe best cand)

theorem foldl_chooseBetter_keyLe_all :
    ∀ (best0 : Candidate) (xs : List Candidate),
      keyLe (xs.foldl chooseBetter best0) best0 ∧
        (∀ a ∈ xs, keyLe (xs.foldl chooseBetter best0) a) := by
  intro best0 xs
  induction xs generalizing best0 with
  | nil =>
      simp [List.foldl, keyLe]
  | cons a xs ih =>
      have ih' := ih (best0 := chooseBetter best0 a)
      have hStepBest : keyLe (chooseBetter best0 a) best0 :=
        chooseBetter_keyLe_best best0 a
      have hStepA : keyLe (chooseBetter best0 a) a :=
        chooseBetter_keyLe_cand best0 a
      constructor
      · have hBestLeStep : keyLe (xs.foldl chooseBetter (chooseBetter best0 a)) (chooseBetter best0 a) :=
          ih'.1
        have hBestLeBest0 : keyLe (xs.foldl chooseBetter (chooseBetter best0 a)) best0 :=
          keyLe_trans hBestLeStep hStepBest
        simpa [List.foldl] using hBestLeBest0
      · intro x hx
        have hBestLeStep : keyLe (xs.foldl chooseBetter (chooseBetter best0 a)) (chooseBetter best0 a) :=
          ih'.1
        have hx' : x = a ∨ x ∈ xs := by
          simpa using hx
        cases hx' with
        | inl hxEq =>
            have hBestLeA : keyLe (xs.foldl chooseBetter (chooseBetter best0 a)) a :=
              keyLe_trans hBestLeStep hStepA
            simpa [hxEq, List.foldl] using hBestLeA
        | inr hxMem =>
            have hBestLeX : keyLe (xs.foldl chooseBetter (chooseBetter best0 a)) x :=
              ih'.2 x hxMem
            simpa [List.foldl] using hBestLeX

structure ArgminStep where
  winnerKey : Nat
  winnerIndex : Nat
  candKey : Nat
  candIndex : Nat
  bindingOk : Bool
deriving DecidableEq, Repr

def buildArgminStep
    (winnerKey winnerIndex candKey candIndex : Nat)
    (bindingOk : Bool) : ArgminStep :=
  {
    winnerKey := winnerKey
    winnerIndex := winnerIndex
    candKey := candKey
    candIndex := candIndex
    bindingOk := bindingOk
  }

structure Certificate where
  winnerIndex : Nat
  winnerKey : Nat
  argminSteps : List ArgminStep
deriving DecidableEq, Repr

def buildCertificate
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool) : Certificate :=
  let winner := rest.foldl chooseBetter first
  {
    winnerIndex := winner.candidateIndex
    winnerKey := winner.routeKeyRank
    argminSteps :=
      (first :: rest).map fun cand =>
        buildArgminStep
          winner.routeKeyRank
          winner.candidateIndex
          cand.routeKeyRank
          cand.candidateIndex
          bindingOk
  }

def verifyCertificate
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool)
    (certificate : Certificate) : Prop :=
  certificate = buildCertificate first rest bindingOk

theorem verifyCertificate_iff
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool)
    (certificate : Certificate) :
    verifyCertificate first rest bindingOk certificate ↔
      certificate = buildCertificate first rest bindingOk := by
  rfl

theorem verifyCertificate_of_build
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool) :
    verifyCertificate
      first
      rest
      bindingOk
      (buildCertificate first rest bindingOk) := by
  rfl

theorem verifyingCertificate_unique
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool)
    {certificate : Certificate}
    (hVerify : verifyCertificate first rest bindingOk certificate) :
    certificate = buildCertificate first rest bindingOk := by
  exact hVerify

theorem buildCertificate_winner_keyLe_all
    (first : Candidate)
    (rest : List Candidate)
    (bindingOk : Bool)
    {cand : Candidate}
    (hMem : cand ∈ first :: rest) :
    keyLe
      { candidateIndex := (buildCertificate first rest bindingOk).winnerIndex
        routeKeyRank := (buildCertificate first rest bindingOk).winnerKey }
      cand := by
  have hFold := foldl_chooseBetter_keyLe_all first rest
  change keyLe
    { candidateIndex := (rest.foldl chooseBetter first).candidateIndex
      routeKeyRank := (rest.foldl chooseBetter first).routeKeyRank }
    cand
  have hCases : cand = first ∨ cand ∈ rest := by
    exact List.mem_cons.mp hMem
  cases hCases with
  | inl hEq =>
      simpa [hEq] using hFold.1
  | inr hMemRest =>
      exact hFold.2 cand hMemRest

theorem buildCertificate_prefers_lower_candidate_index_on_equal_key
    (best cand : Candidate)
    (hRank : cand.routeKeyRank = best.routeKeyRank)
    (hIdx : cand.candidateIndex < best.candidateIndex) :
    chooseBetter best cand = cand := by
  unfold chooseBetter
  have hNotLt : ¬ cand.routeKeyRank < best.routeKeyRank := by
    intro h
    exact Nat.lt_irrefl _ (hRank ▸ h)
  have hNotGt : ¬ best.routeKeyRank < cand.routeKeyRank := by
    intro h
    exact Nat.lt_irrefl _ (hRank.symm ▸ h)
  simp [hNotLt, hNotGt, hIdx]

end ExactInRouteCertificate
end Routing
end TauSwap
