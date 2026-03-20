import Proofs.ZenoDEXExactInRouteRankProjection
import Proofs.ZenoDEXUniqueCanonicalWinnerEverywhere

namespace TauSwap
namespace Routing
namespace ExactInTrueKeyWinner

open ExactInRouteCertificate
open ExactInRouteRankProjection
open UniqueCanonicalWinnerEverywhere

variable {α : Type} [LinearOrder α]

def projectedCandidates (keys : List α) : List Candidate :=
  (List.finRange keys.length).map (projectedCandidate keys)

theorem mem_projectedCandidates (keys : List α) (i : Fin keys.length) :
    projectedCandidate keys i ∈ projectedCandidates keys := by
  unfold projectedCandidates
  exact List.mem_map.2 ⟨i, by simp, rfl⟩

theorem candidateIndex_lt_length_of_mem_projectedCandidates
    {keys : List α} {cand : Candidate}
    (h : cand ∈ projectedCandidates keys) :
    cand.candidateIndex < keys.length := by
  unfold projectedCandidates at h
  rcases List.mem_map.1 h with ⟨i, _hi, rfl⟩
  simpa [projectedCandidate] using i.2

theorem projectedCandidate_of_mem_projectedCandidates
    {keys : List α} {cand : Candidate}
    (h : cand ∈ projectedCandidates keys) :
    cand =
      projectedCandidate keys
        ⟨cand.candidateIndex, candidateIndex_lt_length_of_mem_projectedCandidates h⟩ := by
  unfold projectedCandidates at h
  rcases List.mem_map.1 h with ⟨i, _hi, rfl⟩
  apply congrArg (projectedCandidate keys)
  apply Fin.ext
  simp [projectedCandidate]

theorem projectedCandidate_injective (keys : List α) :
    Function.Injective (projectedCandidate keys) := by
  intro i j hij
  apply Fin.ext
  simpa [projectedCandidate] using congrArg Candidate.candidateIndex hij

theorem candidateWinner_iff_trueKeyWinner
    (keys : List α) (i : Fin keys.length) :
    (∀ cand ∈ projectedCandidates keys, keyLe (projectedCandidate keys i) cand) ↔
      (∀ j : Fin keys.length, trueKeyLe keys i j) := by
  constructor
  · intro h j
    have hmem : projectedCandidate keys j ∈ projectedCandidates keys :=
      mem_projectedCandidates keys j
    exact (projectedCandidate_keyLe_iff_trueKeyLe keys i j).1 (h _ hmem)
  · intro h cand hmem
    let j : Fin keys.length :=
      ⟨cand.candidateIndex, candidateIndex_lt_length_of_mem_projectedCandidates hmem⟩
    have hcand : cand = projectedCandidate keys j :=
      projectedCandidate_of_mem_projectedCandidates hmem
    rw [hcand]
    exact (projectedCandidate_keyLe_iff_trueKeyLe keys i j).2 (h j)

theorem exact_in_exists_unique_true_key_winner
    (first : α) (rest : List α) :
    ∃! w : Fin (List.length (first :: rest)),
      ∀ j : Fin (List.length (first :: rest)), trueKeyLe (first :: rest) w j := by
  let keys : List α := first :: rest
  let head : Fin keys.length := ⟨0, by simp [keys]⟩
  let tail : List Candidate :=
    (List.finRange rest.length).map fun j =>
      projectedCandidate keys j.succ
  have hProj :
      projectedCandidates keys =
        projectedCandidate keys head :: tail := by
    simp [projectedCandidates, keys, head, tail, List.finRange_succ]
  rcases exact_in_exists_unique_canonical_winner
      (first := projectedCandidate keys head)
      (rest := tail) with
    ⟨winner, ⟨hWinnerMem, hWinnerLe⟩, hWinnerUnique⟩
  have hWinnerMemProj : winner ∈ projectedCandidates keys := by
    simpa [hProj] using hWinnerMem
  let w : Fin keys.length :=
    ⟨winner.candidateIndex, candidateIndex_lt_length_of_mem_projectedCandidates hWinnerMemProj⟩
  have hWinnerEq : winner = projectedCandidate keys w :=
    projectedCandidate_of_mem_projectedCandidates hWinnerMemProj
  have hw : ∀ j : Fin keys.length, trueKeyLe keys w j := by
    refine (candidateWinner_iff_trueKeyWinner keys w).1 ?_
    intro cand hCand
    have : cand ∈ projectedCandidate keys head :: tail := by
      simpa [hProj] using hCand
    simpa [hWinnerEq] using hWinnerLe cand this
  refine ⟨w, ?_, ?_⟩
  · simpa [keys] using hw
  · intro w' hw'
    have hCandW : ∀ cand ∈ projectedCandidates keys, keyLe (projectedCandidate keys w) cand :=
      (candidateWinner_iff_trueKeyWinner keys w).2 hw
    have hCandW' : ∀ cand ∈ projectedCandidates keys, keyLe (projectedCandidate keys w') cand :=
      (candidateWinner_iff_trueKeyWinner keys w').2 <| by
        simpa [keys] using hw'
    have hWW' : keyLe (projectedCandidate keys w) (projectedCandidate keys w') :=
      hCandW _ (mem_projectedCandidates keys w')
    have hW'W : keyLe (projectedCandidate keys w') (projectedCandidate keys w) :=
      hCandW' _ (mem_projectedCandidates keys w)
    exact projectedCandidate_injective keys (keyLe_antisymm hW'W hWW')

end ExactInTrueKeyWinner
end Routing
end TauSwap
