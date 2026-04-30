/-!
# ZenoDEX AutoTrader Binary Decision

This file formalizes the mathematical core of the current AutoTrader binary
decision kernel:

- candidate `0` is `NO_OP` with key `0`
- candidate `1` is `EMIT_COMPILED_INTENT` with key `1` iff
  `emitRequested && emitAdmissible`
- the canonical winner is selected under the same pair order used by the Tau
  `argmax_stream_certificate_v1` surface:
  larger key wins, and ties prefer the smaller index

This proves the kernel-level claim only. It does **not** prove the surrounding
hash/provenance binding surface from the imperative shell.
-/

namespace TauSwap
namespace AutoTrader
namespace BinaryDecision

abbrev Candidate := Nat × Nat

/-- Tau-side argmax pair order: larger key wins; ties prefer smaller index. -/
def GePair (winner candidate : Candidate) : Prop :=
  winner.1 > candidate.1 ∨ (winner.1 = candidate.1 ∧ winner.2 ≤ candidate.2)

instance (winner candidate : Candidate) : Decidable (GePair winner candidate) := by
  unfold GePair
  infer_instance

def emitKey (emitRequested emitAdmissible : Bool) : Nat :=
  if emitRequested && emitAdmissible then 1 else 0

def winnerIndex (emitRequested emitAdmissible : Bool) : Nat :=
  if emitRequested && emitAdmissible then 1 else 0

def winnerKey (emitRequested emitAdmissible : Bool) : Nat :=
  if emitRequested && emitAdmissible then 1 else 0

def winnerPair (emitRequested emitAdmissible : Bool) : Candidate :=
  (winnerKey emitRequested emitAdmissible, winnerIndex emitRequested emitAdmissible)

def candidateSet (emitRequested emitAdmissible : Bool) : List Candidate :=
  [(0, 0), (emitKey emitRequested emitAdmissible, 1)]

def CanonicalWinner (emitRequested emitAdmissible : Bool) (k : Candidate) : Prop :=
  k ∈ candidateSet emitRequested emitAdmissible ∧
    ∀ x ∈ candidateSet emitRequested emitAdmissible, GePair k x

theorem winnerPair_ge_noop (emitRequested emitAdmissible : Bool) :
    GePair (winnerPair emitRequested emitAdmissible) (0, 0) := by
  by_cases hRequested : emitRequested = true
  · by_cases hAdmissible : emitAdmissible = true
    · simp [winnerPair, winnerKey, winnerIndex, GePair, hRequested, hAdmissible]
    · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
      simp [winnerPair, winnerKey, winnerIndex, GePair, hRequested, hBlocked]
  · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
    simp [winnerPair, winnerKey, winnerIndex, GePair, hBlocked]

theorem winnerPair_ge_emitCandidate (emitRequested emitAdmissible : Bool) :
    GePair (winnerPair emitRequested emitAdmissible) (emitKey emitRequested emitAdmissible, 1) := by
  by_cases hRequested : emitRequested = true
  · by_cases hAdmissible : emitAdmissible = true
    · simp [winnerPair, winnerKey, winnerIndex, emitKey, GePair, hRequested, hAdmissible]
    · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
      simp [winnerPair, winnerKey, winnerIndex, emitKey, GePair, hRequested, hBlocked]
  · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
    simp [winnerPair, winnerKey, winnerIndex, emitKey, GePair, hBlocked]

theorem noop_tie_break_when_emit_blocked
    (h : emitRequested && emitAdmissible = false) :
    winnerPair emitRequested emitAdmissible = (0, 0) := by
  by_cases hRequested : emitRequested = true
  · by_cases hAdmissible : emitAdmissible = true
    · simp [hRequested, hAdmissible] at h
    · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
      simp [winnerPair, winnerKey, winnerIndex, hRequested, hBlocked]
  · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
    simp [winnerPair, winnerKey, winnerIndex, hBlocked]

theorem emit_wins_when_requested_and_admissible
    (h : emitRequested && emitAdmissible = true) :
    winnerPair emitRequested emitAdmissible = (1, 1) := by
  by_cases hRequested : emitRequested = true
  · by_cases hAdmissible : emitAdmissible = true
    · simp [winnerPair, winnerKey, winnerIndex, hRequested, hAdmissible]
    · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
      simp [hRequested, hBlocked] at h
  · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
    simp [hBlocked] at h

theorem winnerPair_is_canonical (emitRequested emitAdmissible : Bool) :
    CanonicalWinner emitRequested emitAdmissible (winnerPair emitRequested emitAdmissible) := by
  constructor
  · by_cases hRequested : emitRequested = true
    · by_cases hAdmissible : emitAdmissible = true
      · simp [candidateSet, winnerPair, winnerKey, winnerIndex, emitKey,
          hRequested, hAdmissible]
      · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
        simp [candidateSet, winnerPair, winnerKey, winnerIndex, emitKey,
          hRequested, hBlocked]
    · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
      simp [candidateSet, winnerPair, winnerKey, winnerIndex, emitKey, hBlocked]
  · intro x hx
    have hx' : x = (0, 0) ∨ x = (emitKey emitRequested emitAdmissible, 1) := by
      simpa [candidateSet] using hx
    rcases hx' with h | h
    · simpa [h] using winnerPair_ge_noop emitRequested emitAdmissible
    · simpa [h] using winnerPair_ge_emitCandidate emitRequested emitAdmissible

theorem canonicalWinner_unique
    (emitRequested emitAdmissible : Bool) {k : Candidate}
    (hk : CanonicalWinner emitRequested emitAdmissible k) :
    k = winnerPair emitRequested emitAdmissible := by
  by_cases hRequested : emitRequested = true
  · by_cases hAdmissible : emitAdmissible = true
    · simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex,
        emitKey, GePair, hRequested, hAdmissible] at hk ⊢
      rcases hk with ⟨hk_mem, _hk_noop, hk_emit⟩
      rcases hk_mem with rfl | rfl
      · exfalso
        simp at hk_emit
      · rfl
    · have hBlocked : emitAdmissible = false := Bool.eq_false_iff.mpr hAdmissible
      simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex,
        emitKey, GePair, hRequested, hBlocked] at hk ⊢
      rcases hk with ⟨hk_mem, hk_noop, _hk_emit⟩
      rcases hk_mem with rfl | rfl
      · rfl
      · exfalso
        simp at hk_noop
  · have hBlocked : emitRequested = false := Bool.eq_false_iff.mpr hRequested
    simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex,
      emitKey, GePair, hBlocked] at hk ⊢
    rcases hk with ⟨hk_mem, hk_noop, _hk_emit⟩
    rcases hk_mem with rfl | rfl
    · rfl
    · exfalso
      simp at hk_noop

theorem exists_unique_canonicalWinner (emitRequested emitAdmissible : Bool) :
    ∃ k, CanonicalWinner emitRequested emitAdmissible k ∧
      ∀ y, CanonicalWinner emitRequested emitAdmissible y → y = k := by
  refine
    ⟨winnerPair emitRequested emitAdmissible,
      winnerPair_is_canonical emitRequested emitAdmissible, ?_⟩
  intro y hy
  exact canonicalWinner_unique emitRequested emitAdmissible hy

end BinaryDecision
end AutoTrader
end TauSwap
