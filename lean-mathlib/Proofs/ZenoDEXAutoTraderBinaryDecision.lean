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
  cases emitRequested <;> cases emitAdmissible <;> decide

theorem winnerPair_ge_emitCandidate (emitRequested emitAdmissible : Bool) :
    GePair (winnerPair emitRequested emitAdmissible) (emitKey emitRequested emitAdmissible, 1) := by
  cases emitRequested <;> cases emitAdmissible <;> decide

theorem noop_tie_break_when_emit_blocked
    (h : emitRequested && emitAdmissible = false) :
    winnerPair emitRequested emitAdmissible = (0, 0) := by
  cases emitRequested <;> cases emitAdmissible <;> simp [winnerPair, winnerKey, winnerIndex] at h ⊢

theorem emit_wins_when_requested_and_admissible
    (h : emitRequested && emitAdmissible = true) :
    winnerPair emitRequested emitAdmissible = (1, 1) := by
  cases emitRequested <;> cases emitAdmissible <;> simp [winnerPair, winnerKey, winnerIndex] at h ⊢

theorem winnerPair_is_canonical (emitRequested emitAdmissible : Bool) :
    CanonicalWinner emitRequested emitAdmissible (winnerPair emitRequested emitAdmissible) := by
  constructor
  · cases emitRequested <;> cases emitAdmissible <;>
      simp [candidateSet, winnerPair, winnerKey, winnerIndex, emitKey]
  · intro x hx
    have hx' : x = (0, 0) ∨ x = (emitKey emitRequested emitAdmissible, 1) := by
      simpa [candidateSet] using hx
    cases hx' with
    | inl h =>
        simpa [h] using winnerPair_ge_noop emitRequested emitAdmissible
    | inr h =>
        simpa [h] using winnerPair_ge_emitCandidate emitRequested emitAdmissible

theorem canonicalWinner_unique
    (emitRequested emitAdmissible : Bool) {k : Candidate}
    (hk : CanonicalWinner emitRequested emitAdmissible k) :
    k = winnerPair emitRequested emitAdmissible := by
  cases emitRequested <;> cases emitAdmissible
  · simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex, emitKey, GePair] at hk ⊢
    rcases hk with ⟨hk_mem, hk_noop, _hk_emit⟩
    rcases hk_mem with rfl | rfl
    · rfl
    · exfalso
      simp at hk_noop
  · simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex, emitKey, GePair] at hk ⊢
    rcases hk with ⟨hk_mem, hk_noop, _hk_emit⟩
    rcases hk_mem with rfl | rfl
    · rfl
    · exfalso
      simp at hk_noop
  · simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex, emitKey, GePair] at hk ⊢
    rcases hk with ⟨hk_mem, hk_noop, _hk_emit⟩
    rcases hk_mem with rfl | rfl
    · rfl
    · exfalso
      simp at hk_noop
  · simp [CanonicalWinner, candidateSet, winnerPair, winnerKey, winnerIndex, emitKey, GePair] at hk ⊢
    rcases hk with ⟨hk_mem, _hk_noop, hk_emit⟩
    rcases hk_mem with rfl | rfl
    · exfalso
      simp at hk_emit
    · rfl

theorem exists_unique_canonicalWinner (emitRequested emitAdmissible : Bool) :
    ∃ k, CanonicalWinner emitRequested emitAdmissible k ∧
      ∀ y, CanonicalWinner emitRequested emitAdmissible y → y = k := by
  refine ⟨winnerPair emitRequested emitAdmissible, winnerPair_is_canonical emitRequested emitAdmissible, by
    intro y hy
    exact canonicalWinner_unique emitRequested emitAdmissible hy⟩

end BinaryDecision
end AutoTrader
end TauSwap
