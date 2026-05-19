import Mathlib

/-!
# ZenoEnergy Advisory Boundary

This file promotes the Aristotle-checked boundary for using an energy-based
reasoning or ranking model inside ZenoDEX. The model may rank candidates or
suggest an early stop. The verifier-facing cost and explicit certificates remain
the authority.

It does not prove learned-model calibration, profitability, full generative EBM
correctness, or that energy alone authorizes a value-moving action.
-/

namespace Proofs
namespace ZenoEnergyAdvisoryBoundary

/-- Abstract settlement, route, proof, or action candidate. -/
structure Candidate where
  id : Nat
deriving DecidableEq, Repr

/--
`WithinEps energy trueCost eps` says the advisory energy cost is an eps-close
approximation of the verifier-facing true cost. Lower cost is better.
-/
def WithinEps (energy trueCost eps : Nat) : Prop :=
  energy <= trueCost + eps ∧ trueCost <= energy + eps

/-- True verifier-facing weak optimality on a finite candidate list. -/
def TrueWeaklyBest
    (trueCost : Candidate -> Nat)
    (winner : Candidate)
    (candidates : List Candidate) : Prop :=
  ∀ candidate, candidate ∈ candidates -> trueCost winner <= trueCost candidate

/-- True verifier-facing weak maximality on a finite candidate list. -/
def TrueWeaklyMax
    (score : Candidate -> Nat)
    (winner : Candidate)
    (candidates : List Candidate) : Prop :=
  ∀ candidate, candidate ∈ candidates -> score candidate <= score winner

/-- Global weak optimality over a feasible predicate. -/
def GloballyTrueWeaklyBest
    (trueCost : Candidate -> Nat)
    (winner : Candidate)
    (Feasible : Candidate -> Prop) : Prop :=
  ∀ candidate, Feasible candidate -> trueCost winner <= trueCost candidate

/-- Global weak maximality over a feasible predicate. -/
def GloballyTrueWeaklyMax
    (score : Candidate -> Nat)
    (winner : Candidate)
    (Feasible : Candidate -> Prop) : Prop :=
  ∀ candidate, Feasible candidate -> score candidate <= score winner

/--
If the winner's advisory energy is separated from another candidate's advisory
energy by at least `2 * eps`, and both energies are eps-close to verifier cost,
then the verifier-facing true cost also ranks the winner no worse.
-/
theorem gap_separated_energy_order_preserves_true_order
    {energyWinner energyOther trueWinner trueOther eps : Nat}
    (hWinnerApprox : WithinEps energyWinner trueWinner eps)
    (hOtherApprox : WithinEps energyOther trueOther eps)
    (hGap : energyWinner + eps + eps <= energyOther) :
    trueWinner <= trueOther := by
  unfold WithinEps at *
  omega

/--
Energy ordering alone is not a verifier-facing minimization certificate. This
counterexample keeps the advisory energy winner first while the true verifier
cost favors the other candidate.
-/
theorem energy_order_alone_does_not_imply_true_weakly_best :
    ¬ (∀ (energy trueCost : Candidate -> Nat)
          (winner : Candidate)
          (candidates : List Candidate),
        winner ∈ candidates ->
        (∀ candidate, candidate ∈ candidates ->
          energy winner <= energy candidate) ->
        TrueWeaklyBest trueCost winner candidates) := by
  intro h
  let winner : Candidate := ⟨0⟩
  let challenger : Candidate := ⟨1⟩
  let energy : Candidate -> Nat := fun candidate =>
    if candidate = winner then 0 else 1
  let trueCost : Candidate -> Nat := fun candidate =>
    if candidate = winner then 1 else 0
  have hWinnerIn : winner ∈ [winner, challenger] := by
    simp
  have hEnergyBest :
      ∀ candidate, candidate ∈ [winner, challenger] ->
        energy winner <= energy candidate := by
    intro candidate hMember
    simp only [List.mem_cons, List.mem_nil_iff] at hMember
    rcases hMember with rfl | hMember
    · simp [energy]
    · rcases hMember with rfl | hNil
      · simp [energy, winner, challenger]
      · cases hNil
  have hBest :=
    h energy trueCost winner [winner, challenger] hWinnerIn hEnergyBest
  have hChallengerIn : challenger ∈ [winner, challenger] := by
    simp
  have hContradiction := hBest challenger hChallengerIn
  simp [trueCost, winner, challenger] at hContradiction

/--
Energy ordering alone is not a verifier-facing maximization certificate. This
counterexample keeps the advisory energy winner first while the true verifier
score favors the other candidate.
-/
theorem energy_order_alone_does_not_imply_true_weakly_max :
    ¬ (∀ (energy score : Candidate -> Nat)
          (winner : Candidate)
          (candidates : List Candidate),
        winner ∈ candidates ->
        (∀ candidate, candidate ∈ candidates ->
          energy winner <= energy candidate) ->
        TrueWeaklyMax score winner candidates) := by
  intro h
  let winner : Candidate := ⟨0⟩
  let challenger : Candidate := ⟨1⟩
  let energy : Candidate -> Nat := fun candidate =>
    if candidate = winner then 0 else 1
  let score : Candidate -> Nat := fun candidate =>
    if candidate = winner then 0 else 1
  have hWinnerIn : winner ∈ [winner, challenger] := by
    simp
  have hEnergyBest :
      ∀ candidate, candidate ∈ [winner, challenger] ->
        energy winner <= energy candidate := by
    intro candidate hMember
    simp only [List.mem_cons, List.mem_nil_iff] at hMember
    rcases hMember with rfl | hMember
    · simp [energy]
    · rcases hMember with rfl | hNil
      · simp [energy, winner, challenger]
      · cases hNil
  have hBest :=
    h energy score winner [winner, challenger] hWinnerIn hEnergyBest
  have hChallengerIn : challenger ∈ [winner, challenger] := by
    simp
  have hContradiction := hBest challenger hChallengerIn
  simp [score, winner, challenger] at hContradiction

/--
The verifier has directly checked the prefix. For the unchecked suffix, it has
an eps-approximation certificate and a large enough advisory-energy gap. Then
the winner is true-weakly-best over the concatenated finite list.
-/
theorem energy_gap_suffix_checked_stop_implies_true_best_concat
    {energy trueCost : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix : List Candidate}
    {eps : Nat}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyBest trueCost winner checked)
    (hWinnerApprox : WithinEps (energy winner) (trueCost winner) eps)
    (hSuffixApprox :
      ∀ candidate, candidate ∈ suffix ->
        WithinEps (energy candidate) (trueCost candidate) eps)
    (hSuffixGap :
      ∀ candidate, candidate ∈ suffix ->
        energy winner + eps + eps <= energy candidate) :
    TrueWeaklyBest trueCost winner (checked ++ suffix) ∧
      winner ∈ checked ++ suffix := by
  constructor
  · intro candidate hMember
    rw [List.mem_append] at hMember
    cases hMember with
    | inl hCheckedMember => exact hChecked candidate hCheckedMember
    | inr hSuffixMember =>
        exact
          gap_separated_energy_order_preserves_true_order
            hWinnerApprox
            (hSuffixApprox candidate hSuffixMember)
            (hSuffixGap candidate hSuffixMember)
  · exact List.mem_append_left _ hWinnerIn

/--
If the checked prefix plus unchecked suffix is a permutation of the full exact
candidate set, the checked-stop certificate transfers to the full list.
-/
theorem energy_gap_checked_stop_with_full_permutation
    {energy trueCost : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix full : List Candidate}
    {eps : Nat}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyBest trueCost winner checked)
    (hWinnerApprox : WithinEps (energy winner) (trueCost winner) eps)
    (hSuffixApprox :
      ∀ candidate, candidate ∈ suffix ->
        WithinEps (energy candidate) (trueCost candidate) eps)
    (hSuffixGap :
      ∀ candidate, candidate ∈ suffix ->
        energy winner + eps + eps <= energy candidate)
    (hPerm : (checked ++ suffix).Perm full) :
    TrueWeaklyBest trueCost winner full ∧ winner ∈ full := by
  have hConcat :=
    energy_gap_suffix_checked_stop_implies_true_best_concat
      hWinnerIn hChecked hWinnerApprox hSuffixApprox hSuffixGap
  constructor
  · intro candidate hMember
    exact hConcat.1 candidate (hPerm.mem_iff.mpr hMember)
  · exact hPerm.mem_iff.mp hConcat.2

/--
The energy model may choose the schedule and propose an early stop, but the
global claim only follows when the finite list has exact feasible coverage.
-/
theorem energy_gap_checked_stop_with_exact_coverage_implies_global
    {energy trueCost : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix full : List Candidate}
    {Feasible : Candidate -> Prop}
    {eps : Nat}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyBest trueCost winner checked)
    (hWinnerApprox : WithinEps (energy winner) (trueCost winner) eps)
    (hSuffixApprox :
      ∀ candidate, candidate ∈ suffix ->
        WithinEps (energy candidate) (trueCost candidate) eps)
    (hSuffixGap :
      ∀ candidate, candidate ∈ suffix ->
        energy winner + eps + eps <= energy candidate)
    (hPerm : (checked ++ suffix).Perm full)
    (hCoverage : ∀ candidate, Feasible candidate -> candidate ∈ full) :
    GloballyTrueWeaklyBest trueCost winner Feasible := by
  have hFull :=
    (energy_gap_checked_stop_with_full_permutation
      hWinnerIn hChecked hWinnerApprox hSuffixApprox hSuffixGap hPerm).1
  intro candidate hFeasible
  exact hFull candidate (hCoverage candidate hFeasible)

/--
A deterministic suffix upper-bound certificate is enough for maximization
objectives such as UPBA volume/surplus encodings. The model may choose the
order, while the stop claim follows from checked-prefix dominance plus a
verifier-facing bound for each unchecked suffix candidate.
-/
theorem suffix_upper_bound_checked_stop_implies_true_max_concat
    {score upperBound : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix : List Candidate}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyMax score winner checked)
    (hSuffixUpper :
      ∀ candidate, candidate ∈ suffix ->
        score candidate <= upperBound candidate)
    (hSuffixDominated :
      ∀ candidate, candidate ∈ suffix ->
        upperBound candidate <= score winner) :
    TrueWeaklyMax score winner (checked ++ suffix) ∧
      winner ∈ checked ++ suffix := by
  constructor
  · intro candidate hMember
    rw [List.mem_append] at hMember
    cases hMember with
    | inl hCheckedMember => exact hChecked candidate hCheckedMember
    | inr hSuffixMember =>
        exact
          Nat.le_trans
            (hSuffixUpper candidate hSuffixMember)
            (hSuffixDominated candidate hSuffixMember)
  · exact List.mem_append_left _ hWinnerIn

/--
If the checked prefix and unchecked suffix are a permutation of the exact finite
candidate list, the deterministic suffix-bound certificate transfers to that
full list.
-/
theorem suffix_upper_bound_checked_stop_with_full_permutation
    {score upperBound : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix full : List Candidate}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyMax score winner checked)
    (hSuffixUpper :
      ∀ candidate, candidate ∈ suffix ->
        score candidate <= upperBound candidate)
    (hSuffixDominated :
      ∀ candidate, candidate ∈ suffix ->
        upperBound candidate <= score winner)
    (hPerm : (checked ++ suffix).Perm full) :
    TrueWeaklyMax score winner full ∧ winner ∈ full := by
  have hConcat :=
    suffix_upper_bound_checked_stop_implies_true_max_concat
      hWinnerIn hChecked hSuffixUpper hSuffixDominated
  constructor
  · intro candidate hMember
    exact hConcat.1 candidate (hPerm.mem_iff.mpr hMember)
  · exact hPerm.mem_iff.mp hConcat.2

/--
Exact finite-list coverage promotes the suffix-bound checked-stop certificate to
a global weak-maximality claim over the scoped feasible predicate.
-/
theorem suffix_upper_bound_checked_stop_with_exact_coverage_implies_global
    {score upperBound : Candidate -> Nat}
    {winner : Candidate}
    {checked suffix full : List Candidate}
    {Feasible : Candidate -> Prop}
    (hWinnerIn : winner ∈ checked)
    (hChecked : TrueWeaklyMax score winner checked)
    (hSuffixUpper :
      ∀ candidate, candidate ∈ suffix ->
        score candidate <= upperBound candidate)
    (hSuffixDominated :
      ∀ candidate, candidate ∈ suffix ->
        upperBound candidate <= score winner)
    (hPerm : (checked ++ suffix).Perm full)
    (hCoverage : ∀ candidate, Feasible candidate -> candidate ∈ full) :
    GloballyTrueWeaklyMax score winner Feasible := by
  have hFull :=
    (suffix_upper_bound_checked_stop_with_full_permutation
      hWinnerIn hChecked hSuffixUpper hSuffixDominated hPerm).1
  intro candidate hFeasible
  exact hFull candidate (hCoverage candidate hFeasible)

end ZenoEnergyAdvisoryBoundary
end Proofs
