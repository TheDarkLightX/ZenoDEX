/-!
# Uniform Batch Optimality Boundaries

This file captures two small optimality lemmas that are useful for UPBA v2
without claiming full auction optimality.

The first lemma is fixed-price aggregate volume optimality: after a uniform price
has determined acceptable demand and supply capacity, no aggregate feasible
settlement can match more than the smaller side.

The second lemma is certificate-facing: if a verifier checks upper bounds over a
finite audited candidate list, then the submitted candidate is weakly optimal in
that audited list by volume first and surplus second. The final lemmas make the
completeness boundary explicit: audited-set optimality lifts to global
optimality only when the audit set covers every feasible candidate and the
declared winner is feasible.

The bounded price-grid lemmas make one such completeness bridge concrete:
enumerating every integer price pair up to configured bounds covers the entire
bounded grid-generated candidate family. This proves an infinite theorem family
over all grid bounds and all deterministic scorers, while keeping each deployed
certificate finite.

These theorems do not prove fair order inclusion, global price-search
completeness, multi-hop routing, or solver correctness.
-/

namespace UniformBatchOptimality

/-- Aggregate acceptable capacity at a fixed uniform price. -/
structure SideCaps where
  demandCap : Nat
  supplyCap : Nat
deriving DecidableEq, Repr

/-- Aggregate matched-flow candidate at the fixed price. -/
structure AggregateUniformCandidate where
  demandFilled : Nat
  supplyFilled : Nat
deriving DecidableEq, Repr

/-- Uniform clearing quantity at the fixed price. -/
def clearQuantity (caps : SideCaps) : Nat :=
  min caps.demandCap caps.supplyCap

/-- The matched volume is the common buy/sell fill amount for feasible candidates. -/
def matchedVolume (candidate : AggregateUniformCandidate) : Nat :=
  candidate.demandFilled

/--
Aggregate feasibility at one uniform price.

The equality represents conservation: the amount bought equals the amount sold.
The two inequalities represent side capacity after order-level price and amount
limits have already been aggregated.
-/
def AggregateFeasible (caps : SideCaps) (candidate : AggregateUniformCandidate) : Prop :=
  candidate.demandFilled = candidate.supplyFilled ∧
    candidate.demandFilled <= caps.demandCap ∧
    candidate.supplyFilled <= caps.supplyCap

/--
Any feasible aggregate uniform candidate has matched volume no larger than the
minimum of acceptable demand and acceptable supply.
-/
theorem aggregate_uniform_volume_upper_bound
    {caps : SideCaps}
    {candidate : AggregateUniformCandidate}
    (hFeasible : AggregateFeasible caps candidate) :
    matchedVolume candidate <= clearQuantity caps := by
  unfold AggregateFeasible matchedVolume clearQuantity at *
  rcases hFeasible with ⟨hConserved, hDemand, hSupply⟩
  exact Nat.le_min.mpr ⟨hDemand, by simpa [hConserved] using hSupply⟩

/-- The aggregate clearing candidate fills the smaller side exactly. -/
def aggregateClearingCandidate (caps : SideCaps) : AggregateUniformCandidate :=
  {
    demandFilled := clearQuantity caps
    supplyFilled := clearQuantity caps
  }

/-- The aggregate clearing candidate is feasible at the aggregate level. -/
theorem aggregate_clear_quantity_feasible
    (caps : SideCaps) :
    AggregateFeasible caps (aggregateClearingCandidate caps) := by
  unfold AggregateFeasible aggregateClearingCandidate clearQuantity
  exact ⟨rfl, Nat.min_le_left caps.demandCap caps.supplyCap, Nat.min_le_right caps.demandCap caps.supplyCap⟩

/--
The aggregate clearing candidate maximizes matched volume among aggregate
feasible uniform candidates at the fixed price.
-/
theorem aggregate_clear_quantity_volume_optimal
    {caps : SideCaps}
    {candidate : AggregateUniformCandidate}
    (hFeasible : AggregateFeasible caps candidate) :
    matchedVolume candidate <= matchedVolume (aggregateClearingCandidate caps) := by
  simpa [aggregateClearingCandidate, matchedVolume]
    using aggregate_uniform_volume_upper_bound (caps := caps) (candidate := candidate) hFeasible

/-- A settlement candidate as seen by a finite certificate audit set. -/
structure SettlementCandidate where
  volume : Nat
  surplus : Nat
deriving DecidableEq, Repr

/--
Weak lexicographic dominance by volume first, surplus second.

This is the certificate obligation the runtime can check locally: no audited
candidate has more volume, and no equal-volume audited candidate has more
surplus.
-/
def WeaklyDominates (winner other : SettlementCandidate) : Prop :=
  other.volume <= winner.volume ∧
    (other.volume = winner.volume -> other.surplus <= winner.surplus)

/--
Objective equivalence for quotient-style reporting.

Two candidates are interchangeable for the weak lexicographic objective exactly
when they have the same executed volume and surplus.
-/
def ObjectiveEquivalent (left right : SettlementCandidate) : Prop :=
  left.volume = right.volume ∧ left.surplus = right.surplus

/-- Weak lexicographic dominance is reflexive. -/
theorem weaklyDominates_refl
    (candidate : SettlementCandidate) :
    WeaklyDominates candidate candidate := by
  unfold WeaklyDominates
  exact ⟨Nat.le_refl candidate.volume, by intro _; exact Nat.le_refl candidate.surplus⟩

/-- Weak lexicographic dominance composes transitively. -/
theorem weaklyDominates_trans
    {candidateA candidateB candidateC : SettlementCandidate}
    (hAB : WeaklyDominates candidateA candidateB)
    (hBC : WeaklyDominates candidateB candidateC) :
    WeaklyDominates candidateA candidateC := by
  unfold WeaklyDominates at *
  rcases hAB with ⟨hVolumeAB, hSurplusAB⟩
  rcases hBC with ⟨hVolumeBC, hSurplusBC⟩
  constructor
  · exact Nat.le_trans hVolumeBC hVolumeAB
  · intro hVolumeCA
    have hVolumeA_le_B : candidateA.volume <= candidateB.volume := by
      simpa [hVolumeCA] using hVolumeBC
    have hVolumeBA : candidateB.volume = candidateA.volume :=
      Nat.le_antisymm hVolumeAB hVolumeA_le_B
    have hVolumeB_le_C : candidateB.volume <= candidateC.volume := by
      simpa [← hVolumeCA] using hVolumeAB
    have hVolumeCB : candidateC.volume = candidateB.volume :=
      Nat.le_antisymm hVolumeBC hVolumeB_le_C
    exact Nat.le_trans (hSurplusBC hVolumeCB) (hSurplusAB hVolumeBA)

/--
An objective-equivalent candidate inherits weak dominance obligations from the
representative that already satisfies them.
-/
theorem objective_equivalent_transfers_weak_dominance
    {winner equivalent candidate : SettlementCandidate}
    (hEquivalent : ObjectiveEquivalent equivalent winner)
    (hDominates : WeaklyDominates winner candidate) :
    WeaklyDominates equivalent candidate := by
  unfold ObjectiveEquivalent WeaklyDominates at *
  rcases hEquivalent with ⟨hVolumeEq, hSurplusEq⟩
  rcases hDominates with ⟨hVolume, hSurplus⟩
  constructor
  · simpa [hVolumeEq] using hVolume
  · intro hCandidateVolume
    have hCandidateWinnerVolume : candidate.volume = winner.volume :=
      hCandidateVolume.trans hVolumeEq
    simpa [hSurplusEq] using hSurplus hCandidateWinnerVolume

/-- Winner is weakly optimal inside a finite audited candidate list. -/
def WeaklyOptimalIn
    (winner : SettlementCandidate)
    (candidates : List SettlementCandidate) : Prop :=
  ∀ candidate, candidate ∈ candidates -> WeaklyDominates winner candidate

/--
If a checked candidate is objective-equivalent to an audited winner, it is
weakly optimal over the same finite list.
-/
theorem objective_equivalent_preserves_weak_optimal_in
    {winner equivalent : SettlementCandidate}
    {candidates : List SettlementCandidate}
    (hEquivalent : ObjectiveEquivalent equivalent winner)
    (hWinnerOptimal : WeaklyOptimalIn winner candidates) :
    WeaklyOptimalIn equivalent candidates := by
  unfold WeaklyOptimalIn at *
  intro candidate hMember
  exact
    objective_equivalent_transfers_weak_dominance
      hEquivalent
      (hWinnerOptimal candidate hMember)

/--
A pruned candidate list dominates a full candidate list when every full-domain
candidate has a retained representative that is weakly at least as good.
-/
def DominanceCover
    (pruned full : List SettlementCandidate) : Prop :=
  ∀ candidate, candidate ∈ full ->
    ∃ representative, representative ∈ pruned ∧ WeaklyDominates representative candidate

/-- The audited list covers every candidate that the external feasibility predicate admits. -/
def CompleteAuditSet
    (candidates : List SettlementCandidate)
    (Feasible : SettlementCandidate -> Prop) : Prop :=
  ∀ candidate, Feasible candidate -> candidate ∈ candidates

def SoundAuditSet
    (candidates : List SettlementCandidate)
    (Feasible : SettlementCandidate -> Prop) : Prop :=
  ∀ candidate, candidate ∈ candidates -> Feasible candidate

def ExactAuditSet
    (candidates : List SettlementCandidate)
    (Feasible : SettlementCandidate -> Prop) : Prop :=
  CompleteAuditSet candidates Feasible ∧ SoundAuditSet candidates Feasible

/--
Global weak optimality over a feasibility predicate.

This definition includes winner feasibility. A candidate that dominates all
feasible candidates but is itself infeasible is not a valid global winner.
-/
def GloballyWeaklyOptimal
    (winner : SettlementCandidate)
    (Feasible : SettlementCandidate -> Prop) : Prop :=
  Feasible winner ∧
    ∀ candidate, Feasible candidate -> WeaklyDominates winner candidate

/--
Certificate-style upper-bound check.

The verifier checks that the winner realizes the declared upper bounds and that
every audited candidate is below those bounds.
-/
def UpperBoundCertificateChecks
    (winner : SettlementCandidate)
    (volumeUpper surplusUpperAtWinnerVolume : Nat)
    (candidates : List SettlementCandidate) : Prop :=
  winner.volume = volumeUpper ∧
    winner.surplus = surplusUpperAtWinnerVolume ∧
    ∀ candidate, candidate ∈ candidates ->
      candidate.volume <= volumeUpper ∧
        (candidate.volume = volumeUpper ->
          candidate.surplus <= surplusUpperAtWinnerVolume)

/--
Runtime certificate checks also require the declared winner to be a member of
the audited candidate list.
-/
def UpperBoundCertificateChecksWithWinner
    (winner : SettlementCandidate)
    (volumeUpper surplusUpperAtWinnerVolume : Nat)
    (candidates : List SettlementCandidate) : Prop :=
  UpperBoundCertificateChecks winner volumeUpper surplusUpperAtWinnerVolume candidates ∧
    winner ∈ candidates

/--
If the finite audit-set certificate checks, the winner is weakly optimal in that
audited set.
-/
theorem upper_bound_certificate_implies_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates : List SettlementCandidate}
    (hCert :
      UpperBoundCertificateChecks
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        candidates) :
    WeaklyOptimalIn winner candidates := by
  unfold UpperBoundCertificateChecks WeaklyOptimalIn WeaklyDominates at *
  intro candidate hMember
  rcases hCert with ⟨hWinnerVolume, hWinnerSurplus, hAll⟩
  rcases hAll candidate hMember with ⟨hVolume, hSurplusAtUpper⟩
  constructor
  · simpa [hWinnerVolume] using hVolume
  · intro hEqualVolume
    have hEqualUpper : candidate.volume = volumeUpper := by
      simpa [hWinnerVolume] using hEqualVolume
    simpa [hWinnerSurplus] using hSurplusAtUpper hEqualUpper

/--
If the runtime-strengthened finite audit-set certificate checks, the declared
winner is both present and weakly optimal in that audited set.
-/
theorem upper_bound_certificate_with_winner_implies_present_and_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates : List SettlementCandidate}
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        candidates) :
    WeaklyOptimalIn winner candidates ∧ winner ∈ candidates := by
  rcases hCert with ⟨hUpper, hMember⟩
  exact ⟨upper_bound_certificate_implies_weak_optimal hUpper, hMember⟩

/--
Audited-set optimality lifts to global optimality only through an explicit
completeness bridge.
-/
theorem complete_audit_set_lifts_weak_optimal_to_global
    {winner : SettlementCandidate}
    {candidates : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hWinnerFeasible : Feasible winner)
    (hComplete : CompleteAuditSet candidates Feasible)
    (hAudit : WeaklyOptimalIn winner candidates) :
    GloballyWeaklyOptimal winner Feasible := by
  unfold CompleteAuditSet WeaklyOptimalIn GloballyWeaklyOptimal at *
  constructor
  · exact hWinnerFeasible
  · intro candidate hFeasible
    exact hAudit candidate (hComplete candidate hFeasible)

/--
Global weak optimality transfers to a verifier-accepted candidate in the same
objective-equivalence class.
-/
theorem objective_equivalent_preserves_global_weak_optimal
    {winner equivalent : SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hEquivalent : ObjectiveEquivalent equivalent winner)
    (hEquivalentFeasible : Feasible equivalent)
    (hWinnerGlobal : GloballyWeaklyOptimal winner Feasible) :
    GloballyWeaklyOptimal equivalent Feasible := by
  unfold GloballyWeaklyOptimal at *
  rcases hWinnerGlobal with ⟨_, hWinnerDominates⟩
  constructor
  · exact hEquivalentFeasible
  · intro candidate hFeasible
    exact
      objective_equivalent_transfers_weak_dominance
        hEquivalent
        (hWinnerDominates candidate hFeasible)

/--
A runtime-strengthened upper-bound certificate gives global weak optimality
only when paired with winner feasibility and audit-set completeness.
-/
theorem complete_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hWinnerFeasible : Feasible winner)
    (hComplete : CompleteAuditSet candidates Feasible)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        candidates) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ candidates := by
  rcases upper_bound_certificate_with_winner_implies_present_and_weak_optimal hCert with
    ⟨hAudit, hMember⟩
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hMember⟩

/--
An exact audit set removes the need for a separate winner-feasibility premise:
if the winner is a member of a sound audited set, then it is feasible.
-/
theorem exact_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet candidates Feasible)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        candidates) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ candidates := by
  rcases hExact with ⟨hComplete, hSound⟩
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hWinnerFeasible : Feasible winner :=
    hSound winner hWinnerMember
  exact
    complete_upper_bound_certificate_implies_global_weak_optimal
      hWinnerFeasible
      hComplete
      ⟨hUpper, hWinnerMember⟩

/--
If the certificate selects one representative of a tied objective class, any
verifier-accepted audited candidate with the same objective is globally weakly
optimal over the same exact finite family.
-/
theorem objective_equivalent_exact_upper_bound_certificate_implies_global_weak_optimal
    {winner equivalent : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet candidates Feasible)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        candidates)
    (hEquivalent : ObjectiveEquivalent equivalent winner)
    (hEquivalentMember : equivalent ∈ candidates) :
    GloballyWeaklyOptimal equivalent Feasible ∧ equivalent ∈ candidates := by
  rcases exact_upper_bound_certificate_implies_global_weak_optimal hExact hCert with
    ⟨hWinnerGlobal, _⟩
  rcases hExact with ⟨_, hSound⟩
  have hEquivalentFeasible : Feasible equivalent :=
    hSound equivalent hEquivalentMember
  exact
    ⟨objective_equivalent_preserves_global_weak_optimal
      hEquivalent
      hEquivalentFeasible
      hWinnerGlobal,
      hEquivalentMember⟩

/-- Reordering a complete audit set preserves completeness. -/
theorem complete_audit_set_of_perm
    {candidates ordered : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hComplete : CompleteAuditSet candidates Feasible)
    (hPerm : ordered.Perm candidates) :
    CompleteAuditSet ordered Feasible := by
  unfold CompleteAuditSet at *
  intro candidate hFeasible
  exact (hPerm.mem_iff).2 (hComplete candidate hFeasible)

/-- Reordering a sound audit set preserves soundness. -/
theorem sound_audit_set_of_perm
    {candidates ordered : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hSound : SoundAuditSet candidates Feasible)
    (hPerm : ordered.Perm candidates) :
    SoundAuditSet ordered Feasible := by
  unfold SoundAuditSet at *
  intro candidate hMember
  exact hSound candidate ((hPerm.mem_iff).1 hMember)

/-- Reordering an exact audit set preserves exactness. -/
theorem exact_audit_set_of_perm
    {candidates ordered : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet candidates Feasible)
    (hPerm : ordered.Perm candidates) :
    ExactAuditSet ordered Feasible := by
  rcases hExact with ⟨hComplete, hSound⟩
  exact
    ⟨complete_audit_set_of_perm hComplete hPerm,
      sound_audit_set_of_perm hSound hPerm⟩

/--
Full deterministic fallback is exhaustive-equivalent when the checked order is a
permutation of the original finite candidate set.
-/
def FullFallbackEquivalentOrder
    (candidates ordered : List SettlementCandidate) : Prop :=
  ordered.Perm candidates

/--
An advisory repair or neighborhood generator may expand a base candidate list.
This relation records the proof obligation that every base candidate remains in
the augmented list.
-/
def CandidateSubset
    (base augmented : List SettlementCandidate) : Prop :=
  ∀ candidate, candidate ∈ base -> candidate ∈ augmented

/--
An advisory repair selector may choose a smaller proposal set than the full
neighborhood generator, but it must preserve the base candidate list. This
definition names the selector-specific proof obligation used by ZenoEnergy.
-/
def AdvisorySelectedRepairSet
    (base selected : List SettlementCandidate) : Prop :=
  CandidateSubset base selected

/-- Candidate-subset inclusion is reflexive. -/
theorem candidate_subset_refl
    (candidates : List SettlementCandidate) :
    CandidateSubset candidates candidates := by
  unfold CandidateSubset
  intro candidate hMember
  exact hMember

/-- Candidate-subset inclusion composes. -/
theorem candidate_subset_trans
    {base middle augmented : List SettlementCandidate}
    (hBaseMiddle : CandidateSubset base middle)
    (hMiddleAugmented : CandidateSubset middle augmented) :
    CandidateSubset base augmented := by
  unfold CandidateSubset at *
  intro candidate hMember
  exact hMiddleAugmented candidate (hBaseMiddle candidate hMember)

/-- The selector-specific base-preservation obligation is exactly subset inclusion. -/
theorem advisory_selected_repair_set_implies_candidate_subset
    {base selected : List SettlementCandidate}
    (hSelected : AdvisorySelectedRepairSet base selected) :
    CandidateSubset base selected := by
  exact hSelected

/--
If a verifier-backed winner is weakly optimal in an augmented neighborhood list,
then it is weakly optimal over any preserved base list.
-/
theorem augmented_superset_weak_optimal_implies_base_weak_optimal
    {winner : SettlementCandidate}
    {base augmented : List SettlementCandidate}
    (hSubset : CandidateSubset base augmented)
    (hAugmentedOptimal : WeaklyOptimalIn winner augmented) :
    WeaklyOptimalIn winner base := by
  unfold CandidateSubset WeaklyOptimalIn at *
  intro candidate hBaseMember
  exact hAugmentedOptimal candidate (hSubset candidate hBaseMember)

/--
An upper-bound certificate over a neighborhood-augmented list proves dominance
over the original base list when the base list is preserved as a subset.
-/
theorem augmented_superset_upper_bound_certificate_implies_base_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {base augmented : List SettlementCandidate}
    (hSubset : CandidateSubset base augmented)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        augmented) :
    WeaklyOptimalIn winner base ∧ winner ∈ augmented := by
  rcases upper_bound_certificate_with_winner_implies_present_and_weak_optimal hCert with
    ⟨hAugmentedOptimal, hWinnerMember⟩
  exact
    ⟨augmented_superset_weak_optimal_implies_base_weak_optimal
      hSubset
      hAugmentedOptimal,
      hWinnerMember⟩

/--
A repair selector may reduce the added proposal set. If its selected set
preserves the base list, any verifier upper-bound certificate over the selected
set still proves weak optimality over the preserved base list.
-/
theorem advisory_selected_repair_set_upper_bound_certificate_implies_base_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {base selected : List SettlementCandidate}
    (hSelected : AdvisorySelectedRepairSet base selected)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        selected) :
    WeaklyOptimalIn winner base ∧ winner ∈ selected := by
  exact
    augmented_superset_upper_bound_certificate_implies_base_weak_optimal
      (base := base)
      (augmented := selected)
      (hSubset := advisory_selected_repair_set_implies_candidate_subset hSelected)
      hCert

/-- Full fallback preserves candidate membership exactly. -/
theorem full_fallback_equivalent_order_preserves_membership_iff
    {candidate : SettlementCandidate}
    {candidates ordered : List SettlementCandidate}
    (hEquivalent : FullFallbackEquivalentOrder candidates ordered) :
    candidate ∈ ordered ↔ candidate ∈ candidates := by
  unfold FullFallbackEquivalentOrder at hEquivalent
  exact hEquivalent.mem_iff

/--
Full fallback preserves audited weak optimality exactly. The candidate order may
change, but the finite set checked by the verifier is the same.
-/
theorem full_fallback_equivalent_order_preserves_weak_optimality_iff
    {winner : SettlementCandidate}
    {candidates ordered : List SettlementCandidate}
    (hEquivalent : FullFallbackEquivalentOrder candidates ordered) :
    WeaklyOptimalIn winner ordered ↔ WeaklyOptimalIn winner candidates := by
  unfold FullFallbackEquivalentOrder at hEquivalent
  constructor
  · intro hOptimal candidate hMember
    exact hOptimal candidate ((hEquivalent.mem_iff).2 hMember)
  · intro hOptimal candidate hMember
    exact hOptimal candidate ((hEquivalent.mem_iff).1 hMember)

/--
A deterministic early-stop certificate over a ranked prefix must cover both the
checked candidates and the unchecked suffix. The model can choose the schedule,
but the stopping reason is the verifier-facing dominance claim.
-/
def CheckedStopCertificate
    (winner : SettlementCandidate)
    (checked suffix : List SettlementCandidate) : Prop :=
  winner ∈ checked ∧
    WeaklyOptimalIn winner checked ∧
    WeaklyOptimalIn winner suffix

/--
If a checked-stop certificate covers the checked candidates and unchecked
suffix, the winner is weakly optimal over their concatenation.
-/
theorem checked_stop_certificate_implies_concat_weak_optimal
    {winner : SettlementCandidate}
    {checked suffix : List SettlementCandidate}
    (hStop : CheckedStopCertificate winner checked suffix) :
    WeaklyOptimalIn winner (checked ++ suffix) ∧
      winner ∈ checked ++ suffix := by
  unfold CheckedStopCertificate at hStop
  rcases hStop with ⟨hWinnerChecked, hCheckedOptimal, hSuffixOptimal⟩
  constructor
  · unfold WeaklyOptimalIn at *
    intro candidate hMember
    rcases (List.mem_append.mp hMember) with hCheckedMember | hSuffixMember
    · exact hCheckedOptimal candidate hCheckedMember
    · exact hSuffixOptimal candidate hSuffixMember
  · exact List.mem_append.mpr (Or.inl hWinnerChecked)

/--
If the checked candidates plus unchecked suffix are a permutation of the full
finite candidate list, a deterministic checked-stop certificate proves audited
weak optimality over the full list.
-/
theorem checked_stop_certificate_with_full_permutation_implies_full_weak_optimal
    {winner : SettlementCandidate}
    {checked suffix full : List SettlementCandidate}
    (hStop : CheckedStopCertificate winner checked suffix)
    (hPerm : (checked ++ suffix).Perm full) :
    WeaklyOptimalIn winner full ∧ winner ∈ full := by
  rcases checked_stop_certificate_implies_concat_weak_optimal hStop with
    ⟨hConcatOptimal, hWinnerConcat⟩
  constructor
  · unfold WeaklyOptimalIn at *
    intro candidate hMemberFull
    exact hConcatOptimal candidate ((hPerm.mem_iff).2 hMemberFull)
  · exact (hPerm.mem_iff).1 hWinnerConcat

/--
Checked stopping lifts to global weak optimality only when the full finite
candidate list is an exact audit set for the feasibility predicate.
-/
theorem checked_stop_certificate_with_exact_full_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {checked suffix full : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet full Feasible)
    (hStop : CheckedStopCertificate winner checked suffix)
    (hPerm : (checked ++ suffix).Perm full) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ full := by
  rcases hExact with ⟨hComplete, hSound⟩
  rcases checked_stop_certificate_with_full_permutation_implies_full_weak_optimal
      hStop
      hPerm with
    ⟨hFullOptimal, hWinnerFull⟩
  have hWinnerFeasible : Feasible winner :=
    hSound winner hWinnerFull
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hFullOptimal,
      hWinnerFull⟩

/--
A verifier certificate over any advisory ordering of an exact audit set still
proves global weak optimality over the same feasibility predicate.

The advisory model can choose the order. The proof obligation stays attached to
the deterministic verifier certificate over an exact candidate set.
-/
theorem reordered_exact_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates ordered : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet candidates Feasible)
    (hPerm : ordered.Perm candidates)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        ordered) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ ordered := by
  exact
    exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := ordered)
      (Feasible := Feasible)
      (exact_audit_set_of_perm hExact hPerm)
      hCert

/--
Advisory ordering may expose an objective-equivalent candidate before the
hash-selected representative. If that candidate is present in the verifier's
ordered exact audit set, the same deterministic certificate proves it is an
equivalent global weak optimum.
-/
theorem objective_equivalent_reordered_exact_upper_bound_certificate_implies_global_weak_optimal
    {winner equivalent : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {candidates ordered : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hExact : ExactAuditSet candidates Feasible)
    (hPerm : ordered.Perm candidates)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        ordered)
    (hEquivalent : ObjectiveEquivalent equivalent winner)
    (hEquivalentMember : equivalent ∈ ordered) :
    GloballyWeaklyOptimal equivalent Feasible ∧ equivalent ∈ ordered := by
  exact
    objective_equivalent_exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := ordered)
      (Feasible := Feasible)
      (hExact := exact_audit_set_of_perm hExact hPerm)
      (hCert := hCert)
      hEquivalent
      hEquivalentMember

/--
Generated candidate data has the same mathematical standing as any other audit
set exactly when it is sound and complete for the feasibility predicate it
claims to represent.
-/
def GeneratedCorpusExact
    (generated : List SettlementCandidate)
    (Feasible : SettlementCandidate -> Prop) : Prop :=
  ExactAuditSet generated Feasible

/--
If a generated corpus is exact for a candidate family, verifier upper-bound
checks over that corpus lift to global weak optimality for that family.
-/
theorem generated_corpus_exact_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {generated : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hGeneratedExact : GeneratedCorpusExact generated Feasible)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        generated) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ generated := by
  exact
    exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := generated)
      (Feasible := Feasible)
      hGeneratedExact
      hCert

/--
Dominance pruning can replace full audit-set enumeration.

If the full list covers every feasible candidate, the pruned list contains only
feasible candidates, and every full-list candidate is weakly dominated by some
pruned representative, then a verifier certificate over the pruned list proves
global weak optimality over the original feasibility predicate.
-/
theorem dominance_cover_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume : Nat}
    {full pruned : List SettlementCandidate}
    {Feasible : SettlementCandidate -> Prop}
    (hFullComplete : CompleteAuditSet full Feasible)
    (hPrunedSound : SoundAuditSet pruned Feasible)
    (hCover : DominanceCover pruned full)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        pruned) :
    GloballyWeaklyOptimal winner Feasible ∧ winner ∈ pruned := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hWinnerFeasible : Feasible winner :=
    hPrunedSound winner hWinnerMember
  have hPrunedOptimal : WeaklyOptimalIn winner pruned :=
    upper_bound_certificate_implies_weak_optimal hUpper
  constructor
  · unfold GloballyWeaklyOptimal
    constructor
    · exact hWinnerFeasible
    · intro candidate hFeasible
      rcases hCover candidate (hFullComplete candidate hFeasible) with
        ⟨representative, hRepresentativeMember, hRepresentativeDominates⟩
      exact
        weaklyDominates_trans
          (hPrunedOptimal representative hRepresentativeMember)
          hRepresentativeDominates
  · exact hWinnerMember

/-- Integer uniform price ratio used by the bounded price-grid model. -/
structure Price where
  num : Nat
  den : Nat
deriving DecidableEq, Repr

/-- Price is inside the configured inclusive integer grid bounds. -/
def PriceInGridBounds
    (maxNum maxDen : Nat)
    (price : Price) : Prop :=
  price.num <= maxNum ∧ price.den <= maxDen

/--
Canonical bounded integer price grid.

The grid intentionally enumerates all pairs up to the configured bounds by
structural list ranges. Runtime validity predicates, such as positive
denominator or reduced ratio, can be layered on top. Completeness over this
superset is enough for an exact finite audit set once candidate feasibility
filters invalid prices.
-/
def priceGrid (maxNum maxDen : Nat) : List Price :=
  List.flatMap
    (fun num =>
      (List.range (maxDen + 1)).map fun den =>
        { num := num, den := den })
    (List.range (maxNum + 1))

/-- Candidate list produced by scoring every bounded grid price. -/
def priceGridCandidates
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate) : List SettlementCandidate :=
  (priceGrid maxNum maxDen).map scoreAt

/-- Candidate is generated by at least one bounded grid price. -/
def FeasibleGridCandidate
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price, PriceInGridBounds maxNum maxDen price ∧ candidate = scoreAt price

def PriceInPositiveGridBounds
    (maxNum maxDen : Nat)
    (price : Price) : Prop :=
  0 < price.num ∧ price.num <= maxNum ∧ 0 < price.den ∧ price.den <= maxDen

def positivePriceGrid (maxNum maxDen : Nat) : List Price :=
  (priceGrid maxNum maxDen).filter fun price =>
    decide (0 < price.num ∧ 0 < price.den)

def positivePriceGridCandidates
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate) : List SettlementCandidate :=
  (positivePriceGrid maxNum maxDen).map scoreAt

def FeasiblePositiveGridCandidate
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price, PriceInPositiveGridBounds maxNum maxDen price ∧ candidate = scoreAt price

def priceReducedBool (price : Price) : Bool :=
  Nat.gcd price.num price.den == 1

def PriceReduced (price : Price) : Prop :=
  priceReducedBool price = true

def PriceInCanonicalGridBounds
    (maxNum maxDen : Nat)
    (price : Price) : Prop :=
  PriceInPositiveGridBounds maxNum maxDen price ∧ PriceReduced price

def canonicalPriceGrid (maxNum maxDen : Nat) : List Price :=
  (positivePriceGrid maxNum maxDen).filter priceReducedBool

def canonicalPriceGridCandidates
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate) : List SettlementCandidate :=
  (canonicalPriceGrid maxNum maxDen).map scoreAt

def FeasibleCanonicalGridCandidate
    (maxNum maxDen : Nat)
    (scoreAt : Price -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price, PriceInCanonicalGridBounds maxNum maxDen price ∧ candidate = scoreAt price

/--
Every bounded integer price pair is present in the canonical finite grid.

This is the induction-style completeness bridge: the theorem is universal over
all natural grid bounds, so one proof covers the infinite family of deployed
finite grids.
-/
theorem priceGrid_complete
    {maxNum maxDen : Nat}
    {price : Price}
    (hBounds : PriceInGridBounds maxNum maxDen price) :
    price ∈ priceGrid maxNum maxDen := by
  rcases hBounds with ⟨hNum, hDen⟩
  unfold priceGrid
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact
    ⟨price.num,
      Nat.lt_succ_of_le hNum,
      price.den,
      Nat.lt_succ_of_le hDen,
      by cases price; rfl⟩

theorem priceGrid_sound
    {maxNum maxDen : Nat}
    {price : Price}
    (hMember : price ∈ priceGrid maxNum maxDen) :
    PriceInGridBounds maxNum maxDen price := by
  unfold priceGrid at hMember
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hMember
  rcases hMember with ⟨num, hNum, den, hDen, hEq⟩
  cases hEq
  exact ⟨Nat.le_of_lt_succ hNum, Nat.le_of_lt_succ hDen⟩

/-- Scoring preserves price-grid completeness at the candidate-list level. -/
theorem priceGridCandidates_complete
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    {price : Price}
    (hBounds : PriceInGridBounds maxNum maxDen price) :
    scoreAt price ∈ priceGridCandidates maxNum maxDen scoreAt := by
  unfold priceGridCandidates
  exact List.mem_map.mpr ⟨price, priceGrid_complete hBounds, rfl⟩

/--
The scored bounded price grid is a complete audit set for every candidate that
can be generated by a bounded grid price.
-/
theorem priceGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    CompleteAuditSet
      (priceGridCandidates maxNum maxDen scoreAt)
      (FeasibleGridCandidate maxNum maxDen scoreAt) := by
  unfold CompleteAuditSet FeasibleGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, hBounds, hCandidate⟩
  rw [hCandidate]
  exact priceGridCandidates_complete hBounds

theorem priceGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    SoundAuditSet
      (priceGridCandidates maxNum maxDen scoreAt)
      (FeasibleGridCandidate maxNum maxDen scoreAt) := by
  unfold SoundAuditSet FeasibleGridCandidate priceGridCandidates
  intro candidate hMember
  rcases List.mem_map.mp hMember with ⟨price, hPriceMember, hCandidate⟩
  exact ⟨price, priceGrid_sound hPriceMember, hCandidate.symm⟩

theorem priceGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    ExactAuditSet
      (priceGridCandidates maxNum maxDen scoreAt)
      (FeasibleGridCandidate maxNum maxDen scoreAt) :=
  ⟨priceGridCandidates_complete_audit_set, priceGridCandidates_sound_audit_set⟩

theorem positivePriceGrid_complete
    {maxNum maxDen : Nat}
    {price : Price}
    (hBounds : PriceInPositiveGridBounds maxNum maxDen price) :
    price ∈ positivePriceGrid maxNum maxDen := by
  rcases hBounds with ⟨hNumPositive, hNumBound, hDenPositive, hDenBound⟩
  unfold positivePriceGrid
  exact
    List.mem_filter.mpr
      ⟨priceGrid_complete ⟨hNumBound, hDenBound⟩,
        by simpa using And.intro hNumPositive hDenPositive⟩

theorem positivePriceGrid_sound
    {maxNum maxDen : Nat}
    {price : Price}
    (hMember : price ∈ positivePriceGrid maxNum maxDen) :
    PriceInPositiveGridBounds maxNum maxDen price := by
  unfold positivePriceGrid at hMember
  rcases List.mem_filter.mp hMember with ⟨hGridMember, hPositive⟩
  rcases priceGrid_sound hGridMember with ⟨hNumBound, hDenBound⟩
  have hPositivePair : 0 < price.num ∧ 0 < price.den := by
    exact of_decide_eq_true hPositive
  exact ⟨hPositivePair.1, hNumBound, hPositivePair.2, hDenBound⟩

theorem positivePriceGridCandidates_complete
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    {price : Price}
    (hBounds : PriceInPositiveGridBounds maxNum maxDen price) :
    scoreAt price ∈ positivePriceGridCandidates maxNum maxDen scoreAt := by
  unfold positivePriceGridCandidates
  exact List.mem_map.mpr ⟨price, positivePriceGrid_complete hBounds, rfl⟩

theorem positivePriceGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    CompleteAuditSet
      (positivePriceGridCandidates maxNum maxDen scoreAt)
      (FeasiblePositiveGridCandidate maxNum maxDen scoreAt) := by
  unfold CompleteAuditSet FeasiblePositiveGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, hBounds, hCandidate⟩
  rw [hCandidate]
  exact positivePriceGridCandidates_complete hBounds

theorem positivePriceGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    SoundAuditSet
      (positivePriceGridCandidates maxNum maxDen scoreAt)
      (FeasiblePositiveGridCandidate maxNum maxDen scoreAt) := by
  unfold SoundAuditSet FeasiblePositiveGridCandidate positivePriceGridCandidates
  intro candidate hMember
  rcases List.mem_map.mp hMember with ⟨price, hPriceMember, hCandidate⟩
  exact ⟨price, positivePriceGrid_sound hPriceMember, hCandidate.symm⟩

theorem positivePriceGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    ExactAuditSet
      (positivePriceGridCandidates maxNum maxDen scoreAt)
      (FeasiblePositiveGridCandidate maxNum maxDen scoreAt) :=
  ⟨positivePriceGridCandidates_complete_audit_set, positivePriceGridCandidates_sound_audit_set⟩

theorem canonicalPriceGrid_complete
    {maxNum maxDen : Nat}
    {price : Price}
    (hBounds : PriceInCanonicalGridBounds maxNum maxDen price) :
    price ∈ canonicalPriceGrid maxNum maxDen := by
  rcases hBounds with ⟨hPositiveBounds, hReduced⟩
  unfold canonicalPriceGrid
  exact
    List.mem_filter.mpr
      ⟨positivePriceGrid_complete hPositiveBounds,
        by simpa [PriceReduced] using hReduced⟩

theorem canonicalPriceGrid_sound
    {maxNum maxDen : Nat}
    {price : Price}
    (hMember : price ∈ canonicalPriceGrid maxNum maxDen) :
    PriceInCanonicalGridBounds maxNum maxDen price := by
  unfold canonicalPriceGrid at hMember
  rcases List.mem_filter.mp hMember with ⟨hPositiveMember, hReduced⟩
  exact ⟨positivePriceGrid_sound hPositiveMember, by simpa [PriceReduced] using hReduced⟩

theorem canonicalPriceGridCandidates_complete
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    {price : Price}
    (hBounds : PriceInCanonicalGridBounds maxNum maxDen price) :
    scoreAt price ∈ canonicalPriceGridCandidates maxNum maxDen scoreAt := by
  unfold canonicalPriceGridCandidates
  exact List.mem_map.mpr ⟨price, canonicalPriceGrid_complete hBounds, rfl⟩

theorem canonicalPriceGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    CompleteAuditSet
      (canonicalPriceGridCandidates maxNum maxDen scoreAt)
      (FeasibleCanonicalGridCandidate maxNum maxDen scoreAt) := by
  unfold CompleteAuditSet FeasibleCanonicalGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, hBounds, hCandidate⟩
  rw [hCandidate]
  exact canonicalPriceGridCandidates_complete hBounds

theorem canonicalPriceGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    SoundAuditSet
      (canonicalPriceGridCandidates maxNum maxDen scoreAt)
      (FeasibleCanonicalGridCandidate maxNum maxDen scoreAt) := by
  unfold SoundAuditSet FeasibleCanonicalGridCandidate canonicalPriceGridCandidates
  intro candidate hMember
  rcases List.mem_map.mp hMember with ⟨price, hPriceMember, hCandidate⟩
  exact ⟨price, canonicalPriceGrid_sound hPriceMember, hCandidate.symm⟩

theorem canonicalPriceGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate} :
    ExactAuditSet
      (canonicalPriceGridCandidates maxNum maxDen scoreAt)
      (FeasibleCanonicalGridCandidate maxNum maxDen scoreAt) :=
  ⟨canonicalPriceGridCandidates_complete_audit_set, canonicalPriceGridCandidates_sound_audit_set⟩

/--
A runtime-strengthened upper-bound certificate over the complete bounded
price-grid candidate list proves global weak optimality over all candidates
generated by that grid.
-/
theorem price_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    (hWinnerFeasible : FeasibleGridCandidate maxNum maxDen scoreAt winner)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (priceGridCandidates maxNum maxDen scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasibleGridCandidate maxNum maxDen scoreAt) ∧
      winner ∈ priceGridCandidates maxNum maxDen scoreAt := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hAudit :
      WeaklyOptimalIn
        winner
        (priceGridCandidates maxNum maxDen scoreAt) :=
    upper_bound_certificate_implies_weak_optimal hUpper
  have hComplete :
      CompleteAuditSet
        (priceGridCandidates maxNum maxDen scoreAt)
        (FeasibleGridCandidate maxNum maxDen scoreAt) :=
    priceGridCandidates_complete_audit_set
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hWinnerMember⟩

theorem positive_price_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    (hWinnerFeasible : FeasiblePositiveGridCandidate maxNum maxDen scoreAt winner)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (positivePriceGridCandidates maxNum maxDen scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasiblePositiveGridCandidate maxNum maxDen scoreAt) ∧
      winner ∈ positivePriceGridCandidates maxNum maxDen scoreAt := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hAudit :
      WeaklyOptimalIn
        winner
        (positivePriceGridCandidates maxNum maxDen scoreAt) :=
    upper_bound_certificate_implies_weak_optimal hUpper
  have hComplete :
      CompleteAuditSet
        (positivePriceGridCandidates maxNum maxDen scoreAt)
        (FeasiblePositiveGridCandidate maxNum maxDen scoreAt) :=
    positivePriceGridCandidates_complete_audit_set
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hWinnerMember⟩

theorem canonical_price_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {scoreAt : Price -> SettlementCandidate}
    (hWinnerFeasible : FeasibleCanonicalGridCandidate maxNum maxDen scoreAt winner)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (canonicalPriceGridCandidates maxNum maxDen scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasibleCanonicalGridCandidate maxNum maxDen scoreAt) ∧
      winner ∈ canonicalPriceGridCandidates maxNum maxDen scoreAt := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hAudit :
      WeaklyOptimalIn
        winner
        (canonicalPriceGridCandidates maxNum maxDen scoreAt) :=
    upper_bound_certificate_implies_weak_optimal hUpper
  have hComplete :
      CompleteAuditSet
        (canonicalPriceGridCandidates maxNum maxDen scoreAt)
        (FeasibleCanonicalGridCandidate maxNum maxDen scoreAt) :=
    canonicalPriceGridCandidates_complete_audit_set
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hWinnerMember⟩

/--
A bounded partial-fill plan is the non-price part of a UPBA v2 candidate.

The runtime certificate names concrete fill amounts per admitted intent. This
abstract model only needs a finite plan identity; the deterministic scorer
interprets the plan together with a price.
-/
structure PartialFillPlan where
  planId : Nat
deriving DecidableEq, Repr

/--
Candidate list generated by every canonical bounded-grid price paired with
every admitted bounded partial-fill plan.
-/
def partialFillCanonicalGridCandidates
    (maxNum maxDen : Nat)
    (plans : List PartialFillPlan)
    (scoreAt : Price -> PartialFillPlan -> SettlementCandidate) : List SettlementCandidate :=
  (canonicalPriceGrid maxNum maxDen).flatMap fun price =>
    plans.map fun plan =>
      scoreAt price plan

/-- Candidate is generated by one canonical bounded price and one admitted partial-fill plan. -/
def FeasiblePartialFillCanonicalGridCandidate
    (maxNum maxDen : Nat)
    (plans : List PartialFillPlan)
    (scoreAt : Price -> PartialFillPlan -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price plan,
    PriceInCanonicalGridBounds maxNum maxDen price ∧
      plan ∈ plans ∧
      candidate = scoreAt price plan

theorem partialFillCanonicalGridCandidates_complete
    {maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    {price : Price}
    {plan : PartialFillPlan}
    (hPrice : PriceInCanonicalGridBounds maxNum maxDen price)
    (hPlan : plan ∈ plans) :
    scoreAt price plan ∈
      partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt := by
  unfold partialFillCanonicalGridCandidates
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨price, canonicalPriceGrid_complete hPrice, plan, hPlan, rfl⟩

theorem partialFillCanonicalGridCandidates_sound
    {maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    {candidate : SettlementCandidate}
    (hMember :
      candidate ∈ partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt) :
    FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt candidate := by
  unfold partialFillCanonicalGridCandidates at hMember
  simp only [List.mem_flatMap, List.mem_map] at hMember
  rcases hMember with ⟨price, hPriceMember, plan, hPlanMember, hCandidate⟩
  exact
    ⟨price,
      plan,
      canonicalPriceGrid_sound hPriceMember,
      hPlanMember,
      hCandidate.symm⟩

theorem partialFillCanonicalGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate} :
    CompleteAuditSet
      (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) := by
  unfold CompleteAuditSet FeasiblePartialFillCanonicalGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, plan, hPrice, hPlan, hCandidate⟩
  rw [hCandidate]
  exact partialFillCanonicalGridCandidates_complete hPrice hPlan

theorem partialFillCanonicalGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate} :
    SoundAuditSet
      (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) := by
  unfold SoundAuditSet
  intro candidate hMember
  exact partialFillCanonicalGridCandidates_sound hMember

theorem partialFillCanonicalGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate} :
    ExactAuditSet
      (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) :=
  ⟨partialFillCanonicalGridCandidates_complete_audit_set,
    partialFillCanonicalGridCandidates_sound_audit_set⟩

/--
UPBA v2 partial-fill bridge.

If the deployed finite audit set enumerates every canonical bounded-grid price
and every admitted bounded partial-fill plan, then the same upper-bound
certificate predicate proves global weak optimality over that bounded v2
candidate family.
-/
theorem upba_v2_partial_fill_bounded_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    (hWinnerFeasible :
      FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt winner)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hAudit :
      WeaklyOptimalIn
        winner
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt) :=
    upper_bound_certificate_implies_weak_optimal hUpper
  have hComplete :
      CompleteAuditSet
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
        (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) :=
    partialFillCanonicalGridCandidates_complete_audit_set
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hWinnerMember⟩

/--
UPBA v2 advisory-order bridge.

If an energy scorer only reorders the exact bounded-grid partial-fill candidate
set, then a verifier upper-bound certificate over that reordered list proves the
same bounded global weak optimality claim.
-/
theorem upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    {ordered : List SettlementCandidate}
    (hPerm :
      ordered.Perm
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt))
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        ordered) :
    GloballyWeaklyOptimal
      winner
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ ordered := by
  exact
    reordered_exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (ordered := ordered)
      (Feasible := FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt)
      partialFillCanonicalGridCandidates_exact_audit_set
      hPerm
      hCert

/--
UPBA v2 hard-barrier hybrid-order bridge.

A hard-barrier hybrid scorer is still advisory when it only permutes the exact
bounded-grid partial-fill candidate set. The deterministic verifier certificate
therefore proves the same bounded global weak optimality claim.
-/
theorem upba_v2_hard_barrier_hybrid_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    {ordered : List SettlementCandidate}
    (hPerm :
      ordered.Perm
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt))
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        ordered) :
    GloballyWeaklyOptimal
      winner
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ ordered := by
  exact
    upba_v2_advisory_reordered_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
      (ordered := ordered)
      hPerm
      hCert

/--
UPBA v2 dominance-pruned bridge.

The pruned list may be smaller than the complete bounded-grid partial-fill
candidate set. The extra proof obligation is a dominance cover showing that each
full-domain candidate is weakly dominated by some retained feasible candidate.
-/
theorem upba_v2_dominance_pruned_partial_fill_bounded_grid_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List PartialFillPlan}
    {scoreAt : Price -> PartialFillPlan -> SettlementCandidate}
    {pruned : List SettlementCandidate}
    (hPrunedSound :
      SoundAuditSet
        pruned
        (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt))
    (hCover :
      DominanceCover
        pruned
        (partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt))
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        pruned) :
    GloballyWeaklyOptimal
      winner
      (FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ pruned := by
  exact
    dominance_cover_upper_bound_certificate_implies_global_weak_optimal
      (full := partialFillCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (pruned := pruned)
      (Feasible := FeasiblePartialFillCanonicalGridCandidate maxNum maxDen plans scoreAt)
      partialFillCanonicalGridCandidates_complete_audit_set
      hPrunedSound
      hCover
      hCert

/--
A bounded exact-out fill plan is the non-price part of a UPBA v3 candidate.

The runtime certificate fixes full exact-out fills. This model only needs a
finite plan identity; the deterministic scorer interprets the plan together with
a bounded-grid price.
-/
structure ExactOutFillPlan where
  planId : Nat
deriving DecidableEq, Repr

/--
Candidate list generated by every canonical bounded-grid price paired with
every admitted bounded exact-out fill plan.
-/
def exactOutCanonicalGridCandidates
    (maxNum maxDen : Nat)
    (plans : List ExactOutFillPlan)
    (scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate) : List SettlementCandidate :=
  (canonicalPriceGrid maxNum maxDen).flatMap fun price =>
    plans.map fun plan =>
      scoreAt price plan

/--
Candidate list for the current UPBA v3 full-fill exact-out surface.

The exact-out fill plan is fixed by the admitted intent set. The bounded search
axis is therefore the canonical price grid.
-/
def exactOutFullFillCanonicalGridCandidates
    (maxNum maxDen : Nat)
    (fullFillPlan : ExactOutFillPlan)
    (scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate) : List SettlementCandidate :=
  (canonicalPriceGrid maxNum maxDen).map fun price =>
    scoreAt price fullFillPlan

/-- Candidate is generated by one canonical bounded price and one admitted exact-out plan. -/
def FeasibleExactOutCanonicalGridCandidate
    (maxNum maxDen : Nat)
    (plans : List ExactOutFillPlan)
    (scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price plan,
    PriceInCanonicalGridBounds maxNum maxDen price ∧
      plan ∈ plans ∧
      candidate = scoreAt price plan

/-- Candidate is generated by one canonical bounded price and the fixed full-fill plan. -/
def FeasibleExactOutFullFillCanonicalGridCandidate
    (maxNum maxDen : Nat)
    (fullFillPlan : ExactOutFillPlan)
    (scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate)
    (candidate : SettlementCandidate) : Prop :=
  ∃ price,
    PriceInCanonicalGridBounds maxNum maxDen price ∧
      candidate = scoreAt price fullFillPlan

/--
The full-fill exact-out candidate list is the singleton-plan instance of the
general exact-out candidate list.
-/
theorem exactOutFullFillCanonicalGridCandidates_eq_singleton_plan
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt =
      exactOutCanonicalGridCandidates maxNum maxDen [fullFillPlan] scoreAt := by
  unfold exactOutFullFillCanonicalGridCandidates exactOutCanonicalGridCandidates
  induction canonicalPriceGrid maxNum maxDen with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]

/--
The full-fill feasible predicate is the singleton-plan instance of the general
exact-out feasible predicate.
-/
theorem feasibleExactOutFullFill_iff_singleton_plan
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    {candidate : SettlementCandidate} :
    FeasibleExactOutFullFillCanonicalGridCandidate
        maxNum
        maxDen
        fullFillPlan
        scoreAt
        candidate ↔
      FeasibleExactOutCanonicalGridCandidate
        maxNum
        maxDen
        [fullFillPlan]
        scoreAt
        candidate := by
  constructor
  · intro hFeasible
    rcases hFeasible with ⟨price, hPrice, hCandidate⟩
    exact ⟨price, fullFillPlan, hPrice, by simp, hCandidate⟩
  · intro hFeasible
    rcases hFeasible with ⟨price, plan, hPrice, hPlan, hCandidate⟩
    simp only [List.mem_singleton] at hPlan
    subst plan
    exact ⟨price, hPrice, hCandidate⟩

theorem exactOutCanonicalGridCandidates_complete
    {maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    {price : Price}
    {plan : ExactOutFillPlan}
    (hPrice : PriceInCanonicalGridBounds maxNum maxDen price)
    (hPlan : plan ∈ plans) :
    scoreAt price plan ∈
      exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt := by
  unfold exactOutCanonicalGridCandidates
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨price, canonicalPriceGrid_complete hPrice, plan, hPlan, rfl⟩

theorem exactOutCanonicalGridCandidates_sound
    {maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    {candidate : SettlementCandidate}
    (hMember :
      candidate ∈ exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt) :
    FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt candidate := by
  unfold exactOutCanonicalGridCandidates at hMember
  simp only [List.mem_flatMap, List.mem_map] at hMember
  rcases hMember with ⟨price, hPriceMember, plan, hPlanMember, hCandidate⟩
  exact
    ⟨price,
      plan,
      canonicalPriceGrid_sound hPriceMember,
      hPlanMember,
      hCandidate.symm⟩

theorem exactOutFullFillCanonicalGridCandidates_complete
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    {price : Price}
    (hPrice : PriceInCanonicalGridBounds maxNum maxDen price) :
    scoreAt price fullFillPlan ∈
      exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt := by
  unfold exactOutFullFillCanonicalGridCandidates
  exact List.mem_map.mpr ⟨price, canonicalPriceGrid_complete hPrice, rfl⟩

theorem exactOutFullFillCanonicalGridCandidates_sound
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    {candidate : SettlementCandidate}
    (hMember :
      candidate ∈
        exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt) :
    FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt candidate := by
  unfold exactOutFullFillCanonicalGridCandidates at hMember
  rcases List.mem_map.mp hMember with ⟨price, hPriceMember, hCandidate⟩
  exact ⟨price, canonicalPriceGrid_sound hPriceMember, hCandidate.symm⟩

theorem exactOutCanonicalGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    CompleteAuditSet
      (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) := by
  unfold CompleteAuditSet FeasibleExactOutCanonicalGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, plan, hPrice, hPlan, hCandidate⟩
  rw [hCandidate]
  exact exactOutCanonicalGridCandidates_complete hPrice hPlan

theorem exactOutCanonicalGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    SoundAuditSet
      (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) := by
  unfold SoundAuditSet
  intro candidate hMember
  exact exactOutCanonicalGridCandidates_sound hMember

theorem exactOutFullFillCanonicalGridCandidates_complete_audit_set
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    CompleteAuditSet
      (exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt)
      (FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt) := by
  unfold CompleteAuditSet FeasibleExactOutFullFillCanonicalGridCandidate
  intro candidate hFeasible
  rcases hFeasible with ⟨price, hPrice, hCandidate⟩
  rw [hCandidate]
  exact exactOutFullFillCanonicalGridCandidates_complete hPrice

theorem exactOutFullFillCanonicalGridCandidates_sound_audit_set
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    SoundAuditSet
      (exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt)
      (FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt) := by
  unfold SoundAuditSet
  intro candidate hMember
  exact exactOutFullFillCanonicalGridCandidates_sound hMember

theorem exactOutCanonicalGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    ExactAuditSet
      (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) :=
  ⟨exactOutCanonicalGridCandidates_complete_audit_set,
    exactOutCanonicalGridCandidates_sound_audit_set⟩

theorem exactOutFullFillCanonicalGridCandidates_exact_audit_set
    {maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate} :
    ExactAuditSet
      (exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt)
      (FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt) :=
  ⟨exactOutFullFillCanonicalGridCandidates_complete_audit_set,
    exactOutFullFillCanonicalGridCandidates_sound_audit_set⟩

/--
UPBA v3 exact-out bridge.

If the deployed finite audit set enumerates every canonical bounded-grid price
and every admitted bounded exact-out fill plan, then the same upper-bound
certificate predicate proves global weak optimality over that bounded v3
candidate family.
-/
theorem upba_v3_exact_out_bounded_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    (hWinnerFeasible :
      FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt winner)
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt := by
  rcases hCert with ⟨hUpper, hWinnerMember⟩
  have hAudit :
      WeaklyOptimalIn
        winner
        (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt) :=
    upper_bound_certificate_implies_weak_optimal hUpper
  have hComplete :
      CompleteAuditSet
        (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)
        (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) :=
    exactOutCanonicalGridCandidates_complete_audit_set
  exact
    ⟨complete_audit_set_lifts_weak_optimal_to_global
      hWinnerFeasible
      hComplete
      hAudit,
      hWinnerMember⟩

/--
UPBA v3 exact-out bridge with winner feasibility derived from the exact audited
candidate set.
-/
theorem upba_v3_exact_out_exact_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {plans : List ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt) ∧
      winner ∈ exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt := by
  exact
    exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := exactOutCanonicalGridCandidates maxNum maxDen plans scoreAt)
      (Feasible := FeasibleExactOutCanonicalGridCandidate maxNum maxDen plans scoreAt)
      exactOutCanonicalGridCandidates_exact_audit_set
      hCert

/--
UPBA v3 full-fill exact-out bridge.

For the current runtime surface, the exact-out fill plan is fixed by the
admitted intent set, so the complete audited domain is the canonical bounded
price grid scored with that one plan.
-/
theorem upba_v3_full_fill_exact_out_grid_upper_bound_certificate_implies_global_weak_optimal
    {winner : SettlementCandidate}
    {volumeUpper surplusUpperAtWinnerVolume maxNum maxDen : Nat}
    {fullFillPlan : ExactOutFillPlan}
    {scoreAt : Price -> ExactOutFillPlan -> SettlementCandidate}
    (hCert :
      UpperBoundCertificateChecksWithWinner
        winner
        volumeUpper
        surplusUpperAtWinnerVolume
        (exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt)) :
    GloballyWeaklyOptimal
      winner
      (FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt) ∧
      winner ∈ exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt := by
  exact
    exact_upper_bound_certificate_implies_global_weak_optimal
      (candidates := exactOutFullFillCanonicalGridCandidates maxNum maxDen fullFillPlan scoreAt)
      (Feasible :=
        FeasibleExactOutFullFillCanonicalGridCandidate maxNum maxDen fullFillPlan scoreAt)
      exactOutFullFillCanonicalGridCandidates_exact_audit_set
      hCert

/--
Negative boundary: audited-set optimality alone says nothing about a better
candidate omitted from the audited list.
-/
theorem audited_set_optimality_does_not_exclude_omitted_better_candidate :
    ∃ winner omitted candidates,
      WeaklyOptimalIn winner candidates ∧
        omitted ∉ candidates ∧
        ¬ WeaklyDominates winner omitted := by
  let winner : SettlementCandidate := { volume := 1, surplus := 0 }
  let omitted : SettlementCandidate := { volume := 2, surplus := 0 }
  exact
    ⟨winner,
      omitted,
      [winner],
      by
        intro candidate hMember
        simp only [List.mem_singleton] at hMember
        subst candidate
        unfold WeaklyDominates
        exact ⟨Nat.le_refl 1, by intro _; exact Nat.le_refl 0⟩,
      by decide,
      by
        intro hDominates
        exact Nat.not_succ_le_self 1 hDominates.1⟩

end UniformBatchOptimality
