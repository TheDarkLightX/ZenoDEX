/-!
# Uniform Batch Optimality Boundaries

This file captures two small optimality lemmas that are useful for UPBA v2
without claiming full auction optimality.

The first lemma is fixed-price aggregate volume optimality: after a uniform price
has determined acceptable demand and supply capacity, no aggregate feasible
settlement can match more than the smaller side.

The second lemma is certificate-facing: if a verifier checks upper bounds over a
finite audited candidate list, then the submitted candidate is weakly optimal in
that audited list by volume first and surplus second.

These theorems do not prove fair order inclusion, global price search
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

/-- Winner is weakly optimal inside a finite audited candidate list. -/
def WeaklyOptimalIn
    (winner : SettlementCandidate)
    (candidates : List SettlementCandidate) : Prop :=
  ∀ candidate, candidate ∈ candidates -> WeaklyDominates winner candidate

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

end UniformBatchOptimality
