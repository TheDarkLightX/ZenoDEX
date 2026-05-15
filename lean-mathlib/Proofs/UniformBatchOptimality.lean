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

/-- Winner is weakly optimal inside a finite audited candidate list. -/
def WeaklyOptimalIn
    (winner : SettlementCandidate)
    (candidates : List SettlementCandidate) : Prop :=
  ∀ candidate, candidate ∈ candidates -> WeaklyDominates winner candidate

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
  refine ⟨winner, omitted, [winner], ?_, ?_, ?_⟩
  · intro candidate hMember
    simp only [List.mem_singleton] at hMember
    subst candidate
    unfold WeaklyDominates
    exact ⟨Nat.le_refl 1, by intro _; exact Nat.le_refl 0⟩
  · decide
  · intro hDominates
    exact Nat.not_succ_le_self 1 hDominates.1

end UniformBatchOptimality
