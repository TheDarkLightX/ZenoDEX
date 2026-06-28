import Proofs.CPMMOutputMonotonicity
import Mathlib.Tactic

/-!
# AB Strict Zero-Min Monotone Reserve Lemmas

This file isolates the arithmetic proof obligation behind the experimental
AB strict executable zero-min compression result.

For same-pool, same-direction, exact-in swaps with `min_amount_out = 0`, the
runtime still requires positive output. Inside the strict executable scope,
each candidate suffix is a fixed sequence of successful exact-in steps. The
only state component relevant to output variation between two records for the
same processed subset is `reserve_out`; `reserve_in` follows the same gross
input sum for both records.

The core lemma proves that the CPMM post-swap output reserve

`reserve_out - floor(reserve_out * net_in / (reserve_in + net_in))`

is monotone in the starting output reserve, including integer floor rounding.
The suffix theorem lifts that one-step fact through a fixed list of future
exact-in steps. This is a proof component for the research certificate only;
it does not authorize ordering, settlement, or production promotion.
-/

namespace ABStrictZeroMinMonotone

open AntiFragmentation (swapOut)

/-- One fixed exact-in step in a strict executable suffix.

`grossIn` advances the input reserve. `netIn` is the already-computed input
after deterministic fees. The monotonicity proof is independent of the fee
formula once `netIn` is fixed for the compared records. -/
structure ExactInStep where
  grossIn : Nat
  netIn : Nat
  deriving Repr, DecidableEq

/-- CPMM post-swap output reserve for one exact-in step. -/
def postReserveOut (reserveIn reserveOut netIn : Nat) : Nat :=
  reserveOut - swapOut reserveIn reserveOut netIn

/-- Execute a fixed strict exact-in suffix, returning only the final output
reserve. The input reserve advances by gross input because fees remain in the
pool for the v8 exact-in zero-protocol-fee surface used by the batch refuter. -/
def runReserveOutAfterSuffix (reserveIn reserveOut : Nat) : List ExactInStep -> Nat
  | [] => reserveOut
  | step :: rest =>
      runReserveOutAfterSuffix
        (reserveIn + step.grossIn)
        (postReserveOut reserveIn reserveOut step.netIn)
        rest

/-- Execute a fixed strict exact-in suffix, returning the sum of per-step
outputs. For the zero-min research surface, this is also the suffix surplus. -/
def runOutputAfterSuffix (reserveIn reserveOut : Nat) : List ExactInStep -> Nat
  | [] => 0
  | step :: rest =>
      let amountOut := swapOut reserveIn reserveOut step.netIn
      amountOut +
        runOutputAfterSuffix
          (reserveIn + step.grossIn)
          (postReserveOut reserveIn reserveOut step.netIn)
          rest

/-- Reserve-in after a fixed suffix is a function of the gross input multiset
sum. This records the order-independence component used by the induction
argument. -/
def reserveInAfterGross (initialReserveIn : Nat) (steps : List ExactInStep) : Nat :=
  initialReserveIn + (steps.map ExactInStep.grossIn).sum

/-- Execute a fixed suffix, returning only the final input reserve. -/
def runReserveInAfterSuffix (reserveIn : Nat) : List ExactInStep -> Nat
  | [] => reserveIn
  | step :: rest =>
      runReserveInAfterSuffix
        (reserveIn + step.grossIn)
        rest

/-- Running a fixed suffix advances input reserve by exactly the sum of gross
input amounts. Output reserve and CPMM arithmetic are irrelevant to this
component. -/
theorem runReserveInAfterSuffix_eq_reserveInAfterGross
    (initialReserveIn : Nat)
    (steps : List ExactInStep) :
    runReserveInAfterSuffix initialReserveIn steps =
      reserveInAfterGross initialReserveIn steps := by
  induction steps generalizing initialReserveIn with
  | nil =>
      simp [runReserveInAfterSuffix, reserveInAfterGross]
  | cons step rest ih =>
      simp [runReserveInAfterSuffix, reserveInAfterGross, ih, Nat.add_assoc]

/-- Appending two fixed suffixes adds their gross input contributions. -/
theorem reserveInAfterGross_append
    (initialReserveIn : Nat)
    (firstSteps suffix : List ExactInStep) :
    reserveInAfterGross initialReserveIn (firstSteps ++ suffix) =
      reserveInAfterGross (reserveInAfterGross initialReserveIn firstSteps) suffix := by
  simp [reserveInAfterGross, Nat.add_assoc]

/-- Reversing a fixed suffix preserves the total gross input contribution to
the input reserve. -/
theorem reserveInAfterGross_reverse (initialReserveIn : Nat) (steps : List ExactInStep) :
    reserveInAfterGross initialReserveIn steps.reverse =
      reserveInAfterGross initialReserveIn steps := by
  simp [reserveInAfterGross]

/-- Two records with the same processed gross-input sum have the same processed
input reserve. This is the record-level invariant used by the pruning lemmas. -/
theorem sameGrossSum_gives_sameReserveIn
    {initialReserveIn : Nat}
    {left right : List ExactInStep}
    (hsum :
      (left.map ExactInStep.grossIn).sum =
        (right.map ExactInStep.grossIn).sum) :
    reserveInAfterGross initialReserveIn left =
      reserveInAfterGross initialReserveIn right := by
  simp [reserveInAfterGross, hsum]

/-- Concrete non-vacuity witness for input-reserve suffix execution. -/
theorem witness_runReserveInAfterSuffix :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    runReserveInAfterSuffix 1000 suffix = 1300 ∧
      reserveInAfterGross 1000 suffix = 1300 := by
  native_decide

/-- Concrete non-vacuity witness for same gross-input sums. -/
theorem witness_sameGrossSum_gives_sameReserveIn :
    let left : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    let right : List ExactInStep := [
      ⟨200, 199⟩,
      ⟨100, 99⟩
    ]
    reserveInAfterGross 1000 left = reserveInAfterGross 1000 right := by
  native_decide

/-- A fixed strict exact-in suffix cannot increase output reserve. -/
theorem runReserveOutAfterSuffix_le_initial
    (reserveIn reserveOut : Nat)
    (steps : List ExactInStep) :
    runReserveOutAfterSuffix reserveIn reserveOut steps ≤ reserveOut := by
  induction steps generalizing reserveIn reserveOut with
  | nil =>
      simp [runReserveOutAfterSuffix]
  | cons step rest ih =>
      simp [runReserveOutAfterSuffix]
      exact Nat.le_trans
        (ih
          (reserveIn := reserveIn + step.grossIn)
          (reserveOut := postReserveOut reserveIn reserveOut step.netIn))
        (Nat.sub_le reserveOut (swapOut reserveIn reserveOut step.netIn))

/-- Telescoping output identity for a fixed strict exact-in suffix.

The sum of per-step zero-min outputs is exactly the drop in output reserve from
the suffix start to the suffix end. This connects the final reserve-out order
used by the pruning proof to the zero-min surplus objective. -/
theorem runOutputAfterSuffix_eq_reserveOut_sub_finalReserveOut
    (reserveIn reserveOut : Nat)
    (steps : List ExactInStep) :
    runOutputAfterSuffix reserveIn reserveOut steps =
      reserveOut - runReserveOutAfterSuffix reserveIn reserveOut steps := by
  induction steps generalizing reserveIn reserveOut with
  | nil =>
      simp [runOutputAfterSuffix, runReserveOutAfterSuffix]
  | cons step rest ih =>
      simp [runOutputAfterSuffix, runReserveOutAfterSuffix]
      rw [ih]
      have hout_le :
          swapOut reserveIn reserveOut step.netIn ≤ reserveOut :=
        AntiFragmentation.swapOut_le_reserve reserveIn reserveOut step.netIn
      have hfinal_le :
          runReserveOutAfterSuffix
              (reserveIn + step.grossIn)
              (postReserveOut reserveIn reserveOut step.netIn)
              rest ≤
            postReserveOut reserveIn reserveOut step.netIn :=
        runReserveOutAfterSuffix_le_initial
          (reserveIn + step.grossIn)
          (postReserveOut reserveIn reserveOut step.netIn)
          rest
      unfold postReserveOut at hfinal_le ⊢
      omega

/-- In the zero-min suffix model, suffix surplus equals final output-reserve
drop. -/
def zeroMinSuffixSurplus (reserveIn reserveOut : Nat) (steps : List ExactInStep) : Nat :=
  runOutputAfterSuffix reserveIn reserveOut steps

/-- Zero-min suffix surplus is the initial output reserve minus the final
output reserve. -/
theorem zeroMinSuffixSurplus_eq_reserveOut_sub_finalReserveOut
    (reserveIn reserveOut : Nat)
    (steps : List ExactInStep) :
    zeroMinSuffixSurplus reserveIn reserveOut steps =
      reserveOut - runReserveOutAfterSuffix reserveIn reserveOut steps := by
  exact runOutputAfterSuffix_eq_reserveOut_sub_finalReserveOut reserveIn reserveOut steps

/-- Concrete non-vacuity witness for the zero-min output telescoping identity. -/
theorem witness_runOutputAfterSuffix_telescopes :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    runOutputAfterSuffix 1000 1200 suffix =
      1200 - runReserveOutAfterSuffix 1000 1200 suffix ∧
    zeroMinSuffixSurplus 1000 1200 suffix = runOutputAfterSuffix 1000 1200 suffix := by
  native_decide

/-- One-step CPMM post-reserve monotonicity in `reserve_out`.

If one record starts with no more output reserve than another record, then after
the same exact-in step it still has no more output reserve. The proof uses
`swapOut_contraction`: adding `delta` output reserve can increase the output by
at most `delta`, so the unspent reserve cannot move in the opposite direction. -/
theorem postReserveOut_mono_reserveOut
    {reserveIn netIn reserveOutSmall reserveOutLarge : Nat}
    (hreserve : reserveOutSmall ≤ reserveOutLarge) :
    postReserveOut reserveIn reserveOutSmall netIn ≤
      postReserveOut reserveIn reserveOutLarge netIn := by
  unfold postReserveOut
  obtain ⟨delta, hdelta⟩ := Nat.exists_eq_add_of_le hreserve
  subst reserveOutLarge
  have hcontract :=
    CPMMOutputMonotonicity.swapOut_contraction reserveIn reserveOutSmall netIn delta
  have hsmall_le :
      swapOut reserveIn reserveOutSmall netIn ≤ reserveOutSmall :=
    AntiFragmentation.swapOut_le_reserve reserveIn reserveOutSmall netIn
  omega

/-- Fixed-suffix monotonicity.

Keeping the lower output-reserve representative for a processed subset preserves
the lower-output-reserve relation through any fixed future strict exact-in
suffix. -/
theorem runReserveOutAfterSuffix_mono
    {reserveIn reserveOutSmall reserveOutLarge : Nat}
    {steps : List ExactInStep}
    (hreserve : reserveOutSmall ≤ reserveOutLarge) :
    runReserveOutAfterSuffix reserveIn reserveOutSmall steps ≤
      runReserveOutAfterSuffix reserveIn reserveOutLarge steps := by
  induction steps generalizing reserveIn reserveOutSmall reserveOutLarge with
  | nil =>
      simpa [runReserveOutAfterSuffix] using hreserve
  | cons step rest ih =>
      simp [runReserveOutAfterSuffix]
      exact ih
        (reserveIn := reserveIn + step.grossIn)
        (reserveOutSmall := postReserveOut reserveIn reserveOutSmall step.netIn)
        (reserveOutLarge := postReserveOut reserveIn reserveOutLarge step.netIn)
        (postReserveOut_mono_reserveOut
          (reserveIn := reserveIn)
          (netIn := step.netIn)
          hreserve)

/-- Lower final output reserve means weakly greater total extracted output from
the same original reserve. -/
theorem lowerFinalReserve_gives_ge_totalOutput
    {initialReserveOut finalSmall finalLarge : Nat}
    (hfinal : finalSmall ≤ finalLarge) :
    initialReserveOut - finalLarge ≤ initialReserveOut - finalSmall := by
  omega

/-- A compressed DP record after a fixed processed subset.

For the strict zero-min research surface, two records with the same processed
subset have the same input reserve contribution. The compression keeps only the
record with the lower output reserve. -/
structure ProcessedRecord where
  processedReserveIn : Nat
  reserveOut : Nat
  deriving Repr, DecidableEq

/-- Final output reserve after continuing from a compressed record through a
fixed strict exact-in suffix. -/
def finalReserveOutAfterRecord (record : ProcessedRecord) (suffix : List ExactInStep) : Nat :=
  runReserveOutAfterSuffix record.processedReserveIn record.reserveOut suffix

/-- Total output extracted from the original output reserve after continuing
from a compressed record. -/
def suffixTotalOutput
    (initialReserveOut : Nat)
    (record : ProcessedRecord)
    (suffix : List ExactInStep) : Nat :=
  initialReserveOut - finalReserveOutAfterRecord record suffix

/-- DP-level representative dominance.

If two records represent the same processed subset, encoded here as the same
processed input reserve, and one has no more output reserve than the other,
then retaining the lower-output-reserve record gives weakly greater total
output after any fixed strict zero-min suffix. This is the abstract pruning
lemma behind the one-record min-reserve-out compression certificate. -/
theorem minReserveRecord_dominates_suffixTotalOutput
    {initialReserveOut : Nat}
    {lower upper : ProcessedRecord}
    {suffix : List ExactInStep}
    (hsame : lower.processedReserveIn = upper.processedReserveIn)
    (hreserve : lower.reserveOut ≤ upper.reserveOut) :
    suffixTotalOutput initialReserveOut upper suffix ≤
      suffixTotalOutput initialReserveOut lower suffix := by
  unfold suffixTotalOutput finalReserveOutAfterRecord
  rw [← hsame]
  exact lowerFinalReserve_gives_ge_totalOutput
    (runReserveOutAfterSuffix_mono
      (reserveIn := lower.processedReserveIn)
      (reserveOutSmall := lower.reserveOut)
      (reserveOutLarge := upper.reserveOut)
      (steps := suffix)
      hreserve)

/-- Best suffix output among a finite candidate record set. -/
def bestSuffixOutputFromRecords
    (initialReserveOut : Nat)
    (records : List ProcessedRecord)
    (suffix : List ExactInStep) : Nat :=
  (records.map (fun record => suffixTotalOutput initialReserveOut record suffix)).foldl Nat.max 0

/-- Helper for bounding a `foldl Nat.max` aggregate by a known upper bound. -/
theorem foldlMax_le_bound
    {values : List Nat}
    {acc bound : Nat}
    (hacc : acc ≤ bound)
    (hvalues : ∀ value, value ∈ values -> value ≤ bound) :
    values.foldl Nat.max acc ≤ bound := by
  induction values generalizing acc with
  | nil =>
      simpa using hacc
  | cons value rest ih =>
      apply ih
      · exact Nat.max_le.mpr ⟨hacc, hvalues value (by simp)⟩
      · intro candidate hcandidate
        exact hvalues candidate (by simp [hcandidate])

/-- Finite candidate-set pruning theorem.

If `selected` has the minimum output reserve among a finite set of records that
all represent the same processed input reserve, then the best suffix output
obtainable from that whole record set is no better than continuing from
`selected`. This is the finite-record version of the DP pruning obligation. -/
theorem bestSuffixOutputFromRecords_le_selected
    {initialReserveOut : Nat}
    {selected : ProcessedRecord}
    {records : List ProcessedRecord}
    {suffix : List ExactInStep}
    (hsame :
      ∀ record, record ∈ records ->
        selected.processedReserveIn = record.processedReserveIn)
    (hmin :
      ∀ record, record ∈ records ->
        selected.reserveOut ≤ record.reserveOut) :
    bestSuffixOutputFromRecords initialReserveOut records suffix ≤
      suffixTotalOutput initialReserveOut selected suffix := by
  unfold bestSuffixOutputFromRecords
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨record, hrecord, rfl⟩
    exact minReserveRecord_dominates_suffixTotalOutput
      (initialReserveOut := initialReserveOut)
      (lower := selected)
      (upper := record)
      (suffix := suffix)
      (hsame record hrecord)
      (hmin record hrecord)

/-- Concrete non-vacuity witness for record dominance. -/
theorem witness_minReserveRecord_dominates_suffixTotalOutput :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    let lower : ProcessedRecord := ⟨1100, 900⟩
    let upper : ProcessedRecord := ⟨1100, 1100⟩
    suffixTotalOutput 1200 upper suffix ≤
      suffixTotalOutput 1200 lower suffix := by
  native_decide

/-- Concrete non-vacuity witness for finite record-set pruning. -/
theorem witness_bestSuffixOutputFromRecords_le_selected :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    let selected : ProcessedRecord := ⟨1100, 800⟩
    let records : List ProcessedRecord := [
      ⟨1100, 900⟩,
      ⟨1100, 1100⟩
    ]
    bestSuffixOutputFromRecords 1200 records suffix ≤
      suffixTotalOutput 1200 selected suffix := by
  native_decide

/-- Concrete non-vacuity witness for one-step monotonicity. -/
theorem witness_postReserveOut_mono_strict :
    postReserveOut 1000 1000 100 ≤ postReserveOut 1000 1500 100 ∧
      postReserveOut 1000 1000 100 = 910 ∧
      postReserveOut 1000 1500 100 = 1364 := by
  native_decide

/-- Concrete non-vacuity witness for suffix monotonicity. -/
theorem witness_runReserveOutAfterSuffix_mono :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    runReserveOutAfterSuffix 1000 900 suffix ≤
      runReserveOutAfterSuffix 1000 1100 suffix := by
  native_decide

end ABStrictZeroMinMonotone
