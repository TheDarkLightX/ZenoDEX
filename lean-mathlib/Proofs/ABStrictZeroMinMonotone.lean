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

/-- Strict executable one-step predicate for the zero-min research surface.

This captures the local conditions needed by the abstract suffix model: positive
reserves, positive gross and net input, fee sanity (`netIn <= grossIn`), and
positive CPMM output. -/
def strictStepExecutable (reserveIn reserveOut : Nat) (step : ExactInStep) : Prop :=
  0 < reserveIn ∧
    0 < reserveOut ∧
    0 < step.grossIn ∧
    0 < step.netIn ∧
    step.netIn ≤ step.grossIn ∧
    0 < swapOut reserveIn reserveOut step.netIn

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

/-- Strict executable suffix predicate for the zero-min research surface. -/
def suffixExecutable (reserveIn reserveOut : Nat) : List ExactInStep -> Prop
  | [] => True
  | step :: rest =>
      strictStepExecutable reserveIn reserveOut step ∧
        suffixExecutable
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

/-- With positive reserves, CPMM output is strictly less than output reserve. -/
theorem swapOut_lt_reserve_of_pos
    (reserveIn reserveOut netIn : Nat)
    (hin : 0 < reserveIn)
    (hout : 0 < reserveOut) :
    swapOut reserveIn reserveOut netIn < reserveOut := by
  simp only [swapOut]
  by_cases hnet : netIn = 0
  · subst hnet
    simp [hout]
  · apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm (reserveIn + netIn) reserveOut]
    exact (Nat.mul_lt_mul_left hout).mpr (by omega)

/-- A strict executable step leaves positive output reserve. -/
theorem strictStepExecutable_postReserveOut_pos
    {reserveIn reserveOut : Nat}
    {step : ExactInStep}
    (hexec : strictStepExecutable reserveIn reserveOut step) :
    0 < postReserveOut reserveIn reserveOut step.netIn := by
  rcases hexec with ⟨hin, hout, _hgross, _hnet, _hfee, _houtput⟩
  have hlt := swapOut_lt_reserve_of_pos reserveIn reserveOut step.netIn hin hout
  unfold postReserveOut
  omega

/-- A strict executable step strictly decreases output reserve. -/
theorem strictStepExecutable_postReserveOut_lt
    {reserveIn reserveOut : Nat}
    {step : ExactInStep}
    (hexec : strictStepExecutable reserveIn reserveOut step) :
    postReserveOut reserveIn reserveOut step.netIn < reserveOut := by
  rcases hexec with ⟨_hin, _hout, _hgross, _hnet, _hfee, houtput⟩
  have hle :
      swapOut reserveIn reserveOut step.netIn ≤ reserveOut :=
    AntiFragmentation.swapOut_le_reserve reserveIn reserveOut step.netIn
  unfold postReserveOut
  omega

/-- A strict executable suffix leaves positive final output reserve. -/
theorem suffixExecutable_finalReserveOut_pos
    {reserveIn reserveOut : Nat}
    {steps : List ExactInStep}
    (hout : 0 < reserveOut)
    (hexec : suffixExecutable reserveIn reserveOut steps) :
    0 < runReserveOutAfterSuffix reserveIn reserveOut steps := by
  induction steps generalizing reserveIn reserveOut with
  | nil =>
      simpa [suffixExecutable, runReserveOutAfterSuffix] using hout
  | cons step rest ih =>
      rcases hexec with ⟨hstep, hrest⟩
      simp [runReserveOutAfterSuffix]
      exact ih
        (reserveIn := reserveIn + step.grossIn)
        (reserveOut := postReserveOut reserveIn reserveOut step.netIn)
        (strictStepExecutable_postReserveOut_pos hstep)
        hrest

/-- A strict executable suffix keeps the input reserve positive. -/
theorem suffixExecutable_finalReserveIn_pos
    {reserveIn : Nat}
    {steps : List ExactInStep}
    (hin : 0 < reserveIn) :
    0 < runReserveInAfterSuffix reserveIn steps := by
  induction steps generalizing reserveIn with
  | nil =>
      simpa [runReserveInAfterSuffix] using hin
  | cons step rest ih =>
      simp [runReserveInAfterSuffix]
      exact ih (reserveIn := reserveIn + step.grossIn) (by omega)

/-- Concrete non-vacuity witness for strict executable suffixes. -/
theorem witness_suffixExecutable :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    suffixExecutable 1000 1200 suffix ∧
      0 < runReserveOutAfterSuffix 1000 1200 suffix ∧
      0 < runReserveInAfterSuffix 1000 suffix := by
  norm_num [suffixExecutable, strictStepExecutable, postReserveOut,
    runReserveOutAfterSuffix, runReserveInAfterSuffix, swapOut]

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

/-- Economic AB key for the strict executable zero-min research surface.

The key intentionally contains only the economic dimensions supported by the
counterexample-salvage evidence: executed input and zero-min surplus. Canonical
tie order is outside this key. -/
structure ZeroMinEconomicKey where
  executedInput : Nat
  surplus : Nat
  deriving Repr, DecidableEq

/-- Candidate key is weakly dominated by winner key in the economic objective. -/
def zeroMinEconomicKeyDominated
    (candidate winner : ZeroMinEconomicKey) : Prop :=
  candidate.executedInput ≤ winner.executedInput ∧
    candidate.surplus ≤ winner.surplus

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

/-- A finite subset-mask record family.

`maskId` is an abstract identifier for the processed subset. This file does
not model bit operations; it isolates the proof obligation that per-mask
representative pruning composes across a finite family of masks. -/
structure MaskRecordSet where
  maskId : Nat
  selected : ProcessedRecord
  records : List ProcessedRecord
  deriving Repr, DecidableEq

/-- Bit-level membership predicate for a natural-number subset mask. -/
def maskHasBit (mask bitIndex : Nat) : Prop :=
  mask.testBit bitIndex = true

/-- Bit-level subset-mask step relation.

The transition sets `bitIndex` in the child mask and preserves every other bit.
This is relational so it does not depend on a particular bitwise-set helper
being available in the Lean toolchain. -/
def bitMaskStep (parentMask bitIndex childMask : Nat) : Prop :=
  maskHasBit childMask bitIndex ∧
    ∀ otherBit, otherBit ≠ bitIndex ->
      childMask.testBit otherBit = parentMask.testBit otherBit

/-- A bit-mask path is a finite sequence of one-bit mask steps. -/
def bitMaskPath : Nat -> List Nat -> Nat -> Prop
  | currentMask, [], finalMask => finalMask = currentMask
  | currentMask, bitIndex :: rest, finalMask =>
      ∃ nextMask,
        bitMaskStep currentMask bitIndex nextMask ∧
          bitMaskPath nextMask rest finalMask

/-- A bit-mask step sets the selected bit in the child mask. -/
theorem bitMaskStep_sets_bit
    {parentMask childMask bitIndex : Nat}
    (hstep : bitMaskStep parentMask bitIndex childMask) :
    maskHasBit childMask bitIndex := by
  exact hstep.1

/-- A bit-mask step preserves every non-selected bit. -/
theorem bitMaskStep_preserves_other_bits
    {parentMask childMask bitIndex otherBit : Nat}
    (hstep : bitMaskStep parentMask bitIndex childMask)
    (hother : otherBit ≠ bitIndex) :
    childMask.testBit otherBit = parentMask.testBit otherBit := by
  exact hstep.2 otherBit hother

/-- A bit-mask step preserves all bits already set in the parent mask. -/
theorem bitMaskStep_preserves_prior_bits
    {parentMask childMask bitIndex priorBit : Nat}
    (hstep : bitMaskStep parentMask bitIndex childMask)
    (hprior : maskHasBit parentMask priorBit) :
    maskHasBit childMask priorBit := by
  by_cases hsame : priorBit = bitIndex
  · subst priorBit
    exact hstep.1
  · unfold maskHasBit at hprior ⊢
    rw [hstep.2 priorBit hsame]
    exact hprior

/-- Setting an already-selected bit is extensionally a no-op on masks. -/
theorem bitMaskStep_already_selected_eq
    {parentMask childMask bitIndex : Nat}
    (hstep : bitMaskStep parentMask bitIndex childMask)
    (hprior : maskHasBit parentMask bitIndex) :
    childMask = parentMask := by
  apply Nat.eq_of_testBit_eq
  intro otherBit
  by_cases hsame : otherBit = bitIndex
  · subst otherBit
    unfold maskHasBit at hprior
    rw [hstep.1, hprior]
  · exact hstep.2 otherBit hsame

/-- A bit-mask path preserves every bit set in the start mask. -/
theorem bitMaskPath_preserves_prior_bits
    {startMask finalMask : Nat}
    {pathBits : List Nat}
    {priorBit : Nat}
    (hpath : bitMaskPath startMask pathBits finalMask)
    (hprior : maskHasBit startMask priorBit) :
    maskHasBit finalMask priorBit := by
  induction pathBits generalizing startMask with
  | nil =>
      simp [bitMaskPath] at hpath
      simpa [hpath] using hprior
  | cons bitIndex rest ih =>
      simp [bitMaskPath] at hpath
      rcases hpath with ⟨nextMask, hstep, hrest⟩
      exact ih hrest (bitMaskStep_preserves_prior_bits hstep hprior)

/-- The bit selected by the head step remains set after the rest of the path. -/
theorem bitMaskPath_head_bit_remains_set
    {startMask finalMask bitIndex : Nat}
    {rest : List Nat}
    (hpath : bitMaskPath startMask (bitIndex :: rest) finalMask) :
    maskHasBit finalMask bitIndex := by
  simp [bitMaskPath] at hpath
  rcases hpath with ⟨nextMask, hstep, hrest⟩
  exact bitMaskPath_preserves_prior_bits hrest hstep.1

/-- Every bit in a finite bit-index list is set in a mask. -/
def allBitsSet (mask : Nat) (pathBits : List Nat) : Prop :=
  ∀ bitIndex, bitIndex ∈ pathBits -> maskHasBit mask bitIndex

/-- A bit-mask path sets every bit named by the path. -/
theorem bitMaskPath_sets_path_bits
    {startMask finalMask : Nat}
    {pathBits : List Nat}
    (hpath : bitMaskPath startMask pathBits finalMask) :
    allBitsSet finalMask pathBits := by
  induction pathBits generalizing startMask finalMask with
  | nil =>
      intro bitIndex hmem
      simp at hmem
  | cons stepBit rest ih =>
      intro candidateBit hcandidate
      simp [bitMaskPath] at hpath
      rcases hpath with ⟨nextMask, hstep, hrest⟩
      rw [List.mem_cons] at hcandidate
      cases hcandidate with
      | inl hhead =>
          subst hhead
          exact bitMaskPath_preserves_prior_bits hrest hstep.1
      | inr htail =>
          exact ih hrest candidateBit htail

/-- A bit-mask path preserves start bits and sets path bits. -/
theorem bitMaskPath_preserves_start_or_sets_path_bits
    {startMask finalMask : Nat}
    {pathBits : List Nat}
    {bitIndex : Nat}
    (hpath : bitMaskPath startMask pathBits finalMask)
    (hbit : maskHasBit startMask bitIndex ∨ bitIndex ∈ pathBits) :
    maskHasBit finalMask bitIndex := by
  cases hbit with
  | inl hstart =>
      exact bitMaskPath_preserves_prior_bits hpath hstart
  | inr hpathBit =>
      exact bitMaskPath_sets_path_bits hpath bitIndex hpathBit

/-- Every bit below a finite bound is set in a mask. -/
def allBitsBelowSet (mask bitCount : Nat) : Prop :=
  ∀ bitIndex, bitIndex < bitCount -> maskHasBit mask bitIndex

/-- Coverage of `List.range bitCount` gives bounded full-mask coverage. -/
theorem allBitsSet_range_gives_allBitsBelowSet
    {mask bitCount : Nat}
    (hbits : allBitsSet mask (List.range bitCount)) :
    allBitsBelowSet mask bitCount := by
  intro bitIndex hlt
  exact hbits bitIndex (List.mem_range.mpr hlt)

/-- A bit-mask path over `List.range bitCount` sets every bit below the bound. -/
theorem bitMaskPath_sets_range_bits
    {startMask finalMask bitCount : Nat}
    (hpath : bitMaskPath startMask (List.range bitCount) finalMask) :
    allBitsBelowSet finalMask bitCount := by
  exact allBitsSet_range_gives_allBitsBelowSet (bitMaskPath_sets_path_bits hpath)

/-- A record-level mask transition links the `maskId` fields to the bit-level
step relation. -/
def maskRecordStep (parent child : MaskRecordSet) (bitIndex : Nat) : Prop :=
  bitMaskStep parent.maskId bitIndex child.maskId

/-- A record-level mask path links the `maskId` fields to the bit-level path
relation. -/
def maskRecordPath (parent : MaskRecordSet) (pathBits : List Nat) (child : MaskRecordSet) : Prop :=
  bitMaskPath parent.maskId pathBits child.maskId

/-- A record-level mask transition sets the chosen bit in the child mask id. -/
theorem maskRecordStep_sets_child_bit
    {parent child : MaskRecordSet}
    {bitIndex : Nat}
    (hstep : maskRecordStep parent child bitIndex) :
    maskHasBit child.maskId bitIndex := by
  exact bitMaskStep_sets_bit hstep

/-- A record-level mask transition preserves prior bits from the parent mask id. -/
theorem maskRecordStep_preserves_parent_bits
    {parent child : MaskRecordSet}
    {bitIndex priorBit : Nat}
    (hstep : maskRecordStep parent child bitIndex)
    (hprior : maskHasBit parent.maskId priorBit) :
    maskHasBit child.maskId priorBit := by
  exact bitMaskStep_preserves_prior_bits hstep hprior

/-- A record-level mask path sets every bit named by the path in the child
mask id. -/
theorem maskRecordPath_sets_path_bits
    {parent child : MaskRecordSet}
    {pathBits : List Nat}
    (hpath : maskRecordPath parent pathBits child) :
    allBitsSet child.maskId pathBits := by
  exact bitMaskPath_sets_path_bits hpath

/-- A record-level mask path preserves bits that were set in the parent mask id. -/
theorem maskRecordPath_preserves_parent_bits
    {parent child : MaskRecordSet}
    {pathBits : List Nat}
    {bitIndex : Nat}
    (hpath : maskRecordPath parent pathBits child)
    (hprior : maskHasBit parent.maskId bitIndex) :
    maskHasBit child.maskId bitIndex := by
  exact bitMaskPath_preserves_prior_bits hpath hprior

/-- A record-level mask path over `List.range bitCount` sets every bit below the
bound in the child mask id. -/
theorem maskRecordPath_sets_range_bits
    {parent child : MaskRecordSet}
    {bitCount : Nat}
    (hpath : maskRecordPath parent (List.range bitCount) child) :
    allBitsBelowSet child.maskId bitCount := by
  exact bitMaskPath_sets_range_bits hpath

/-- Concrete non-vacuity witness for the bit-mask transition relation. -/
theorem witness_bitMaskStep_noop :
    bitMaskStep 1 0 1 ∧ bitMaskPath 1 [0] 1 := by
  have hstep : bitMaskStep 1 0 1 := by
    unfold bitMaskStep maskHasBit
    constructor
    · native_decide
    · intro otherBit _hother
      rfl
  constructor
  · exact hstep
  · exact ⟨1, hstep, by simp [bitMaskPath]⟩

/-- Concrete non-vacuity witness for bit-mask path growth. -/
theorem witness_bitMaskPath_sets_path_bits :
    bitMaskPath 1 [0] 1 ∧ allBitsSet 1 [0] := by
  constructor
  · exact witness_bitMaskStep_noop.2
  · intro bitIndex hmem
    simp at hmem
    subst bitIndex
    unfold maskHasBit
    native_decide

/-- Concrete non-vacuity witness for bounded full-range bit coverage. -/
theorem witness_bitMaskPath_sets_range_bits :
    bitMaskPath 1 (List.range 1) 1 ∧ allBitsBelowSet 1 1 := by
  have hpath : bitMaskPath 1 (List.range 1) 1 := by
    simpa using witness_bitMaskStep_noop.2
  constructor
  · exact hpath
  · exact bitMaskPath_sets_range_bits hpath

/-- A mask is locally prunable when its selected record has the same processed
input reserve as every full record and no more output reserve. -/
def maskPruningInvariant (mask : MaskRecordSet) : Prop :=
  (∀ record, record ∈ mask.records ->
    mask.selected.processedReserveIn = record.processedReserveIn) ∧
  (∀ record, record ∈ mask.records ->
    mask.selected.reserveOut ≤ record.reserveOut)

/-- Best suffix output from the full record set at one abstract mask. -/
def maskFullBestSuffixOutput
    (initialReserveOut : Nat)
    (mask : MaskRecordSet)
    (suffix : List ExactInStep) : Nat :=
  bestSuffixOutputFromRecords initialReserveOut mask.records suffix

/-- Suffix output from the selected compressed representative at one abstract
mask. -/
def maskSelectedSuffixOutput
    (initialReserveOut : Nat)
    (mask : MaskRecordSet)
    (suffix : List ExactInStep) : Nat :=
  suffixTotalOutput initialReserveOut mask.selected suffix

/-- Best suffix output from all full record sets across a finite mask family. -/
def bestFullSuffixOutputAcrossMasks
    (initialReserveOut : Nat)
    (masks : List MaskRecordSet)
    (suffix : List ExactInStep) : Nat :=
  (masks.map (fun mask => maskFullBestSuffixOutput initialReserveOut mask suffix)).foldl Nat.max 0

/-- Best suffix output from all compressed representatives across a finite mask
family. -/
def bestSelectedSuffixOutputAcrossMasks
    (initialReserveOut : Nat)
    (masks : List MaskRecordSet)
    (suffix : List ExactInStep) : Nat :=
  (masks.map (fun mask => maskSelectedSuffixOutput initialReserveOut mask suffix)).foldl Nat.max 0

/-- Economic key for the selected compressed representative. -/
def selectedZeroMinEconomicKey
    (executedInput initialReserveOut : Nat)
    (winner : MaskRecordSet)
    (suffix : List ExactInStep) : ZeroMinEconomicKey :=
  ⟨executedInput, maskSelectedSuffixOutput initialReserveOut winner suffix⟩

/-- Economic key for the best full-state child frontier under a fixed executed
input component. -/
def fullFrontierZeroMinEconomicKey
    (executedInput initialReserveOut : Nat)
    (children : List MaskRecordSet)
    (suffix : List ExactInStep) : ZeroMinEconomicKey :=
  ⟨executedInput, bestFullSuffixOutputAcrossMasks initialReserveOut children suffix⟩

/-- A fold over `Nat.max` is at least its starting accumulator. -/
theorem acc_le_foldlMax (values : List Nat) (acc : Nat) :
    acc ≤ values.foldl Nat.max acc := by
  induction values generalizing acc with
  | nil =>
      simp
  | cons value rest ih =>
      exact Nat.le_trans
        (Nat.le_max_left acc value)
        (ih (Nat.max acc value))

/-- Every member of a finite max-fold is bounded by the fold result. -/
theorem mem_le_foldlMax
    {values : List Nat}
    {value acc : Nat}
    (hvalue : value ∈ values) :
    value ≤ values.foldl Nat.max acc := by
  induction values generalizing acc with
  | nil =>
      simp at hvalue
  | cons head rest ih =>
      rw [List.mem_cons] at hvalue
      cases hvalue with
      | inl hhead =>
          simpa [hhead] using Nat.le_trans
            (Nat.le_max_right acc head)
            (acc_le_foldlMax rest (Nat.max acc head))
      | inr hrest =>
          exact ih (acc := Nat.max acc head) hrest

/-- Local mask pruning bounds the full records at that mask by the selected
representative. -/
theorem maskFullBestSuffixOutput_le_selected
    {initialReserveOut : Nat}
    {mask : MaskRecordSet}
    {suffix : List ExactInStep}
    (hinvariant : maskPruningInvariant mask) :
    maskFullBestSuffixOutput initialReserveOut mask suffix ≤
      maskSelectedSuffixOutput initialReserveOut mask suffix := by
  rcases hinvariant with ⟨hsame, hmin⟩
  exact bestSuffixOutputFromRecords_le_selected
    (initialReserveOut := initialReserveOut)
    (selected := mask.selected)
    (records := mask.records)
    (suffix := suffix)
    hsame
    hmin

/-- A one-bit record-level child transition that also satisfies the local pruning
invariant. This is the step relation needed by the subset-mask induction
frontier. -/
def reachablePrunedStepMask
    (parent child : MaskRecordSet)
    (bitIndex : Nat) : Prop :=
  maskRecordStep parent child bitIndex ∧
    maskPruningInvariant child

/-- A reachable pruned one-step child sets the selected transition bit. -/
theorem reachablePrunedStepMask_sets_child_bit
    {parent child : MaskRecordSet}
    {bitIndex : Nat}
    (hstep : reachablePrunedStepMask parent child bitIndex) :
    maskHasBit child.maskId bitIndex := by
  exact maskRecordStep_sets_child_bit hstep.1

/-- A reachable pruned one-step child preserves bits already set in the parent. -/
theorem reachablePrunedStepMask_preserves_parent_bits
    {parent child : MaskRecordSet}
    {bitIndex priorBit : Nat}
    (hstep : reachablePrunedStepMask parent child bitIndex)
    (hprior : maskHasBit parent.maskId priorBit) :
    maskHasBit child.maskId priorBit := by
  exact maskRecordStep_preserves_parent_bits hstep.1 hprior

/-- Prefix-cover induction step for mask growth.

If the parent covers every bit below `bitIndex`, then a pruned transition at
`bitIndex` gives a child covering every bit below `bitIndex + 1`. -/
theorem reachablePrunedStepMask_extends_prefix
    {parent child : MaskRecordSet}
    {bitIndex : Nat}
    (hprefix : allBitsBelowSet parent.maskId bitIndex)
    (hstep : reachablePrunedStepMask parent child bitIndex) :
    allBitsBelowSet child.maskId (bitIndex + 1) := by
  intro candidateBit hcandidate
  have hle : candidateBit ≤ bitIndex := Nat.lt_succ_iff.mp hcandidate
  by_cases hsame : candidateBit = bitIndex
  · subst candidateBit
    exact reachablePrunedStepMask_sets_child_bit hstep
  · have hlt : candidateBit < bitIndex := lt_of_le_of_ne hle hsame
    exact reachablePrunedStepMask_preserves_parent_bits hstep (hprefix candidateBit hlt)

/-- A reachable pruned one-step child bounds its full record set by its selected
representative. -/
theorem reachablePrunedStepMask_bounds_suffix_output
    {parent child : MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hstep : reachablePrunedStepMask parent child bitIndex) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      maskSelectedSuffixOutput initialReserveOut child suffix := by
  exact maskFullBestSuffixOutput_le_selected hstep.2

/-- A reachable pruned one-step child has been retained in a finite selected
mask family. -/
def reachablePrunedStepMaskInFamily
    (parent child : MaskRecordSet)
    (bitIndex : Nat)
    (masks : List MaskRecordSet) : Prop :=
  reachablePrunedStepMask parent child bitIndex ∧
    child ∈ masks

/-- A retained reachable pruned one-step child is bounded by the selected-family
aggregate. -/
theorem reachablePrunedStepMaskInFamily_bounds_family_selected
    {parent child : MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hfull : reachablePrunedStepMaskInFamily parent child bitIndex masks) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  rcases hfull with ⟨hstep, hmem⟩
  have hlocal :
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        maskSelectedSuffixOutput initialReserveOut child suffix :=
    reachablePrunedStepMask_bounds_suffix_output
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      hstep
  have hselected_mem :
      maskSelectedSuffixOutput initialReserveOut child suffix ∈
        masks.map (fun candidate =>
          maskSelectedSuffixOutput initialReserveOut candidate suffix) := by
    exact List.mem_map.mpr ⟨child, hmem, rfl⟩
  exact Nat.le_trans hlocal (mem_le_foldlMax (acc := 0) hselected_mem)

/-- One-step family endpoint: a retained pruned child extends prefix bit coverage
and is bounded by the selected-family aggregate. -/
theorem reachablePrunedStepMaskInFamily_extends_prefix_and_bounds_family
    {parent child : MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hprefix : allBitsBelowSet parent.maskId bitIndex)
    (hfull : reachablePrunedStepMaskInFamily parent child bitIndex masks) :
    allBitsBelowSet child.maskId (bitIndex + 1) ∧
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · exact reachablePrunedStepMask_extends_prefix hprefix hfull.1
  · exact reachablePrunedStepMaskInFamily_bounds_family_selected hfull

/-- Every child in a finite one-step frontier is a retained reachable pruned
child for the selected mask family. -/
def reachablePrunedStepMaskListInFamily
    (parent : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitIndex : Nat)
    (masks : List MaskRecordSet) : Prop :=
  ∀ child, child ∈ children ->
    reachablePrunedStepMaskInFamily parent child bitIndex masks

/-- Every child in a retained one-step frontier extends parent prefix coverage. -/
theorem reachablePrunedStepMaskListInFamily_extends_prefix_members
    {parent child : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitIndex : Nat}
    (hprefix : allBitsBelowSet parent.maskId bitIndex)
    (hlist : reachablePrunedStepMaskListInFamily parent children bitIndex masks)
    (hchild : child ∈ children) :
    allBitsBelowSet child.maskId (bitIndex + 1) := by
  exact reachablePrunedStepMask_extends_prefix hprefix (hlist child hchild).1

/-- A retained one-step frontier is bounded by the selected-family aggregate. -/
theorem reachablePrunedStepMaskListInFamily_bounds_family_selected
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedStepMaskListInFamily parent children bitIndex masks) :
    bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  unfold bestFullSuffixOutputAcrossMasks
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨child, hchild, rfl⟩
    exact reachablePrunedStepMaskInFamily_bounds_family_selected
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      (hlist child hchild)

/-- One-step list endpoint for the subset-mask induction frontier: all retained
children extend parent prefix coverage, and the full child frontier is bounded by
the selected-family aggregate. -/
theorem reachablePrunedStepMaskListInFamily_extends_prefix_and_bounds_family
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hprefix : allBitsBelowSet parent.maskId bitIndex)
    (hlist : reachablePrunedStepMaskListInFamily parent children bitIndex masks) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId (bitIndex + 1)) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedStepMaskListInFamily_extends_prefix_members
      hprefix hlist hchild
  · exact reachablePrunedStepMaskListInFamily_bounds_family_selected hlist

/-- A record-level mask is range-reachable and locally pruned when it is
reachable by a range path and satisfies the local pruning invariant. -/
def reachablePrunedRangeMask
    (parent child : MaskRecordSet)
    (bitCount : Nat) : Prop :=
  maskRecordPath parent (List.range bitCount) child ∧
    maskPruningInvariant child

/-- A reachable pruned range mask covers every bit below the bound. -/
theorem reachablePrunedRangeMask_covers_bits
    {parent child : MaskRecordSet}
    {bitCount : Nat}
    (hmask : reachablePrunedRangeMask parent child bitCount) :
    allBitsBelowSet child.maskId bitCount := by
  exact maskRecordPath_sets_range_bits hmask.1

/-- A reachable pruned range mask bounds the full record-set suffix output by
the selected representative. -/
theorem reachablePrunedRangeMask_bounds_suffix_output
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hmask : reachablePrunedRangeMask parent child bitCount) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      maskSelectedSuffixOutput initialReserveOut child suffix := by
  exact maskFullBestSuffixOutput_le_selected hmask.2

/-- Endpoint bridge for the subset-mask induction frontier: a range-reachable
locally pruned child both covers the bounded mask range and bounds full suffix
output by the selected representative. -/
theorem reachablePrunedRangeMask_covers_and_bounds
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hmask : reachablePrunedRangeMask parent child bitCount) :
    allBitsBelowSet child.maskId bitCount ∧
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        maskSelectedSuffixOutput initialReserveOut child suffix := by
  constructor
  · exact reachablePrunedRangeMask_covers_bits hmask
  · exact reachablePrunedRangeMask_bounds_suffix_output hmask

/-- A reachable pruned range mask has been retained in a finite mask family.

This is the family-membership boundary used by the subset-mask induction
frontier. The predicate is explicit about membership; it does not construct the
family or prove that a host implementation emits it. -/
def reachablePrunedFullMaskInFamily
    (parent child : MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet) : Prop :=
  reachablePrunedRangeMask parent child bitCount ∧
    child ∈ masks

/-- A reachable pruned full-mask family member is bounded by the family selected
representative aggregate. -/
theorem reachablePrunedFullMaskInFamily_bounds_family_selected
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hfull : reachablePrunedFullMaskInFamily parent child bitCount masks) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  rcases hfull with ⟨hmask, hmem⟩
  have hlocal :
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        maskSelectedSuffixOutput initialReserveOut child suffix :=
    reachablePrunedRangeMask_bounds_suffix_output
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      hmask
  have hselected_mem :
      maskSelectedSuffixOutput initialReserveOut child suffix ∈
        masks.map (fun candidate =>
          maskSelectedSuffixOutput initialReserveOut candidate suffix) := by
    exact List.mem_map.mpr ⟨child, hmem, rfl⟩
  exact Nat.le_trans hlocal (mem_le_foldlMax (acc := 0) hselected_mem)

/-- Family endpoint bridge for the subset-mask induction frontier: a reachable
pruned range child retained in the mask family both covers the bounded mask
range and is bounded by the family selected-representative aggregate. -/
theorem reachablePrunedFullMaskInFamily_covers_and_bounds_family
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hfull : reachablePrunedFullMaskInFamily parent child bitCount masks) :
    allBitsBelowSet child.maskId bitCount ∧
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · exact reachablePrunedRangeMask_covers_bits hfull.1
  · exact reachablePrunedFullMaskInFamily_bounds_family_selected hfull

/-- Every child in a finite list is a reachable pruned full-mask member of the
selected mask family. -/
def reachablePrunedFullMaskListInFamily
    (parent : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet) : Prop :=
  ∀ child, child ∈ children ->
    reachablePrunedFullMaskInFamily parent child bitCount masks

/-- Every member of a reachable pruned full-mask list covers the bounded range. -/
theorem reachablePrunedFullMaskListInFamily_covers_members
    {parent child : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount : Nat}
    (hlist : reachablePrunedFullMaskListInFamily parent children bitCount masks)
    (hchild : child ∈ children) :
    allBitsBelowSet child.maskId bitCount := by
  exact reachablePrunedRangeMask_covers_bits (hlist child hchild).1

/-- A finite list of reachable pruned full-mask children is bounded by the
selected-representative aggregate of the family that retains them. -/
theorem reachablePrunedFullMaskListInFamily_bounds_family_selected
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedFullMaskListInFamily parent children bitCount masks) :
    bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  unfold bestFullSuffixOutputAcrossMasks
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨child, hchild, rfl⟩
    exact reachablePrunedFullMaskInFamily_bounds_family_selected
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      (hlist child hchild)

/-- List-level family bridge for the subset-mask induction frontier: every child
in the reachable pruned full-mask list covers the bounded mask range, and the
list's full-record suffix aggregate is bounded by the selected family aggregate. -/
theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_family
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedFullMaskListInFamily parent children bitCount masks) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedFullMaskListInFamily_covers_members hlist hchild
  · exact reachablePrunedFullMaskListInFamily_bounds_family_selected hlist

/-- A supplied compressed representative is a selected-output winner for a mask
family when every retained selected representative is no better than it.

This predicate does not construct the winner or specify a tie order. It records
only the proof obligation needed to collapse the selected-family aggregate to
one explicit representative. -/
def selectedFamilyOutputWinner
    (winner : MaskRecordSet)
    (masks : List MaskRecordSet)
    (initialReserveOut : Nat)
    (suffix : List ExactInStep) : Prop :=
  winner ∈ masks ∧
    ∀ mask, mask ∈ masks ->
      maskSelectedSuffixOutput initialReserveOut mask suffix ≤
        maskSelectedSuffixOutput initialReserveOut winner suffix

/-- A selected-output winner bounds the selected-representative aggregate for
the whole family. -/
theorem selectedFamilyOutputWinner_bounds_selected_family
    {winner : MaskRecordSet}
    {masks : List MaskRecordSet}
    {initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hwinner : selectedFamilyOutputWinner winner masks initialReserveOut suffix) :
    bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix ≤
      maskSelectedSuffixOutput initialReserveOut winner suffix := by
  unfold selectedFamilyOutputWinner at hwinner
  rcases hwinner with ⟨_hwinner_mem, hdominates⟩
  unfold bestSelectedSuffixOutputAcrossMasks
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨mask, hmask, rfl⟩
    exact hdominates mask hmask

/-- If a reachable pruned full-mask child list is retained in a selected family
and a supplied winner dominates that family, then the child-list full-record
aggregate is bounded by the winner's selected output. -/
theorem reachablePrunedFullMaskListInFamily_bounds_selected_winner
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedFullMaskListInFamily parent children bitCount masks)
    (hwinner : selectedFamilyOutputWinner winner masks initialReserveOut suffix) :
    bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
      maskSelectedSuffixOutput initialReserveOut winner suffix := by
  exact Nat.le_trans
    (reachablePrunedFullMaskListInFamily_bounds_family_selected
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      hlist)
    (selectedFamilyOutputWinner_bounds_selected_family hwinner)

/-- Winner-level endpoint for the subset-mask induction frontier: every reachable
child covers the bounded mask range, and the full child-list aggregate is bounded
by one supplied compressed representative. -/
theorem reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedFullMaskListInFamily parent children bitCount masks)
    (hwinner : selectedFamilyOutputWinner winner masks initialReserveOut suffix) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        maskSelectedSuffixOutput initialReserveOut winner suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedFullMaskListInFamily_covers_members hlist hchild
  · exact reachablePrunedFullMaskListInFamily_bounds_selected_winner hlist hwinner

/-- A proof-carrying compressed winner certificate for a finite strict zero-min
child frontier.

The certificate packages the assumptions already separated by the proof ladder:
the full-state child list is represented by reachable pruned members of the
selected mask family, and the supplied winner dominates that selected family.
It does not construct those objects or specify tie order. -/
def compressedWinnerCertificate
    (parent winner : MaskRecordSet)
    (children masks : List MaskRecordSet)
    (bitCount initialReserveOut : Nat)
    (suffix : List ExactInStep) : Prop :=
  reachablePrunedFullMaskListInFamily parent children bitCount masks ∧
    selectedFamilyOutputWinner winner masks initialReserveOut suffix

/-- A compressed winner certificate gives bounded coverage for every child in
the full-state frontier. -/
theorem compressedWinnerCertificate_covers_children
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      compressedWinnerCertificate parent winner children masks
        bitCount initialReserveOut suffix) :
    ∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount := by
  exact (reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
    (initialReserveOut := initialReserveOut)
    (suffix := suffix)
    hcert.1 hcert.2).1

/-- A compressed winner certificate bounds the full-state child frontier by the
winner's selected output. -/
theorem compressedWinnerCertificate_bounds_selected_winner
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      compressedWinnerCertificate parent winner children masks
        bitCount initialReserveOut suffix) :
    bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
      maskSelectedSuffixOutput initialReserveOut winner suffix := by
  exact reachablePrunedFullMaskListInFamily_bounds_selected_winner
    (initialReserveOut := initialReserveOut)
    (suffix := suffix)
    hcert.1 hcert.2

/-- Certificate-level endpoint for the strict zero-min compressed frontier:
bounded coverage and winner dominance follow from one proof-carrying certificate. -/
theorem compressedWinnerCertificate_covers_and_bounds
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      compressedWinnerCertificate parent winner children masks
        bitCount initialReserveOut suffix) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        maskSelectedSuffixOutput initialReserveOut winner suffix := by
  exact reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
    (initialReserveOut := initialReserveOut)
    (suffix := suffix)
    hcert.1 hcert.2

/-- A proof-carrying one-step winner certificate for one layer of the strict
zero-min subset-mask induction.

The certificate packages a retained pruned one-step child frontier and a supplied
selected-family winner. It does not construct either object or specify tie order. -/
def stepWinnerCertificate
    (parent winner : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitIndex : Nat)
    (masks : List MaskRecordSet)
    (initialReserveOut : Nat)
    (suffix : List ExactInStep) : Prop :=
  reachablePrunedStepMaskListInFamily parent children bitIndex masks ∧
    selectedFamilyOutputWinner winner masks initialReserveOut suffix

/-- Certificate-level one-step induction endpoint: if the parent covers the
prefix below `bitIndex`, then every child covers the prefix below `bitIndex + 1`,
and the full child frontier is bounded by one supplied compressed winner. -/
theorem stepWinnerCertificate_extends_prefix_and_bounds
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitIndex initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hprefix : allBitsBelowSet parent.maskId bitIndex)
    (hcert :
      stepWinnerCertificate parent winner children bitIndex masks
        initialReserveOut suffix) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId (bitIndex + 1)) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        maskSelectedSuffixOutput initialReserveOut winner suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedStepMaskListInFamily_extends_prefix_members
      hprefix hcert.1 hchild
  · exact Nat.le_trans
      (reachablePrunedStepMaskListInFamily_bounds_family_selected
        (initialReserveOut := initialReserveOut)
        (suffix := suffix)
        hcert.1)
      (selectedFamilyOutputWinner_bounds_selected_family hcert.2)

/-- A recursive chain of pruned one-bit transitions.

The path records the abstract induction skeleton from a parent mask to a child
mask. Each one-bit transition must also satisfy the local pruning invariant for
the next record set. The empty path requires the endpoint itself to be pruned. -/
def reachablePrunedStepPath (parent : MaskRecordSet) : List Nat -> MaskRecordSet -> Prop
  | [], child => child = parent ∧ maskPruningInvariant child
  | bitIndex :: rest, child =>
      ∃ next,
        reachablePrunedStepMask parent next bitIndex ∧
          reachablePrunedStepPath next rest child

/-- A recursive pruned step path induces the corresponding record-level mask
path. -/
theorem reachablePrunedStepPath_to_maskRecordPath
    {parent child : MaskRecordSet}
    {pathBits : List Nat}
    (hpath : reachablePrunedStepPath parent pathBits child) :
    maskRecordPath parent pathBits child := by
  induction pathBits generalizing parent child with
  | nil =>
      simp [reachablePrunedStepPath] at hpath
      simpa [maskRecordPath, bitMaskPath] using congrArg MaskRecordSet.maskId hpath.1
  | cons bitIndex rest ih =>
      simp [reachablePrunedStepPath, maskRecordPath, bitMaskPath] at hpath ⊢
      rcases hpath with ⟨next, hstep, hrest⟩
      exact ⟨next.maskId, hstep.1, ih hrest⟩

/-- A recursive pruned step path leaves the final child locally pruned. -/
theorem reachablePrunedStepPath_pruningInvariant
    {parent child : MaskRecordSet}
    {pathBits : List Nat}
    (hpath : reachablePrunedStepPath parent pathBits child) :
    maskPruningInvariant child := by
  induction pathBits generalizing parent child with
  | nil =>
      simp [reachablePrunedStepPath] at hpath
      exact hpath.2
  | cons bitIndex rest ih =>
      simp [reachablePrunedStepPath] at hpath
      rcases hpath with ⟨next, _hstep, hrest⟩
      exact ih hrest

/-- A recursive pruned step path over `List.range bitCount` covers every bit
below the bound. -/
theorem reachablePrunedStepPath_covers_range_bits
    {parent child : MaskRecordSet}
    {bitCount : Nat}
    (hpath : reachablePrunedStepPath parent (List.range bitCount) child) :
    allBitsBelowSet child.maskId bitCount := by
  exact maskRecordPath_sets_range_bits (reachablePrunedStepPath_to_maskRecordPath hpath)

/-- The final child of a recursive pruned step path bounds its full record set by
its selected representative. -/
theorem reachablePrunedStepPath_bounds_suffix_output
    {parent child : MaskRecordSet}
    {pathBits : List Nat}
    {initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hpath : reachablePrunedStepPath parent pathBits child) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      maskSelectedSuffixOutput initialReserveOut child suffix := by
  exact maskFullBestSuffixOutput_le_selected
    (reachablePrunedStepPath_pruningInvariant hpath)

/-- Range-specialized recursive pruned path retained in a selected mask family. -/
def reachablePrunedRangeStepPathInFamily
    (parent child : MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet) : Prop :=
  reachablePrunedStepPath parent (List.range bitCount) child ∧
    child ∈ masks

/-- A retained recursive range-step child is bounded by the selected-family
aggregate. -/
theorem reachablePrunedRangeStepPathInFamily_bounds_family_selected
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hfull : reachablePrunedRangeStepPathInFamily parent child bitCount masks) :
    maskFullBestSuffixOutput initialReserveOut child suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  rcases hfull with ⟨hpath, hmem⟩
  have hlocal :
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        maskSelectedSuffixOutput initialReserveOut child suffix :=
    reachablePrunedStepPath_bounds_suffix_output
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      hpath
  have hselected_mem :
      maskSelectedSuffixOutput initialReserveOut child suffix ∈
        masks.map (fun candidate =>
          maskSelectedSuffixOutput initialReserveOut candidate suffix) := by
    exact List.mem_map.mpr ⟨child, hmem, rfl⟩
  exact Nat.le_trans hlocal (mem_le_foldlMax (acc := 0) hselected_mem)

/-- Range-step family endpoint: a retained recursive pruned path gives bounded
full-mask coverage and the selected-family aggregate bound. -/
theorem reachablePrunedRangeStepPathInFamily_covers_and_bounds_family
    {parent child : MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    {masks : List MaskRecordSet}
    (hfull : reachablePrunedRangeStepPathInFamily parent child bitCount masks) :
    allBitsBelowSet child.maskId bitCount ∧
      maskFullBestSuffixOutput initialReserveOut child suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · exact reachablePrunedStepPath_covers_range_bits hfull.1
  · exact reachablePrunedRangeStepPathInFamily_bounds_family_selected hfull

/-- Every child in a finite frontier is retained by a recursive pruned range-step
path in the selected mask family. -/
def reachablePrunedRangeStepPathListInFamily
    (parent : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet) : Prop :=
  ∀ child, child ∈ children ->
    reachablePrunedRangeStepPathInFamily parent child bitCount masks

/-- Every child in a recursive range-step frontier covers the bounded range. -/
theorem reachablePrunedRangeStepPathListInFamily_covers_members
    {parent child : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount : Nat}
    (hlist : reachablePrunedRangeStepPathListInFamily parent children bitCount masks)
    (hchild : child ∈ children) :
    allBitsBelowSet child.maskId bitCount := by
  exact reachablePrunedStepPath_covers_range_bits (hlist child hchild).1

/-- A recursive range-step frontier is bounded by the selected-family aggregate. -/
theorem reachablePrunedRangeStepPathListInFamily_bounds_family_selected
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedRangeStepPathListInFamily parent children bitCount masks) :
    bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  unfold bestFullSuffixOutputAcrossMasks
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨child, hchild, rfl⟩
    exact reachablePrunedRangeStepPathInFamily_bounds_family_selected
      (initialReserveOut := initialReserveOut)
      (suffix := suffix)
      (hlist child hchild)

/-- List-level recursive range-step endpoint: all children cover the bounded mask
range, and the full child frontier is bounded by the selected-family aggregate. -/
theorem reachablePrunedRangeStepPathListInFamily_covers_and_bounds_family
    {parent : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hlist : reachablePrunedRangeStepPathListInFamily parent children bitCount masks) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedRangeStepPathListInFamily_covers_members hlist hchild
  · exact reachablePrunedRangeStepPathListInFamily_bounds_family_selected hlist

/-- A proof-carrying recursive range-step winner certificate for the strict
zero-min subset-mask induction frontier.

The certificate packages recursive pruned range-step reachability for a finite
child frontier and a supplied selected-family winner. It does not construct those
objects or specify tie order. -/
def rangeStepPathWinnerCertificate
    (parent winner : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet)
    (initialReserveOut : Nat)
    (suffix : List ExactInStep) : Prop :=
  reachablePrunedRangeStepPathListInFamily parent children bitCount masks ∧
    selectedFamilyOutputWinner winner masks initialReserveOut suffix

/-- Certificate endpoint for a recursive range-step frontier: bounded coverage
and selected-winner dominance follow from one proof-carrying certificate. -/
theorem rangeStepPathWinnerCertificate_covers_and_bounds
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      rangeStepPathWinnerCertificate parent winner children bitCount masks
        initialReserveOut suffix) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      bestFullSuffixOutputAcrossMasks initialReserveOut children suffix ≤
        maskSelectedSuffixOutput initialReserveOut winner suffix := by
  constructor
  · intro child hchild
    exact reachablePrunedRangeStepPathListInFamily_covers_members hcert.1 hchild
  · exact Nat.le_trans
      (reachablePrunedRangeStepPathListInFamily_bounds_family_selected
        (initialReserveOut := initialReserveOut)
        (suffix := suffix)
        hcert.1)
      (selectedFamilyOutputWinner_bounds_selected_family hcert.2)

/-- A recursive range-step winner certificate bounds the strict zero-min economic
key when the executed-input component is fixed. This captures the supported
economic AB objective while preserving tie order as a non-claim. -/
theorem rangeStepPathWinnerCertificate_bounds_zeroMinEconomicKey
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount executedInput initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      rangeStepPathWinnerCertificate parent winner children bitCount masks
        initialReserveOut suffix) :
    zeroMinEconomicKeyDominated
      (fullFrontierZeroMinEconomicKey executedInput initialReserveOut children suffix)
      (selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix) := by
  unfold zeroMinEconomicKeyDominated
    fullFrontierZeroMinEconomicKey selectedZeroMinEconomicKey
  exact ⟨Nat.le_refl executedInput,
    (rangeStepPathWinnerCertificate_covers_and_bounds hcert).2⟩

/-- Strict executable economic certificate for the compressed range-step winner.

This adds the explicit compressed-winner suffix executability assumption used by
the strict zero-min research surface. It does not prove that a host solver emits
the certificate. -/
def strictRangeStepPathEconomicCertificate
    (parent winner : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet)
    (initialReserveOut : Nat)
    (suffix : List ExactInStep) : Prop :=
  rangeStepPathWinnerCertificate parent winner children bitCount masks
      initialReserveOut suffix ∧
    suffixExecutable winner.selected.processedReserveIn winner.selected.reserveOut suffix

/-- Strict executable economic endpoint: the certificate gives bounded child
coverage, economic-key dominance, and carries compressed-winner suffix
executability. -/
theorem strictRangeStepPathEconomicCertificate_covers_bounds_and_executes
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount executedInput initialReserveOut : Nat}
    {suffix : List ExactInStep}
    (hcert :
      strictRangeStepPathEconomicCertificate parent winner children bitCount masks
        initialReserveOut suffix) :
    (∀ child, child ∈ children -> allBitsBelowSet child.maskId bitCount) ∧
      zeroMinEconomicKeyDominated
        (fullFrontierZeroMinEconomicKey executedInput initialReserveOut children suffix)
        (selectedZeroMinEconomicKey executedInput initialReserveOut winner suffix) ∧
      suffixExecutable winner.selected.processedReserveIn winner.selected.reserveOut suffix := by
  constructor
  · exact (rangeStepPathWinnerCertificate_covers_and_bounds hcert.1).1
  · exact ⟨rangeStepPathWinnerCertificate_bounds_zeroMinEconomicKey hcert.1, hcert.2⟩

/-- Final compressed full-mask economic certificate.

This is the verifier-facing shape a concrete compressed DP emitter should
eventually produce: a strict range-step economic certificate at empty suffix,
plus evidence that the selected winner belongs to the full child frontier. It
does not construct that frontier or connect it to a host implementation. -/
def strictCompressedFullMaskEconomicCertificate
    (parent winner : MaskRecordSet)
    (children : List MaskRecordSet)
    (bitCount : Nat)
    (masks : List MaskRecordSet)
    (initialReserveOut : Nat) : Prop :=
  strictRangeStepPathEconomicCertificate parent winner children bitCount masks
      initialReserveOut [] ∧
    winner ∈ children

/-- Final full-mask endpoint: a strict compressed full-mask economic certificate
proves the selected winner covers the bounded mask, its economic key dominates
the full child frontier at fixed executed input, and the empty suffix is
executable from the selected winner. -/
theorem strictCompressedFullMaskEconomicCertificate_validates
    {parent winner : MaskRecordSet}
    {children masks : List MaskRecordSet}
    {bitCount initialReserveOut executedInput : Nat}
    (hcert :
      strictCompressedFullMaskEconomicCertificate parent winner children bitCount
        masks initialReserveOut) :
    allBitsBelowSet winner.maskId bitCount ∧
      zeroMinEconomicKeyDominated
        (fullFrontierZeroMinEconomicKey executedInput initialReserveOut children [])
        (selectedZeroMinEconomicKey executedInput initialReserveOut winner []) ∧
      suffixExecutable winner.selected.processedReserveIn winner.selected.reserveOut [] := by
  rcases hcert with ⟨hstrict, hwinner_child⟩
  have hendpoint :=
    strictRangeStepPathEconomicCertificate_covers_bounds_and_executes
      (executedInput := executedInput)
      hstrict
  exact ⟨hendpoint.1 winner hwinner_child, hendpoint.2⟩

/-- Data-only shell for a future host-emitted strict full-mask economic
certificate. The `Valid` predicate below is the proof obligation; this structure
does not assert the certificate by itself. -/
structure StrictCompressedFullMaskEconomicWitness where
  parent : MaskRecordSet
  winner : MaskRecordSet
  children : List MaskRecordSet
  bitCount : Nat
  masks : List MaskRecordSet
  initialReserveOut : Nat
  executedInput : Nat
  deriving Repr

/-- Proof obligation for a host-emitted strict full-mask economic witness. -/
def strictCompressedFullMaskEconomicWitnessValid
    (witness : StrictCompressedFullMaskEconomicWitness) : Prop :=
  strictCompressedFullMaskEconomicCertificate witness.parent witness.winner
    witness.children witness.bitCount witness.masks witness.initialReserveOut

/-- Full-frontier key named through the emitter-shaped witness. -/
def strictCompressedFullMaskEconomicWitnessFullKey
    (witness : StrictCompressedFullMaskEconomicWitness) : ZeroMinEconomicKey :=
  fullFrontierZeroMinEconomicKey witness.executedInput witness.initialReserveOut
    witness.children []

/-- Selected-winner key named through the emitter-shaped witness. -/
def strictCompressedFullMaskEconomicWitnessSelectedKey
    (witness : StrictCompressedFullMaskEconomicWitness) : ZeroMinEconomicKey :=
  selectedZeroMinEconomicKey witness.executedInput witness.initialReserveOut
    witness.winner []

/-- Emitter-shaped validation endpoint. If a data-only witness satisfies the
strict full-mask certificate predicate, then it yields full-mask coverage,
economic-key dominance, and selected-winner empty-suffix executability. -/
theorem strictCompressedFullMaskEconomicWitness_validates
    (witness : StrictCompressedFullMaskEconomicWitness)
    (hvalid : strictCompressedFullMaskEconomicWitnessValid witness) :
    allBitsBelowSet witness.winner.maskId witness.bitCount ∧
      zeroMinEconomicKeyDominated
        (strictCompressedFullMaskEconomicWitnessFullKey witness)
        (strictCompressedFullMaskEconomicWitnessSelectedKey witness) ∧
      suffixExecutable witness.winner.selected.processedReserveIn
        witness.winner.selected.reserveOut [] := by
  exact strictCompressedFullMaskEconomicCertificate_validates hvalid

/-- Host packet shell for a strict full-mask economic witness.

The Boolean fields mirror host-side packet rails checked by the Python stress
refuter. They are modeled as explicit validity inputs here; this theorem does
not prove hash computation, JSON canonicalization, or Python-to-Lean refinement. -/
structure StrictCompressedFullMaskEmitterPacket where
  witness : StrictCompressedFullMaskEconomicWitness
  packetHashBound : Bool
  noAuthorityEffect : Bool
  winnerMembershipBound : Bool
  deriving Repr

/-- Validity predicate for the host packet shell.

This packages the non-authority rails around the existing strict full-mask
economic witness predicate. -/
def strictCompressedFullMaskEmitterPacketValid
    (packet : StrictCompressedFullMaskEmitterPacket) : Prop :=
  packet.packetHashBound = true ∧
    packet.noAuthorityEffect = true ∧
    packet.winnerMembershipBound = true ∧
    strictCompressedFullMaskEconomicWitnessValid packet.witness

/-- Full-frontier key named through the host packet shell. -/
def strictCompressedFullMaskEmitterPacketFullKey
    (packet : StrictCompressedFullMaskEmitterPacket) : ZeroMinEconomicKey :=
  strictCompressedFullMaskEconomicWitnessFullKey packet.witness

/-- Selected-winner key named through the host packet shell. -/
def strictCompressedFullMaskEmitterPacketSelectedKey
    (packet : StrictCompressedFullMaskEmitterPacket) : ZeroMinEconomicKey :=
  strictCompressedFullMaskEconomicWitnessSelectedKey packet.witness

/-- Host packet validation endpoint.

A packet satisfying the host-shell rails and the strict witness predicate yields
the no-authority flag, packet-hash binding flag, winner-membership binding flag,
bounded full-mask coverage, economic-key dominance, and empty-suffix
executability. -/
theorem strictCompressedFullMaskEmitterPacket_validates
    (packet : StrictCompressedFullMaskEmitterPacket)
    (hvalid : strictCompressedFullMaskEmitterPacketValid packet) :
    packet.packetHashBound = true ∧
      packet.noAuthorityEffect = true ∧
      packet.winnerMembershipBound = true ∧
      allBitsBelowSet packet.witness.winner.maskId packet.witness.bitCount ∧
      zeroMinEconomicKeyDominated
        (strictCompressedFullMaskEmitterPacketFullKey packet)
        (strictCompressedFullMaskEmitterPacketSelectedKey packet) ∧
      suffixExecutable packet.witness.winner.selected.processedReserveIn
        packet.witness.winner.selected.reserveOut [] := by
  rcases hvalid with ⟨hhash, hnoAuthority, hwinnerMembership, hwitness⟩
  have hwitness_validated :=
    strictCompressedFullMaskEconomicWitness_validates packet.witness hwitness
  exact ⟨hhash, hnoAuthority, hwinnerMembership,
    hwitness_validated.1, hwitness_validated.2⟩

/-- Host-emitter table shell for the strict full-mask certificate.

This is one layer closer to the concrete compressed DP emitter than the packet
shell: it names the parent, winner, full child frontier, selected mask family,
and execution metadata directly. Validity below still requires proof-carrying
range-step reachability and selected-winner dominance as explicit assumptions.
It does not construct those objects from Python tables. -/
structure StrictCompressedFullMaskEmitterTable where
  parent : MaskRecordSet
  winner : MaskRecordSet
  children : List MaskRecordSet
  bitCount : Nat
  masks : List MaskRecordSet
  initialReserveOut : Nat
  executedInput : Nat
  packetHashBound : Bool
  noAuthorityEffect : Bool
  winnerMembershipBound : Bool
  deriving Repr

/-- Interpret a host-emitter table as the strict economic witness shell. -/
def strictCompressedFullMaskEmitterTableWitness
    (table : StrictCompressedFullMaskEmitterTable) :
    StrictCompressedFullMaskEconomicWitness := {
  parent := table.parent
  winner := table.winner
  children := table.children
  bitCount := table.bitCount
  masks := table.masks
  initialReserveOut := table.initialReserveOut
  executedInput := table.executedInput
}

/-- Interpret a host-emitter table as the packet shell checked by the endpoint. -/
def strictCompressedFullMaskEmitterTablePacket
    (table : StrictCompressedFullMaskEmitterTable) :
    StrictCompressedFullMaskEmitterPacket := {
  witness := strictCompressedFullMaskEmitterTableWitness table
  packetHashBound := table.packetHashBound
  noAuthorityEffect := table.noAuthorityEffect
  winnerMembershipBound := table.winnerMembershipBound
}

/-- Validity predicate for the host-emitter table shell.

The predicate is explicit about the remaining proof obligations: recursive
range-step reachability for the full child frontier, selected-family winner
dominance, empty-suffix executability, and winner membership in the full child
frontier. -/
def strictCompressedFullMaskEmitterTableValid
    (table : StrictCompressedFullMaskEmitterTable) : Prop :=
  table.packetHashBound = true ∧
    table.noAuthorityEffect = true ∧
    table.winnerMembershipBound = true ∧
    rangeStepPathWinnerCertificate table.parent table.winner table.children
      table.bitCount table.masks table.initialReserveOut [] ∧
    suffixExecutable table.winner.selected.processedReserveIn
      table.winner.selected.reserveOut [] ∧
    table.winner ∈ table.children

/-- Host-emitter table endpoint.

A valid table shell constructs a valid packet shell, then inherits the packet
endpoint: hash-bound and no-authority rails, winner-membership binding, bounded
full-mask coverage, fixed-input economic-key dominance, and empty-suffix
executability. -/
theorem strictCompressedFullMaskEmitterTable_validates
    (table : StrictCompressedFullMaskEmitterTable)
    (hvalid : strictCompressedFullMaskEmitterTableValid table) :
    strictCompressedFullMaskEmitterPacketValid
        (strictCompressedFullMaskEmitterTablePacket table) ∧
      (strictCompressedFullMaskEmitterTablePacket table).packetHashBound = true ∧
      (strictCompressedFullMaskEmitterTablePacket table).noAuthorityEffect = true ∧
      (strictCompressedFullMaskEmitterTablePacket table).winnerMembershipBound = true ∧
      allBitsBelowSet table.winner.maskId table.bitCount ∧
      zeroMinEconomicKeyDominated
        (strictCompressedFullMaskEmitterPacketFullKey
          (strictCompressedFullMaskEmitterTablePacket table))
        (strictCompressedFullMaskEmitterPacketSelectedKey
          (strictCompressedFullMaskEmitterTablePacket table)) ∧
      suffixExecutable table.winner.selected.processedReserveIn
        table.winner.selected.reserveOut [] := by
  rcases hvalid with
    ⟨hhash, hnoAuthority, hwinnerMembership, hrange, hexec, hwinnerChild⟩
  have hstrict :
      strictRangeStepPathEconomicCertificate table.parent table.winner
        table.children table.bitCount table.masks table.initialReserveOut [] :=
    ⟨hrange, hexec⟩
  have heconomic :
      strictCompressedFullMaskEconomicCertificate table.parent table.winner
        table.children table.bitCount table.masks table.initialReserveOut :=
    ⟨hstrict, hwinnerChild⟩
  have hwitness :
      strictCompressedFullMaskEconomicWitnessValid
        (strictCompressedFullMaskEmitterTableWitness table) := by
    unfold strictCompressedFullMaskEconomicWitnessValid
      strictCompressedFullMaskEmitterTableWitness
    exact heconomic
  have hpacket :
      strictCompressedFullMaskEmitterPacketValid
        (strictCompressedFullMaskEmitterTablePacket table) := by
    unfold strictCompressedFullMaskEmitterPacketValid
      strictCompressedFullMaskEmitterTablePacket
    exact ⟨hhash, hnoAuthority, hwinnerMembership, hwitness⟩
  have hvalidated :=
    strictCompressedFullMaskEmitterPacket_validates
      (strictCompressedFullMaskEmitterTablePacket table)
      hpacket
  exact ⟨hpacket, hvalidated⟩

/-- Finite subset-mask pruning lift.

If every abstract subset mask satisfies the local pruning invariant, then the
best suffix output available from all full-state records across the mask family
is no better than the best suffix output available from the compressed
representatives. This is the mask-family aggregation component of the full
subset-mask induction proof. -/
theorem bestFullSuffixOutputAcrossMasks_le_selected
    {initialReserveOut : Nat}
    {masks : List MaskRecordSet}
    {suffix : List ExactInStep}
    (hinvariant : ∀ mask, mask ∈ masks -> maskPruningInvariant mask) :
    bestFullSuffixOutputAcrossMasks initialReserveOut masks suffix ≤
      bestSelectedSuffixOutputAcrossMasks initialReserveOut masks suffix := by
  unfold bestFullSuffixOutputAcrossMasks bestSelectedSuffixOutputAcrossMasks
  apply foldlMax_le_bound
  · exact Nat.zero_le _
  · intro value hvalue
    rw [List.mem_map] at hvalue
    rcases hvalue with ⟨mask, hmask, rfl⟩
    have hlocal :
        maskFullBestSuffixOutput initialReserveOut mask suffix ≤
          maskSelectedSuffixOutput initialReserveOut mask suffix :=
      maskFullBestSuffixOutput_le_selected
        (initialReserveOut := initialReserveOut)
        (mask := mask)
        (suffix := suffix)
        (hinvariant mask hmask)
    have hselected_mem :
        maskSelectedSuffixOutput initialReserveOut mask suffix ∈
        masks.map (fun candidate =>
            maskSelectedSuffixOutput initialReserveOut candidate suffix) := by
      exact List.mem_map.mpr ⟨mask, hmask, rfl⟩
    exact Nat.le_trans hlocal (mem_le_foldlMax (acc := 0) hselected_mem)

/-- Observed full-mask child-frontier validity for a host-emitter table.

This predicate matches the host witness packets more directly than the
recursive range-step certificate: every observed child already carries bounded
full-mask coverage and a local pruning invariant, and the supplied winner
dominates the observed child frontier. It does not prove how the child frontier
was generated, nor does it prove the recursive subset-mask induction. -/
def strictObservedFullMaskEmitterTableValid
    (table : StrictCompressedFullMaskEmitterTable) : Prop :=
  table.packetHashBound = true ∧
    table.noAuthorityEffect = true ∧
    table.winnerMembershipBound = true ∧
    (∀ child, child ∈ table.children ->
      allBitsBelowSet child.maskId table.bitCount ∧ maskPruningInvariant child) ∧
    selectedFamilyOutputWinner table.winner table.children table.initialReserveOut [] ∧
    suffixExecutable table.winner.selected.processedReserveIn
      table.winner.selected.reserveOut [] ∧
    table.winner ∈ table.children

/-- Observed child-frontier endpoint.

If a host-emitter table supplies full-mask coverage and local pruning for each
observed child, plus a selected winner that dominates the observed frontier,
then the observed full frontier's zero-min economic key is dominated by the
winner at fixed executed input. -/
theorem strictObservedFullMaskEmitterTable_validates
    (table : StrictCompressedFullMaskEmitterTable)
    (hvalid : strictObservedFullMaskEmitterTableValid table) :
    table.packetHashBound = true ∧
      table.noAuthorityEffect = true ∧
      table.winnerMembershipBound = true ∧
      allBitsBelowSet table.winner.maskId table.bitCount ∧
      zeroMinEconomicKeyDominated
        (fullFrontierZeroMinEconomicKey table.executedInput
          table.initialReserveOut table.children [])
        (selectedZeroMinEconomicKey table.executedInput
          table.initialReserveOut table.winner []) ∧
      suffixExecutable table.winner.selected.processedReserveIn
        table.winner.selected.reserveOut [] := by
  rcases hvalid with
    ⟨hhash, hnoAuthority, hwinnerMembership, hchildren, hwinner, hexec, hwinnerChild⟩
  have hcoverage : allBitsBelowSet table.winner.maskId table.bitCount :=
    (hchildren table.winner hwinnerChild).1
  have hinvariant :
      ∀ child, child ∈ table.children -> maskPruningInvariant child := by
    intro child hchild
    exact (hchildren child hchild).2
  have hfull_to_selected :
      bestFullSuffixOutputAcrossMasks table.initialReserveOut table.children [] ≤
        bestSelectedSuffixOutputAcrossMasks table.initialReserveOut table.children [] :=
    bestFullSuffixOutputAcrossMasks_le_selected
      (initialReserveOut := table.initialReserveOut)
      (masks := table.children)
      (suffix := [])
      hinvariant
  have hselected_to_winner :
      bestSelectedSuffixOutputAcrossMasks table.initialReserveOut table.children [] ≤
        maskSelectedSuffixOutput table.initialReserveOut table.winner [] :=
    selectedFamilyOutputWinner_bounds_selected_family hwinner
  have hdominance :
      zeroMinEconomicKeyDominated
        (fullFrontierZeroMinEconomicKey table.executedInput
          table.initialReserveOut table.children [])
        (selectedZeroMinEconomicKey table.executedInput
          table.initialReserveOut table.winner []) := by
    unfold zeroMinEconomicKeyDominated fullFrontierZeroMinEconomicKey
      selectedZeroMinEconomicKey
    exact ⟨Nat.le_refl table.executedInput,
      Nat.le_trans hfull_to_selected hselected_to_winner⟩
  exact ⟨hhash, hnoAuthority, hwinnerMembership, hcoverage, hdominance, hexec⟩

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

/-- Concrete non-vacuity witness for finite subset-mask pruning aggregation. -/
theorem witness_bestFullSuffixOutputAcrossMasks_le_selected :
    let suffix : List ExactInStep := [
      ⟨100, 99⟩,
      ⟨200, 199⟩
    ]
    let maskA : MaskRecordSet := {
      maskId := 1,
      selected := ⟨1100, 800⟩,
      records := [⟨1100, 900⟩, ⟨1100, 1100⟩]
    }
    let maskB : MaskRecordSet := {
      maskId := 2,
      selected := ⟨1300, 700⟩,
      records := [⟨1300, 850⟩]
    }
    let masks : List MaskRecordSet := [maskA, maskB]
    bestFullSuffixOutputAcrossMasks 1200 masks suffix ≤
      bestSelectedSuffixOutputAcrossMasks 1200 masks suffix := by
  native_decide

/-- Concrete non-vacuity witness for the reachable pruned range-mask endpoint. -/
theorem witness_reachablePrunedRangeMask_covers_and_bounds :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    reachablePrunedRangeMask parent child 1 ∧
      allBitsBelowSet child.maskId 1 ∧
        maskFullBestSuffixOutput 1000 child [] ≤
          maskSelectedSuffixOutput 1000 child [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  have hpath : maskRecordPath parent (List.range 1) child := by
    simpa [parent, child, maskRecordPath] using witness_bitMaskStep_noop.2
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hmask : reachablePrunedRangeMask parent child 1 := ⟨hpath, hinvariant⟩
  exact ⟨hmask,
    reachablePrunedRangeMask_covers_and_bounds
      (initialReserveOut := 1000)
      (suffix := [])
      hmask⟩

/-- Concrete non-vacuity witness for the reachable full-mask family endpoint. -/
theorem witness_reachablePrunedFullMaskInFamily_covers_and_bounds_family :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let masks : List MaskRecordSet := [child]
    reachablePrunedFullMaskInFamily parent child 1 masks ∧
      allBitsBelowSet child.maskId 1 ∧
        maskFullBestSuffixOutput 1000 child [] ≤
          bestSelectedSuffixOutputAcrossMasks 1000 masks [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let masks : List MaskRecordSet := [child]
  have hpath : maskRecordPath parent (List.range 1) child := by
    simpa [parent, child, maskRecordPath] using witness_bitMaskStep_noop.2
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedRangeMask parent child 1 := ⟨hpath, hinvariant⟩
  have hfull : reachablePrunedFullMaskInFamily parent child 1 masks := by
    exact ⟨hreachable, by simp [masks]⟩
  exact ⟨hfull,
    reachablePrunedFullMaskInFamily_covers_and_bounds_family
      (initialReserveOut := 1000)
      (suffix := [])
      hfull⟩

/-- Concrete non-vacuity witness for the reachable full-mask list endpoint. -/
theorem witness_reachablePrunedFullMaskListInFamily_covers_and_bounds_family :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    reachablePrunedFullMaskListInFamily parent children 1 masks ∧
      (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
        bestFullSuffixOutputAcrossMasks 1000 children [] ≤
          bestSelectedSuffixOutputAcrossMasks 1000 masks [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hpath : maskRecordPath parent (List.range 1) child := by
    simpa [parent, child, maskRecordPath] using witness_bitMaskStep_noop.2
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedRangeMask parent child 1 := ⟨hpath, hinvariant⟩
  have hfull : reachablePrunedFullMaskInFamily parent child 1 masks := by
    exact ⟨hreachable, by simp [masks]⟩
  have hlist : reachablePrunedFullMaskListInFamily parent children 1 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  exact ⟨hlist,
    reachablePrunedFullMaskListInFamily_covers_and_bounds_family
      (initialReserveOut := 1000)
      (suffix := [])
      hlist⟩

/-- Concrete non-vacuity witness for the selected-family winner endpoint. -/
theorem witness_reachablePrunedFullMaskListInFamily_bounds_selected_winner :
    let record : ProcessedRecord := ⟨100, 90⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    selectedFamilyOutputWinner child masks 1000 [] ∧
      (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
        bestFullSuffixOutputAcrossMasks 1000 children [] ≤
          maskSelectedSuffixOutput 1000 child [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hpath : maskRecordPath parent (List.range 1) child := by
    simpa [parent, child, maskRecordPath] using witness_bitMaskStep_noop.2
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedRangeMask parent child 1 := ⟨hpath, hinvariant⟩
  have hfull : reachablePrunedFullMaskInFamily parent child 1 masks := by
    exact ⟨hreachable, by simp [masks]⟩
  have hlist : reachablePrunedFullMaskListInFamily parent children 1 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  have hwinner : selectedFamilyOutputWinner child masks 1000 [] := by
    constructor
    · simp [masks]
    · intro candidate hcandidate
      simp only [masks, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  exact ⟨hwinner,
    reachablePrunedFullMaskListInFamily_covers_and_bounds_selected_winner
      (initialReserveOut := 1000)
      (suffix := [])
      hlist
      hwinner⟩

/-- Concrete non-vacuity witness for the compressed winner certificate endpoint. -/
theorem witness_compressedWinnerCertificate_covers_and_bounds :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    compressedWinnerCertificate parent child children masks 1 1000 [] ∧
      (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
        bestFullSuffixOutputAcrossMasks 1000 children [] ≤
          maskSelectedSuffixOutput 1000 child [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hpath : maskRecordPath parent (List.range 1) child := by
    simpa [parent, child, maskRecordPath] using witness_bitMaskStep_noop.2
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedRangeMask parent child 1 := ⟨hpath, hinvariant⟩
  have hfull : reachablePrunedFullMaskInFamily parent child 1 masks := by
    exact ⟨hreachable, by simp [masks]⟩
  have hlist : reachablePrunedFullMaskListInFamily parent children 1 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  have hwinner : selectedFamilyOutputWinner child masks 1000 [] := by
    constructor
    · simp [masks]
    · intro candidate hcandidate
      simp only [masks, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hcert : compressedWinnerCertificate parent child children masks 1 1000 [] :=
    ⟨hlist, hwinner⟩
  exact ⟨hcert, compressedWinnerCertificate_covers_and_bounds hcert⟩

/-- Concrete non-vacuity witness for the one-step winner certificate endpoint. -/
theorem witness_stepWinnerCertificate_extends_prefix_and_bounds :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    allBitsBelowSet parent.maskId 0 ∧
      stepWinnerCertificate parent child children 0 masks 1000 [] ∧
        (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
          bestFullSuffixOutputAcrossMasks 1000 children [] ≤
            maskSelectedSuffixOutput 1000 child [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hprefix : allBitsBelowSet parent.maskId 0 := by
    intro bitIndex hlt
    omega
  have hstep : maskRecordStep parent child 0 := by
    simpa [parent, child, maskRecordStep] using witness_bitMaskStep_noop.1
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedStepMask parent child 0 := ⟨hstep, hinvariant⟩
  have hfull : reachablePrunedStepMaskInFamily parent child 0 masks := by
    exact ⟨hreachable, by simp [masks]⟩
  have hlist : reachablePrunedStepMaskListInFamily parent children 0 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  have hwinner : selectedFamilyOutputWinner child masks 1000 [] := by
    constructor
    · simp [masks]
    · intro candidate hcandidate
      simp only [masks, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hcert : stepWinnerCertificate parent child children 0 masks 1000 [] :=
    ⟨hlist, hwinner⟩
  exact ⟨hprefix, hcert, stepWinnerCertificate_extends_prefix_and_bounds hprefix hcert⟩

/-- Concrete non-vacuity witness for the recursive range-step winner endpoint. -/
theorem witness_rangeStepPathWinnerCertificate_covers_and_bounds :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    rangeStepPathWinnerCertificate parent child children 1 masks 1000 [] ∧
      (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
        bestFullSuffixOutputAcrossMasks 1000 children [] ≤
          maskSelectedSuffixOutput 1000 child [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hstep : maskRecordStep parent child 0 := by
    simpa [parent, child, maskRecordStep] using witness_bitMaskStep_noop.1
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedStepMask parent child 0 := ⟨hstep, hinvariant⟩
  have hbase : reachablePrunedStepPath child [] child := ⟨rfl, hinvariant⟩
  have hpath_list : reachablePrunedStepPath parent [0] child := by
    exact ⟨child, hreachable, hbase⟩
  have hpath : reachablePrunedStepPath parent (List.range 1) child := by
    simpa using hpath_list
  have hfull : reachablePrunedRangeStepPathInFamily parent child 1 masks := by
    exact ⟨hpath, by simp [masks]⟩
  have hlist : reachablePrunedRangeStepPathListInFamily parent children 1 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  have hwinner : selectedFamilyOutputWinner child masks 1000 [] := by
    constructor
    · simp [masks]
    · intro candidate hcandidate
      simp only [masks, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hcert : rangeStepPathWinnerCertificate parent child children 1 masks 1000 [] :=
    ⟨hlist, hwinner⟩
  exact ⟨hcert, rangeStepPathWinnerCertificate_covers_and_bounds hcert⟩

/-- Concrete non-vacuity witness for the strict executable economic-key endpoint. -/
theorem witness_strictRangeStepPathEconomicCertificate_covers_bounds_and_executes :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    strictRangeStepPathEconomicCertificate parent child children 1 masks 1000 [] ∧
      (∀ candidate, candidate ∈ children -> allBitsBelowSet candidate.maskId 1) ∧
        zeroMinEconomicKeyDominated
          (fullFrontierZeroMinEconomicKey 100 1000 children [])
          (selectedZeroMinEconomicKey 100 1000 child []) ∧
        suffixExecutable child.selected.processedReserveIn child.selected.reserveOut [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  have hstep : maskRecordStep parent child 0 := by
    simpa [parent, child, maskRecordStep] using witness_bitMaskStep_noop.1
  have hinvariant : maskPruningInvariant child := by
    unfold child maskPruningInvariant
    constructor
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hreachable : reachablePrunedStepMask parent child 0 := ⟨hstep, hinvariant⟩
  have hbase : reachablePrunedStepPath child [] child := ⟨rfl, hinvariant⟩
  have hpath_list : reachablePrunedStepPath parent [0] child := by
    exact ⟨child, hreachable, hbase⟩
  have hpath : reachablePrunedStepPath parent (List.range 1) child := by
    simpa using hpath_list
  have hfull : reachablePrunedRangeStepPathInFamily parent child 1 masks := by
    exact ⟨hpath, by simp [masks]⟩
  have hlist : reachablePrunedRangeStepPathListInFamily parent children 1 masks := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    exact hfull
  have hwinner : selectedFamilyOutputWinner child masks 1000 [] := by
    constructor
    · simp [masks]
    · intro candidate hcandidate
      simp only [masks, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hrange : rangeStepPathWinnerCertificate parent child children 1 masks 1000 [] :=
    ⟨hlist, hwinner⟩
  have hexec : suffixExecutable child.selected.processedReserveIn child.selected.reserveOut [] := by
    simp [suffixExecutable]
  have hcert : strictRangeStepPathEconomicCertificate parent child children 1 masks 1000 [] :=
    ⟨hrange, hexec⟩
  exact ⟨hcert,
    strictRangeStepPathEconomicCertificate_covers_bounds_and_executes
      (executedInput := 100)
      hcert⟩

/-- Concrete non-vacuity witness for the strict compressed full-mask economic
emitter endpoint. -/
theorem witness_strictCompressedFullMaskEconomicWitness_validates :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    let witness : StrictCompressedFullMaskEconomicWitness := {
      parent := parent
      winner := child
      children := children
      bitCount := 1
      masks := masks
      initialReserveOut := 1000
      executedInput := 100
    }
    strictCompressedFullMaskEconomicWitnessValid witness ∧
      allBitsBelowSet witness.winner.maskId witness.bitCount ∧
        zeroMinEconomicKeyDominated
          (strictCompressedFullMaskEconomicWitnessFullKey witness)
          (strictCompressedFullMaskEconomicWitnessSelectedKey witness) ∧
        suffixExecutable witness.winner.selected.processedReserveIn
          witness.winner.selected.reserveOut [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  let witness : StrictCompressedFullMaskEconomicWitness := {
    parent := parent
    winner := child
    children := children
    bitCount := 1
    masks := masks
    initialReserveOut := 1000
    executedInput := 100
  }
  have hstrict :
      strictRangeStepPathEconomicCertificate parent child children 1 masks 1000 [] := by
    simpa [record, parent, child, children, masks] using
      witness_strictRangeStepPathEconomicCertificate_covers_bounds_and_executes.1
  have hvalid : strictCompressedFullMaskEconomicWitnessValid witness := by
    unfold strictCompressedFullMaskEconomicWitnessValid
      strictCompressedFullMaskEconomicCertificate witness
    exact ⟨hstrict, by simp [children]⟩
  exact ⟨hvalid, strictCompressedFullMaskEconomicWitness_validates witness hvalid⟩

/-- Concrete non-vacuity witness for the host packet-shell endpoint. -/
theorem witness_strictCompressedFullMaskEmitterPacket_validates :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    let witness : StrictCompressedFullMaskEconomicWitness := {
      parent := parent
      winner := child
      children := children
      bitCount := 1
      masks := masks
      initialReserveOut := 1000
      executedInput := 100
    }
    let packet : StrictCompressedFullMaskEmitterPacket := {
      witness := witness
      packetHashBound := true
      noAuthorityEffect := true
      winnerMembershipBound := true
    }
    strictCompressedFullMaskEmitterPacketValid packet ∧
      packet.packetHashBound = true ∧
        packet.noAuthorityEffect = true ∧
        packet.winnerMembershipBound = true ∧
        allBitsBelowSet packet.witness.winner.maskId packet.witness.bitCount ∧
        zeroMinEconomicKeyDominated
          (strictCompressedFullMaskEmitterPacketFullKey packet)
          (strictCompressedFullMaskEmitterPacketSelectedKey packet) ∧
        suffixExecutable packet.witness.winner.selected.processedReserveIn
          packet.witness.winner.selected.reserveOut [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  let witness : StrictCompressedFullMaskEconomicWitness := {
    parent := parent
    winner := child
    children := children
    bitCount := 1
    masks := masks
    initialReserveOut := 1000
    executedInput := 100
  }
  let packet : StrictCompressedFullMaskEmitterPacket := {
    witness := witness
    packetHashBound := true
    noAuthorityEffect := true
    winnerMembershipBound := true
  }
  have hwitness_valid : strictCompressedFullMaskEconomicWitnessValid witness := by
    simpa [record, parent, child, children, masks, witness] using
      witness_strictCompressedFullMaskEconomicWitness_validates.1
  have hpacket_valid : strictCompressedFullMaskEmitterPacketValid packet := by
    unfold strictCompressedFullMaskEmitterPacketValid
    exact ⟨rfl, rfl, rfl, hwitness_valid⟩
  exact ⟨hpacket_valid,
    strictCompressedFullMaskEmitterPacket_validates packet hpacket_valid⟩

/-- Concrete non-vacuity witness for the host-emitter table endpoint. -/
theorem witness_strictCompressedFullMaskEmitterTable_validates :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let masks : List MaskRecordSet := [child]
    let table : StrictCompressedFullMaskEmitterTable := {
      parent := parent
      winner := child
      children := children
      bitCount := 1
      masks := masks
      initialReserveOut := 1000
      executedInput := 100
      packetHashBound := true
      noAuthorityEffect := true
      winnerMembershipBound := true
    }
    strictCompressedFullMaskEmitterTableValid table ∧
      strictCompressedFullMaskEmitterPacketValid
        (strictCompressedFullMaskEmitterTablePacket table) ∧
      (strictCompressedFullMaskEmitterTablePacket table).packetHashBound = true ∧
      (strictCompressedFullMaskEmitterTablePacket table).noAuthorityEffect = true ∧
      (strictCompressedFullMaskEmitterTablePacket table).winnerMembershipBound = true ∧
      allBitsBelowSet table.winner.maskId table.bitCount ∧
      zeroMinEconomicKeyDominated
        (strictCompressedFullMaskEmitterPacketFullKey
          (strictCompressedFullMaskEmitterTablePacket table))
        (strictCompressedFullMaskEmitterPacketSelectedKey
          (strictCompressedFullMaskEmitterTablePacket table)) ∧
      suffixExecutable table.winner.selected.processedReserveIn
        table.winner.selected.reserveOut [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let masks : List MaskRecordSet := [child]
  let table : StrictCompressedFullMaskEmitterTable := {
    parent := parent
    winner := child
    children := children
    bitCount := 1
    masks := masks
    initialReserveOut := 1000
    executedInput := 100
    packetHashBound := true
    noAuthorityEffect := true
    winnerMembershipBound := true
  }
  have hstrict :
      strictRangeStepPathEconomicCertificate parent child children 1 masks 1000 [] := by
    simpa [record, parent, child, children, masks] using
      witness_strictRangeStepPathEconomicCertificate_covers_bounds_and_executes.1
  rcases hstrict with ⟨hrange, hexec⟩
  have htable : strictCompressedFullMaskEmitterTableValid table := by
    unfold strictCompressedFullMaskEmitterTableValid
    exact ⟨rfl, rfl, rfl, hrange, hexec, by simp [table, children]⟩
  exact ⟨htable, strictCompressedFullMaskEmitterTable_validates table htable⟩

/-- Concrete non-vacuity witness for the observed full-mask child-frontier endpoint. -/
theorem witness_strictObservedFullMaskEmitterTable_validates :
    let record : ProcessedRecord := ⟨100, 90⟩
    let parent : MaskRecordSet := ⟨1, record, [record]⟩
    let child : MaskRecordSet := ⟨1, record, [record]⟩
    let children : List MaskRecordSet := [child]
    let table : StrictCompressedFullMaskEmitterTable := {
      parent := parent
      winner := child
      children := children
      bitCount := 1
      masks := children
      initialReserveOut := 1000
      executedInput := 100
      packetHashBound := true
      noAuthorityEffect := true
      winnerMembershipBound := true
    }
    strictObservedFullMaskEmitterTableValid table ∧
      table.packetHashBound = true ∧
        table.noAuthorityEffect = true ∧
        table.winnerMembershipBound = true ∧
        allBitsBelowSet table.winner.maskId table.bitCount ∧
        zeroMinEconomicKeyDominated
          (fullFrontierZeroMinEconomicKey table.executedInput
            table.initialReserveOut table.children [])
          (selectedZeroMinEconomicKey table.executedInput
            table.initialReserveOut table.winner []) ∧
        suffixExecutable table.winner.selected.processedReserveIn
          table.winner.selected.reserveOut [] := by
  let record : ProcessedRecord := ⟨100, 90⟩
  let parent : MaskRecordSet := ⟨1, record, [record]⟩
  let child : MaskRecordSet := ⟨1, record, [record]⟩
  let children : List MaskRecordSet := [child]
  let table : StrictCompressedFullMaskEmitterTable := {
    parent := parent
    winner := child
    children := children
    bitCount := 1
    masks := children
    initialReserveOut := 1000
    executedInput := 100
    packetHashBound := true
    noAuthorityEffect := true
    winnerMembershipBound := true
  }
  have hchildren :
      ∀ candidate, candidate ∈ children ->
        allBitsBelowSet candidate.maskId 1 ∧ maskPruningInvariant candidate := by
    intro candidate hcandidate
    simp only [children, List.mem_singleton] at hcandidate
    subst candidate
    constructor
    · unfold allBitsBelowSet
      intro bitIndex hlt
      have hzero : bitIndex = 0 := by omega
      subst bitIndex
      unfold child maskHasBit
      native_decide
    · unfold child maskPruningInvariant
      constructor
      · intro candidate hcandidate
        simp only [List.mem_singleton] at hcandidate
        subst candidate
        rfl
      · intro candidate hcandidate
        simp only [List.mem_singleton] at hcandidate
        subst candidate
        rfl
  have hwinner : selectedFamilyOutputWinner child children 1000 [] := by
    constructor
    · simp [children]
    · intro candidate hcandidate
      simp only [children, List.mem_singleton] at hcandidate
      subst candidate
      rfl
  have hexec : suffixExecutable child.selected.processedReserveIn child.selected.reserveOut [] := by
    simp [suffixExecutable]
  have hvalid : strictObservedFullMaskEmitterTableValid table := by
    unfold strictObservedFullMaskEmitterTableValid
    exact ⟨rfl, rfl, rfl, by simpa [table] using hchildren, by simpa [table] using hwinner,
      by simpa [table] using hexec, by simp [table, children]⟩
  exact ⟨hvalid, strictObservedFullMaskEmitterTable_validates table hvalid⟩

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
