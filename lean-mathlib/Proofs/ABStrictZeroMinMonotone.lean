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

/-- Reserve-in after a fixed suffix is a function of the gross input multiset
sum. This records the order-independence component used by the induction
argument. -/
def reserveInAfterGross (initialReserveIn : Nat) (steps : List ExactInStep) : Nat :=
  initialReserveIn + (steps.map ExactInStep.grossIn).sum

/-- Reversing a fixed suffix preserves the total gross input contribution to
the input reserve. -/
theorem reserveInAfterGross_reverse (initialReserveIn : Nat) (steps : List ExactInStep) :
    reserveInAfterGross initialReserveIn steps.reverse =
      reserveInAfterGross initialReserveIn steps := by
  simp [reserveInAfterGross]

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
