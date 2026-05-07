import Proofs.CPMMInvariants
import Proofs.CPMMEdgeRounding
import Proofs.FeeAwareBatchKGap
import Proofs.RoundingErrorBound
import Mathlib.Tactic

/-!
# CPMM Runtime Certificate Bridge

This file packages existing integer CPMM facts into a runtime-facing certificate
shape. The goal is not to re-prove continuous CPMM algebra. The goal is to state
what an executable integer swap must certify so the runtime step is inside the
proved safety envelope:

* output is the floor-division output,
* ceiling/floor output differ by at most one output unit,
* output cannot overdeliver the output reserve,
* fee-in-pool execution has an exact nonnegative K-gap,
* route-level rounding budgets can be checked by a recurrence certificate.
-/

namespace CPMMRuntimeCertificateBridge

open CPMMInvariants

/-- Runtime-side swap input. All arithmetic here is natural-number arithmetic.
For fixed-width runtimes, a separate machine-integer bridge must prove that these
natural-number operations are exactly represented by the implementation. -/
structure RuntimeSwapInput where
  rin : Nat
  rout : Nat
  gross : Nat
  feeBps : Nat
  deriving Repr, DecidableEq

/-- The fee charged by the executable formula. -/
def runtimeFee (i : RuntimeSwapInput) : Nat :=
  computeFee i.gross i.feeBps

/-- The net amount used for the CPMM quote. The pool still receives `gross`. -/
def runtimeNet (i : RuntimeSwapInput) : Nat :=
  netAmount i.gross i.feeBps

/-- The actual integer runtime output: floor division. -/
def runtimeOut (i : RuntimeSwapInput) : Nat :=
  swapOutput i.rin i.rout (runtimeNet i)

/-- The favorable ceiling envelope for the same quote numerator and denominator. -/
def runtimeCeilOut (i : RuntimeSwapInput) : Nat :=
  CPMMEdgeRounding.ceilSwapOut i.rin i.rout (runtimeNet i)

/-- The product before the runtime step. -/
def runtimeKBefore (i : RuntimeSwapInput) : Nat :=
  kValue i.rin i.rout

/-- The product after the runtime step. The input reserve receives gross input. -/
def runtimeKAfter (i : RuntimeSwapInput) : Nat :=
  kValue (i.rin + i.gross) (i.rout - runtimeOut i)

/-- The exact fee-aware K-gap carried by the runtime formula. -/
def runtimeKGap (i : RuntimeSwapInput) : Nat :=
  FeeAwareBatchKGap.feeAwareKGap
    ⟨i.rin, i.rout⟩ i.gross i.feeBps

/-- A compact certificate shape that a runtime can emit or a checker can
recompute. The proof below treats these as public fields and requires them to
match the canonical formulas exactly. -/
structure RuntimeSwapCertificate where
  fee : Nat
  net : Nat
  out : Nat
  ceilOut : Nat
  kBefore : Nat
  kAfter : Nat
  kGap : Nat
  deriving Repr, DecidableEq

/-- The certificate is accepted exactly when every field matches the canonical
integer runtime formula. -/
def VerifiesRuntimeSwap (i : RuntimeSwapInput) (c : RuntimeSwapCertificate) : Prop :=
  c.fee = runtimeFee i ∧
  c.net = runtimeNet i ∧
  c.out = runtimeOut i ∧
  c.ceilOut = runtimeCeilOut i ∧
  c.kBefore = runtimeKBefore i ∧
  c.kAfter = runtimeKAfter i ∧
  c.kGap = runtimeKGap i

/-- The runtime output cannot exceed the output reserve. -/
theorem runtime_out_no_overdelivery (i : RuntimeSwapInput) :
    runtimeOut i ≤ i.rout := by
  simpa [runtimeOut] using
    (CPMMInvariants.swap_output_le_reserve
      (rin := i.rin) (rout := i.rout) (net := runtimeNet i))

/-- Floor output is below the favorable ceiling envelope. -/
theorem runtime_floor_le_ceiling (i : RuntimeSwapInput) :
    runtimeOut i ≤ runtimeCeilOut i := by
  simpa [runtimeOut, runtimeCeilOut, CPMMInvariants.swapOutput,
    AntiFragmentation.swapOut] using
    CPMMEdgeRounding.cpmm_floor_le_ceil i.rin i.rout (runtimeNet i)

/-- The favorable ceiling envelope is at most one output unit above runtime. -/
theorem runtime_ceiling_le_floor_plus_one (i : RuntimeSwapInput) :
    runtimeCeilOut i ≤ runtimeOut i + 1 := by
  simpa [runtimeOut, runtimeCeilOut, CPMMInvariants.swapOutput,
    AntiFragmentation.swapOut] using
    CPMMEdgeRounding.cpmm_edge_gap_le_one i.rin i.rout (runtimeNet i)

/-- Exact fee-aware K accounting for one executable runtime step. -/
theorem runtime_k_gap_exact (i : RuntimeSwapInput)
    (hFeeBps : i.feeBps ≤ 10000) :
    runtimeKAfter i = runtimeKBefore i + runtimeKGap i := by
  simpa [runtimeKAfter, runtimeKBefore, runtimeKGap, runtimeOut,
    CPMMInvariants.kValue, AntiFragmentation.kValue, CPMMInvariants.swapOutput,
    AntiFragmentation.swapOut] using
    FeeAwareBatchKGap.feeSwap_K_gap_exact
      (p := ⟨i.rin, i.rout⟩) (gross := i.gross)
      (fee_bps := i.feeBps) hFeeBps

/-- K is nondecreasing for every certified runtime step with fee rate at most
10000 bps. -/
theorem runtime_k_nondec (i : RuntimeSwapInput)
    (hFeeBps : i.feeBps ≤ 10000) :
    runtimeKBefore i ≤ runtimeKAfter i := by
  rw [runtime_k_gap_exact i hFeeBps]
  omega

/-- The compact certificate is sound for the single-step runtime safety
envelope. -/
theorem verified_runtime_swap_certificate_sound
    (i : RuntimeSwapInput) (c : RuntimeSwapCertificate)
    (hFeeBps : i.feeBps ≤ 10000)
    (hCert : VerifiesRuntimeSwap i c) :
    c.out ≤ i.rout ∧
    c.out ≤ c.ceilOut ∧
    c.ceilOut ≤ c.out + 1 ∧
    c.kAfter = c.kBefore + c.kGap ∧
    c.kBefore ≤ c.kAfter := by
  rcases hCert with
    ⟨hFee, hNet, hOut, hCeil, hBefore, hAfter, hGap⟩
  constructor
  · rw [hOut]
    exact runtime_out_no_overdelivery i
  constructor
  · rw [hOut, hCeil]
    exact runtime_floor_le_ceiling i
  constructor
  · rw [hOut, hCeil]
    exact runtime_ceiling_le_floor_plus_one i
  constructor
  · rw [hAfter, hBefore, hGap]
    exact runtime_k_gap_exact i hFeeBps
  · rw [hBefore, hAfter]
    exact runtime_k_nondec i hFeeBps

/-- Route-level rounding budgets are sound when a checker supplies the base case
and the step recurrence. This theorem deliberately stays abstract over the route
metric: the caller must define `gap` in the same units the certificate claims. -/
theorem route_rounding_budget_sound
    (gap : Nat → Int) (C : Int)
    (hC : 1 ≤ C)
    (hBase : gap 1 ≤ 1)
    (hStep : ∀ k, 1 ≤ k → gap (k + 1) ≤ gap k + C)
    (k : Nat) (hk : 1 ≤ k) :
    gap k ≤ C * (k : Int) - (C - 1) :=
  Proofs.RoundingErrorBound.rounding_gap_bound_general gap C hC hBase hStep k hk

/-- The common Lipschitz-1 route budget: if each accepted hop increases the
route error by at most one unit, the route error is bounded by its length. -/
theorem route_rounding_lipschitz_budget_sound
    (gap : Nat → Int)
    (hBase : gap 1 ≤ 1)
    (hStep : ∀ k, 1 ≤ k → gap (k + 1) ≤ gap k + 1)
    (k : Nat) (hk : 1 ≤ k) :
    gap k ≤ (k : Int) :=
  Proofs.RoundingErrorBound.rounding_gap_lipschitz_bound gap hBase hStep k hk

/-- Non-vacuity witness matching the motivating example:
pool `(1000,1000)`, gross input `100`, zero fee. -/
theorem witness_zero_fee_runtime_bridge :
    let i : RuntimeSwapInput :=
      ⟨1000, 1000, 100, 0⟩
    runtimeOut i = 90 ∧
    runtimeCeilOut i = 91 ∧
    runtimeKBefore i = 1000000 ∧
    runtimeKAfter i = 1001000 ∧
    runtimeKGap i = 1000 := by
  native_decide

end CPMMRuntimeCertificateBridge
