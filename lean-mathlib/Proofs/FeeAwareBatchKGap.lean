import Proofs.FeeAwareAntiFragmentation
import Mathlib.Tactic

/-!
# Fee-Aware Batch K-Gap Telescoping

**world-model promotion**: `fee_aware_batch_k_gap_accounting` (PROPOSED → PROVED)

**THEOREM**: For a CPMM pool executing a batch of fee-in-pool swaps at rate
`fee_bps ≤ 10000`, the final product invariant K equals the initial K plus the
sum of per-step fee-aware K-gaps:

  K(final) = K(init) + Σᵢ FeeAwareKGap(sᵢ, grossᵢ, fee_bps)

where each per-step gap decomposes as:

  FeeAwareKGap(s, gross, bps) = (s.ry * net) % (s.rx + net) + fee * (s.ry - out)
                                 \___ zero-fee remainder ___/   \_ fee bonus _/

This is the fee-aware generalization of `executeBatchSwaps_K_gap_sum` from
`BatchCPMMUnification.lean`, completing SHAPE_OPTIMIZATION_NOTES item [4]:
"Generalize exact K-gap accounting from zero-fee batch execution to fee-aware."

## Proof architecture

1. **Pool state machine**: `FeePool` with fee-in-pool swap execution
2. **Per-step K-gap**: reuses `fee_in_pool_K_exact` from FeeAwareAntiFragmentation
3. **Batch telescoping**: list induction, each step shifts K by exactly one gap term
4. **Strict positivity**: ceiling fee ≥ 1 + output < reserve → K-gap > 0
5. **Reserve preservation**: rx and ry stay positive through any batch
6. **General strict monotonicity**: positive trade at ANY batch position → K strictly up
7. **Monoid action**: `feeBatch` is a monoid action of `(List ℕ, ++)` on `FeePool`
8. **Output conservation**: total output + final reserve = initial reserve (telescoping)
9. **Balance sheet**: rx_final × ry_final = K_init + K_gap_sum (verifiable identity)
10. **Certificate verification**: K-gap sum uniquely recoverable from boundary data
11. **Fee rate monotonicity**: higher fee rate → higher K at every single swap

## Evidence chain
- `BatchCPMMUnification.lean`: zero-fee batch K-gap sum (Lean proof)
- `FeeAwareAntiFragmentation.lean`: single-swap fee-in-pool K exact formula (Lean proof)
- This file: fee-aware batch telescoping (Lean proof, 0 sorry)
-/

namespace FeeAwareBatchKGap

open CPMMInvariants (ceilDiv computeFee netAmount)
open AntiFragmentation (swapOut kValue swapOut_le_reserve swap_euclidean
  swapOut_mono_amount)
open FeeAwareAntiFragmentation

/-! ## Part 1: Fee-Aware Pool State Machine -/

/-- A pool state for fee-in-pool execution.
    Reuses natural number reserves (matching AntiFragmentation conventions). -/
structure FeePool where
  rx : ℕ  -- input reserve
  ry : ℕ  -- output reserve
  deriving Repr, DecidableEq

/-- Product invariant K = rx * ry. -/
def FeePool.K (p : FeePool) : ℕ := kValue p.rx p.ry

/-- Fee-in-pool swap execution: the pool receives `gross` in the input reserve,
    but output is computed on `net = gross - computeFee(gross, bps)`.
    This matches Uniswap-style fee collection. -/
def feeSwap (p : FeePool) (gross fee_bps : ℕ) : FeePool :=
  let net := netAmount gross fee_bps
  let out := swapOut p.rx p.ry net
  ⟨p.rx + gross, p.ry - out⟩

/-- Sequential fee-in-pool batch execution. -/
def feeBatch (p : FeePool) (fee_bps : ℕ) : List ℕ → FeePool
  | [] => p
  | gross :: rest => feeBatch (feeSwap p gross fee_bps) fee_bps rest

/-- BATCH IDENTITY: empty batch leaves the pool unchanged.
    This is the identity law of the monoid action of `(List ℕ, ++)` on `FeePool`. -/
@[simp]
theorem feeBatch_nil (p : FeePool) (fee_bps : ℕ) :
    feeBatch p fee_bps [] = p := rfl

/-- BATCH SINGLETON: single-element batch reduces to one feeSwap. -/
@[simp]
theorem feeBatch_singleton (p : FeePool) (fee_bps : ℕ) (gross : ℕ) :
    feeBatch p fee_bps [gross] = feeSwap p gross fee_bps := rfl

/-! ## Part 2: Per-Step K-Gap -/

/-- The fee-aware K-gap for a single step: combines the zero-fee Euclidean
    remainder with the fee retention bonus.

    FeeAwareKGap(p, gross, bps) = (ry * net) % (rx + net) + fee * (ry - out)

    The first term is the familiar K-remainder from integer division.
    The second term is the ADDITIONAL K-increase from retaining fees in reserves. -/
def feeAwareKGap (p : FeePool) (gross fee_bps : ℕ) : ℕ :=
  let net := netAmount gross fee_bps
  let fee := computeFee gross fee_bps
  let out := swapOut p.rx p.ry net
  (p.ry * net) % (p.rx + net) + fee * (p.ry - out)

/-- Sum of per-step fee-aware K-gaps across a batch. -/
def feeBatchKGapSum (p : FeePool) (fee_bps : ℕ) : List ℕ → ℕ
  | [] => 0
  | gross :: rest =>
      feeAwareKGap p gross fee_bps +
        feeBatchKGapSum (feeSwap p gross fee_bps) fee_bps rest

/-- K-GAP SUM IDENTITY: empty batch has zero total K-gap. -/
@[simp]
theorem feeBatchKGapSum_nil (p : FeePool) (fee_bps : ℕ) :
    feeBatchKGapSum p fee_bps [] = 0 := rfl

/-! ## Part 3: Single-Step K-Gap Exact -/

/-- SINGLE-STEP K-GAP: the K after one fee-in-pool swap equals the initial K
    plus the fee-aware K-gap.

    Proof: unfold FeePool.K, then apply fee_in_pool_K_exact
    from FeeAwareAntiFragmentation.lean. -/
theorem feeSwap_K_gap_exact (p : FeePool) (gross fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    (feeSwap p gross fee_bps).K = p.K + feeAwareKGap p gross fee_bps := by
  simp only [FeePool.K, feeAwareKGap]
  show kValue (p.rx + gross) (p.ry - swapOut p.rx p.ry (netAmount gross fee_bps)) =
       kValue p.rx p.ry +
         ((p.ry * netAmount gross fee_bps) % (p.rx + netAmount gross fee_bps) +
          computeFee gross fee_bps * (p.ry - swapOut p.rx p.ry (netAmount gross fee_bps)))
  -- fee_in_pool_K_exact gives a + b + c; we need a + (b + c). Omega handles reassociation.
  have := fee_in_pool_K_exact p.rx p.ry gross fee_bps hbps
  omega

/-! ## Part 4: Batch K-Gap Telescoping (Main Theorem) -/

/-- **FEE-AWARE BATCH K-GAP TELESCOPING**: the final K equals the initial K
    plus the sum of per-step fee-aware K-gaps.

    K(feeBatch(p, bps, [g₁,...,gₙ])) = K(p) + Σᵢ feeAwareKGap(pᵢ, gᵢ, bps)

    This is the fee-aware generalization of `executeBatchSwaps_K_gap_sum`:
    each step contributes its own remainder + fee bonus, and the total
    K-increase is their exact sum.

    Proof: list induction. At each step, `feeSwap_K_gap_exact` gives
    K(step) = K(prev) + gap, and the inductive hypothesis gives
    K(rest) = K(step) + Σ rest_gaps. Chain with omega. -/
theorem feeBatch_K_gap_sum (p : FeePool) (amounts : List ℕ) (fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    (feeBatch p fee_bps amounts).K = p.K + feeBatchKGapSum p fee_bps amounts := by
  induction amounts generalizing p with
  | nil => simp [feeBatch, feeBatchKGapSum]
  | cons gross rest ih =>
    show (feeBatch (feeSwap p gross fee_bps) fee_bps rest).K =
         p.K + (feeAwareKGap p gross fee_bps +
                feeBatchKGapSum (feeSwap p gross fee_bps) fee_bps rest)
    rw [ih (feeSwap p gross fee_bps)]
    have := feeSwap_K_gap_exact p gross fee_bps hbps
    omega

/-! ## Part 5: Strict K-Gap Positivity

When fees are charged and trading volume is positive, the K-gap is STRICTLY
positive — the pool always benefits from fee collection. This is the formal
guarantee that fee-bearing pools never lose value from executing trades. -/

/-- The fee retention bonus component of the K-gap. -/
def feeRetentionBonus (p : FeePool) (gross fee_bps : ℕ) : ℕ :=
  computeFee gross fee_bps * (p.ry - swapOut p.rx p.ry (netAmount gross fee_bps))

/-- CEILING FEE POSITIVE: for any positive amount and positive fee rate,
    the ceiling-based fee is at least 1.
    Proof: `⌈a·bps/10000⌉ ≥ 1` when `a·bps > 0`, because `⌈n/d⌉ ≥ 1`
    when `n > 0`. -/
theorem computeFee_pos (gross fee_bps : ℕ) (hgross : 0 < gross) (hbps : 0 < fee_bps) :
    0 < computeFee gross fee_bps := by
  unfold computeFee ceilDiv
  have hprod : 0 < gross * fee_bps := Nat.mul_pos hgross hbps
  -- (gross * fee_bps + 9999) / 10000 ≥ 1 because numerator ≥ 10000
  -- actually, numerator = gross*bps + 9999 > 9999 ≥ 10000 only if gross*bps ≥ 1
  -- We need: (gross*bps + 9999) / 10000 > 0
  -- Equivalently: gross*bps + 9999 ≥ 10000
  -- Which holds when gross*bps ≥ 1 (always, since both > 0)
  omega

/-- OUTPUT STRICTLY LESS THAN RESERVE: when both reserves are positive, the
    CPMM output is strictly less than the output reserve.
    Proof: `y*a/(x+a) < y` because `y*a < y*(x+a)` when `x > 0`.
    Requires `0 < rx` and `0 < ry`. -/
theorem swapOut_lt_reserve (rx ry net : ℕ) (hrx : 0 < rx) (hry : 0 < ry) :
    swapOut rx ry net < ry := by
  simp only [swapOut]
  by_cases hnet : net = 0
  · -- net = 0 → ry * 0 / (rx + 0) = 0 < ry
    subst hnet; simp; exact hry
  · -- net > 0 → ry * net / (rx + net) < ry via ry * net < (rx + net) * ry
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm (rx + net) ry]
    exact (Nat.mul_lt_mul_left hry).mpr (by omega)

/-- FEE RETENTION BONUS POSITIVE: when fee_bps > 0, gross > 0, and reserves
    are positive, the fee bonus is strictly positive.

    This is the key lemma for strict K-gap positivity: fee collection always
    generates a positive K-bonus because (1) ceiling fee ≥ 1, and (2) the pool
    retains positive reserve after output (`ry - out > 0` when `rx > 0`). -/
theorem feeRetentionBonus_pos (p : FeePool) (gross fee_bps : ℕ)
    (hgross : 0 < gross) (hbps_pos : 0 < fee_bps)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    0 < feeRetentionBonus p gross fee_bps := by
  unfold feeRetentionBonus
  apply Nat.mul_pos
  · exact computeFee_pos gross fee_bps hgross hbps_pos
  · -- Need: swapOut rx ry net < ry, so ry - out > 0
    have hlt := swapOut_lt_reserve p.rx p.ry (netAmount gross fee_bps) hrx hry
    omega

/-- **STRICT K-GAP POSITIVITY**: when fee_bps > 0, gross > 0, and both reserves
    are positive, the fee-aware K-gap is STRICTLY positive.

    When fees and trade size are positive and reserves are positive,
    K strictly increases at each step. Combined with batch telescoping,
    this gives STRICT K-monotonicity for fee-aware batches.

    Proof: the K-gap includes `fee * (ry - out)`, which is positive because
    ceiling fees are ≥ 1 and output is strictly less than reserve. -/
theorem feeAwareKGap_strict_pos (p : FeePool) (gross fee_bps : ℕ)
    (hgross : 0 < gross) (hbps_pos : 0 < fee_bps)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    0 < feeAwareKGap p gross fee_bps := by
  simp only [feeAwareKGap]
  have hbonus := feeRetentionBonus_pos p gross fee_bps hgross hbps_pos hrx hry
  simp only [feeRetentionBonus] at hbonus
  -- goal: 0 < mod_term + fee_bonus; have: 0 < fee_bonus
  exact Nat.lt_of_lt_of_le hbonus (Nat.le_add_left _ _)

/-- STRICT BATCH K-MONOTONICITY (head-positive): fee-in-pool batch execution
    with positive fees and a positive FIRST trade strictly increases K.

    This is the base case; see `feeBatch_K_strict_mono_any` for the general
    version handling a positive trade at ANY position in the batch. -/
theorem feeBatch_K_strict_mono (p : FeePool) (gross : ℕ) (rest : List ℕ) (fee_bps : ℕ)
    (hgross : 0 < gross) (hbps_pos : 0 < fee_bps) (hbps : fee_bps ≤ 10000)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    (feeBatch p fee_bps (gross :: rest)).K > p.K := by
  have htele := feeBatch_K_gap_sum p (gross :: rest) fee_bps hbps
  have hpos := feeAwareKGap_strict_pos p gross fee_bps hgross hbps_pos hrx hry
  simp only [feeBatchKGapSum] at htele
  omega

/-! ## Part 5b: Reserve Preservation and General Strict Monotonicity

The `feeBatch_K_strict_mono` above requires the FIRST trade to be positive.
For a batch like `[0, 0, 100, 50]`, the positive trade is at index 2. To handle
this, we prove that fee-in-pool batch execution **preserves positive reserves**:
if the pool starts with rx > 0 and ry > 0, it stays that way after any number
of fee swaps. Then the general strict monotonicity theorem follows by splitting
the batch at the first positive trade via the monoid action (Part 6). -/

/-- FEE SWAP PRESERVES POSITIVE INPUT RESERVE: rx only increases (by gross). -/
theorem feeSwap_rx_pos (p : FeePool) (gross fee_bps : ℕ) (hrx : 0 < p.rx) :
    0 < (feeSwap p gross fee_bps).rx := by
  simp only [feeSwap]; omega

/-- FEE SWAP PRESERVES POSITIVE OUTPUT RESERVE: output is strictly less than
    ry (when rx > 0), so ry - out > 0.

    Key lemma: `swapOut_lt_reserve` gives `out < ry` when both reserves positive. -/
theorem feeSwap_ry_pos (p : FeePool) (gross fee_bps : ℕ)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    0 < (feeSwap p gross fee_bps).ry := by
  simp only [feeSwap]
  have hlt := swapOut_lt_reserve p.rx p.ry (netAmount gross fee_bps) hrx hry
  omega

/-- BATCH PRESERVES POSITIVE INPUT RESERVE: by induction, each feeSwap only
    increases rx (by gross). -/
theorem feeBatch_rx_pos (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (hrx : 0 < p.rx) :
    0 < (feeBatch p fee_bps amounts).rx := by
  induction amounts generalizing p with
  | nil => simpa [feeBatch]
  | cons gross rest ih =>
    simp only [feeBatch]; exact ih _ (feeSwap_rx_pos p gross fee_bps hrx)

/-- BATCH PRESERVES POSITIVE OUTPUT RESERVE: by induction, each step's output
    is strictly less than the reserve (from `swapOut_lt_reserve`), so ry stays
    positive throughout.

    This is the structural invariant that enables `feeBatch_K_strict_mono_any`:
    no matter how many zero-trades precede a positive one, the reserves are
    still positive when the positive trade executes. -/
theorem feeBatch_ry_pos (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    0 < (feeBatch p fee_bps amounts).ry := by
  induction amounts generalizing p with
  | nil => simpa [feeBatch]
  | cons gross rest ih =>
    simp only [feeBatch]
    exact ih _ (feeSwap_rx_pos p gross fee_bps hrx) (feeSwap_ry_pos p gross fee_bps hrx hry)

/-- BATCH K-MONOTONICITY (weak): fee-in-pool batch execution never decreases K.
    Immediate from telescoping: K(final) = K(init) + gap_sum, where gap_sum ≥ 0. -/
private theorem feeBatch_K_mono (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (hbps : fee_bps ≤ 10000) :
    (feeBatch p fee_bps amounts).K ≥ p.K := by
  have := feeBatch_K_gap_sum p amounts fee_bps hbps; omega

/-! ## Part 6: Compositional Batch Splitting (Monoid Action)

Batch execution forms a **monoid action** of `(List ℕ, ++)` on `FeePool`:

1. **Identity**: `feeBatch p bps [] = p` (`feeBatch_nil`)
2. **Associativity**: `feeBatch p bps (xs ++ ys) = feeBatch (feeBatch p bps xs) bps ys` (`feeBatch_append`)
3. **K-gap compatibility**: `KGapSum(xs ++ ys) = KGapSum(xs) + KGapSum(ys)` (`feeBatchKGapSum_append`)

The K-gap sum inherits this structure, splitting additively over concatenation.
This is the compositional verification principle: sub-batch K-gaps can be
computed independently and combined, enabling modular audit of settlement batches. -/

/-- BATCH COMPOSITION (Monoid Action): executing a concatenated batch equals
    sequentially executing the two halves.

    This is the associativity law for the monoid action of `(List ℕ, ++)` on FeePool.
    Combined with `feeBatch_nil` (identity), this makes `feeBatch` a proper
    monoid action — the algebraic foundation for compositional batch verification. -/
theorem feeBatch_append (p : FeePool) (fee_bps : ℕ) (xs ys : List ℕ) :
    feeBatch p fee_bps (xs ++ ys) = feeBatch (feeBatch p fee_bps xs) fee_bps ys := by
  induction xs generalizing p with
  | nil => simp [feeBatch]
  | cons x rest ih => simp only [List.cons_append, feeBatch]; exact ih _

/-- K-GAP SUM SPLITTING (Additive over Concatenation):

    feeBatchKGapSum(p, bps, xs ++ ys) =
      feeBatchKGapSum(p, bps, xs) + feeBatchKGapSum(feeBatch(p, bps, xs), bps, ys)

    The K-gap sum is additive under batch concatenation: the total K-gap over
    xs ++ ys equals the K-gap over xs plus the K-gap over ys starting from
    the pool state after xs. Combined with `feeBatch_K_gap_sum`, this gives:

      K(final) = K(init) + gap(xs) + gap(ys)

    enabling compositional K-accounting where auditors verify sub-batches
    independently and combine the results. -/
theorem feeBatchKGapSum_append (p : FeePool) (fee_bps : ℕ) (xs ys : List ℕ) :
    feeBatchKGapSum p fee_bps (xs ++ ys) =
      feeBatchKGapSum p fee_bps xs + feeBatchKGapSum (feeBatch p fee_bps xs) fee_bps ys := by
  induction xs generalizing p with
  | nil => simp [feeBatchKGapSum, feeBatch]
  | cons x rest ih =>
    simp only [List.cons_append, feeBatchKGapSum, feeBatch]
    rw [ih (feeSwap p x fee_bps)]
    omega

/-- Composition witness: splitting a 4-trade batch at position 2 gives
    the same K-gap sum as processing all 4 together. -/
theorem witness_batch_composition :
    let p : FeePool := ⟨1000, 1000⟩
    let bps := 300
    let xs := [100, 50]; let ys := [200, 75]
    -- Composition: gap(xs ++ ys) = gap(xs) + gap(ys)
    feeBatchKGapSum p bps (xs ++ ys) =
      feeBatchKGapSum p bps xs + feeBatchKGapSum (feeBatch p bps xs) bps ys ∧
    -- Monoid action: batch(xs ++ ys) = batch(batch(xs), ys)
    feeBatch p bps (xs ++ ys) = feeBatch (feeBatch p bps xs) bps ys := by
  native_decide

/-- MODULAR K-ACCOUNTING: composition of batch splitting with K-gap
    telescoping gives K of any sub-batch independently.

    K(feeBatch(p, bps, xs ++ ys)) =
      K(feeBatch(p, bps, xs)) + feeBatchKGapSum(feeBatch(p, bps, xs), bps, ys)

    This is the practical payoff: auditors can verify K-accounting for
    sub-batches independently, then combine results. No need to re-derive
    the full batch telescoping — the monoid action structure handles composition. -/
theorem feeBatch_K_split (p : FeePool) (xs ys : List ℕ) (fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    (feeBatch p fee_bps (xs ++ ys)).K =
      (feeBatch p fee_bps xs).K + feeBatchKGapSum (feeBatch p fee_bps xs) fee_bps ys := by
  rw [feeBatch_append, feeBatch_K_gap_sum _ ys fee_bps hbps]

/-! ## Part 6b: Structural Accounting Identities

Batch execution satisfies structural accounting identities that hold
REGARDLESS of fee rate or pool state. These are the auditable invariants:
rx tracks total gross input, and K-gap decomposes into fee-independent
and fee-dependent components. -/

/-- FEE BATCH RX FORMULA: final input reserve = initial + sum of all gross amounts.
    The pool absorbs the full gross at each step regardless of fee rate.

    This is a KEY accounting identity for on-chain audit: the rx change
    verifies total volume without needing to know the fee schedule.
    In particular, changing the fee rate does NOT affect rx evolution.

    Proof: at each step, `feeSwap` adds `gross` to rx (by definition). -/
theorem feeBatch_rx_formula (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ) :
    (feeBatch p fee_bps amounts).rx = p.rx + amounts.sum := by
  induction amounts generalizing p with
  | nil => simp [feeBatch]
  | cons g rest ih =>
    simp only [feeBatch, List.sum_cons]
    rw [ih]; simp [feeSwap]; omega

/-- Sum of fee retention bonuses across a batch (fee-only K component). -/
def feeBatchRetentionSum (p : FeePool) (fee_bps : ℕ) : List ℕ → ℕ
  | [] => 0
  | gross :: rest =>
      feeRetentionBonus p gross fee_bps +
        feeBatchRetentionSum (feeSwap p gross fee_bps) fee_bps rest

/-- K-GAP ≥ FEE RETENTION: the total batch K-increase is at least the sum
    of fee retention bonuses.

    This gives a COMPUTABLE lower bound on K-increase that requires only
    fee amounts and output reserves (no modular arithmetic needed):

      Σᵢ feeAwareKGap(pᵢ, gᵢ, bps) ≥ Σᵢ fee(gᵢ) * (ryᵢ - outᵢ)

    For pool operators: even ignoring the "rounding bonus" from integer
    division, the pool earns at least the fee retention from every trade.

    Proof: at each step, `feeAwareKGap = mod_remainder + fee_bonus ≥ fee_bonus`
    because the modular remainder is non-negative. By induction, batch sums
    inherit this. -/
theorem feeBatchKGapSum_ge_retention (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ) :
    feeBatchKGapSum p fee_bps amounts ≥ feeBatchRetentionSum p fee_bps amounts := by
  induction amounts generalizing p with
  | nil => simp [feeBatchKGapSum, feeBatchRetentionSum]
  | cons g rest ih =>
    simp only [feeBatchKGapSum, feeBatchRetentionSum, feeAwareKGap, feeRetentionBonus]
    have hrec := ih (feeSwap p g fee_bps)
    omega

/-- K-gap fee retention lower bound witness. -/
theorem witness_retention_lower_bound :
    let p : FeePool := ⟨1000, 1000⟩
    let bps := 500
    let amounts := [100, 200, 50]
    -- K-gap sum strictly exceeds retention sum (mod remainders > 0)
    feeBatchKGapSum p bps amounts > feeBatchRetentionSum p bps amounts ∧
    -- Both are positive
    0 < feeBatchRetentionSum p bps amounts ∧
    0 < feeBatchKGapSum p bps amounts := by
  native_decide

/-! ## Part 7: General Strict Batch Monotonicity

Combining reserve preservation (Part 5b) with compositional splitting (Part 6)
gives the GENERAL strict monotonicity theorem: any positive trade ANYWHERE in
the batch forces K to strictly increase. The proof decomposes the batch at the
positive trade's position, applies weak monotonicity through the zero-trade
prefix, then strict monotonicity from the positive trade onward. -/

/-- **STRICT BATCH K-MONOTONICITY (general)**: if ANY trade in the batch is
    positive (not just the first) and fee_bps > 0 with positive reserves,
    K strictly increases.

    This is strictly stronger than `feeBatch_K_strict_mono`. The proof splits
    the batch as `pre ++ [g] ++ suf` at the positive trade `g`, then:
    1. `feeBatch_K_mono`: K ≥ K₀ after the prefix (weak monotonicity)
    2. `feeBatch_rx_pos`/`feeBatch_ry_pos`: reserves still positive at `g`
    3. `feeBatch_K_strict_mono`: K strictly increases from `g` onward

    The compositional structure from the monoid action (Part 6) is essential:
    it lets us reason about sub-batches independently. -/
theorem feeBatch_K_strict_mono_any (p : FeePool) (fee_bps : ℕ)
    (pre : List ℕ) (g : ℕ) (suf : List ℕ)
    (hg : 0 < g) (hbps_pos : 0 < fee_bps) (hbps : fee_bps ≤ 10000)
    (hrx : 0 < p.rx) (hry : 0 < p.ry) :
    (feeBatch p fee_bps (pre ++ g :: suf)).K > p.K := by
  -- Split the batch via the monoid action
  rw [feeBatch_append]
  -- Reserves preserved through the prefix
  have hrx' := feeBatch_rx_pos p fee_bps pre hrx
  have hry' := feeBatch_ry_pos p fee_bps pre hrx hry
  -- Strict increase from g onward
  have hstrict := feeBatch_K_strict_mono (feeBatch p fee_bps pre)
    g suf fee_bps hg hbps_pos hbps hrx' hry'
  -- Weak monotonicity through the prefix
  have hmono := feeBatch_K_mono p fee_bps pre hbps
  omega

/-- General strict monotonicity witness: positive trade at index 2 (not first). -/
theorem witness_general_strict_mono :
    let p : FeePool := ⟨1000, 1000⟩
    let bps := 300
    -- [0, 0, 100] has positive trade at index 2
    (feeBatch p bps [0, 0, 100]).K > p.K ∧
    -- K values: pool always benefits even after zero-trades
    p.K = 1000000 ∧
    (feeBatch p bps [0, 0, 100]).K > 1000000 := by
  native_decide

/-! ## Part 8: Batch Output Accounting and Balance Sheet

The OUTPUT-SIDE dual of Part 6b's input accounting. Where `feeBatch_rx_formula`
tracks total gross inputs, this section tracks total outputs extracted. Together
with the K-gap telescoping formula, they give a COMPLETE BALANCE SHEET:

  rx_final × ry_final = K_init + K_gap_sum

This is the fee-aware generalization of K = rx × ry, accounting for fee-induced
K accumulation across a batch. An auditor can verify this identity from on-chain
data without replaying the execution — the three sides are independently computable. -/

/-- Total output extracted from a fee-in-pool batch. -/
def batchOutputSum (p : FeePool) (fee_bps : ℕ) : List ℕ → ℕ
  | [] => 0
  | gross :: rest =>
      swapOut p.rx p.ry (netAmount gross fee_bps) +
        batchOutputSum (feeSwap p gross fee_bps) fee_bps rest

/-- BATCH OUTPUT CONSERVATION: total output plus final reserve equals initial reserve.

    Σᵢ outᵢ + ry_final = ry_init

    This is the output-side accounting identity — every Y token that leaves
    the pool is accounted for in the output sum. The identity holds WITHOUT
    any fee rate constraint: it's a pure accounting tautology.

    Combined with `feeBatch_rx_formula` (input side): the pool's token balance
    sheet is always in balance. No tokens are created or destroyed.

    Proof: telescoping. At each step, outᵢ + ryᵢ₊₁ = ryᵢ because
    swapOut ≤ reserve (from `swapOut_le_reserve`). -/
theorem feeBatch_output_conservation (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ) :
    batchOutputSum p fee_bps amounts + (feeBatch p fee_bps amounts).ry = p.ry := by
  induction amounts generalizing p with
  | nil => simp [batchOutputSum, feeBatch]
  | cons g rest ih =>
    simp only [batchOutputSum, feeBatch]
    have hrec := ih (feeSwap p g fee_bps)
    have hle := swapOut_le_reserve p.rx p.ry (netAmount g fee_bps)
    have hry_eq : (feeSwap p g fee_bps).ry =
        p.ry - swapOut p.rx p.ry (netAmount g fee_bps) := rfl
    rw [hry_eq] at hrec; omega

/-- COMPLETE BALANCE SHEET: the K-gap sum is verifiable from on-chain data.

    (rx_init + Σ grossᵢ) × ry_final = rx_init × ry_init + Σ K-gapᵢ

    This connects three independently auditable quantities:
    1. Input reserve change: Σ grossᵢ (from transaction logs)
    2. Final output reserve: ry_final (from pool state query)
    3. K-gap certificate: Σ K-gapᵢ (from the telescoping formula)

    An auditor can verify: compute LHS from (1)+(2), compute RHS from
    initial state + (3), check equality. Any discrepancy proves tampering.

    Proof: unfold K = rx × ry in the telescoping theorem, then substitute
    the rx formula. The monoid action structure ensures the substitution
    is valid across the entire batch. -/
theorem feeBatch_balance_sheet (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (hbps : fee_bps ≤ 10000) :
    (p.rx + amounts.sum) * (feeBatch p fee_bps amounts).ry =
      p.rx * p.ry + feeBatchKGapSum p fee_bps amounts := by
  have hrx := feeBatch_rx_formula p fee_bps amounts
  have hk := feeBatch_K_gap_sum p amounts fee_bps hbps
  simp only [FeePool.K, kValue] at hk
  rw [← hrx]; exact hk

/-- BATCH K-GAP CERTIFICATE VERIFICATION: to verify a claimed K-gap sum `c`,
    check ONLY the balance sheet identity — no need to replay the batch.

    Correctness: if the identity holds, c equals the true K-gap sum.
    Soundness: no false c can pass (the identity uniquely determines c).

    This is the CERTIFICATE theorem: an auditor needs only the initial pool,
    the list of gross amounts, and the final ry to recover the exact K-gap sum.
    The fee schedule, per-step outputs, and intermediate states are all implicit. -/
theorem feeBatch_K_certificate_unique (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (hbps : fee_bps ≤ 10000) (c : ℕ)
    (hcert : (p.rx + amounts.sum) * (feeBatch p fee_bps amounts).ry = p.rx * p.ry + c) :
    c = feeBatchKGapSum p fee_bps amounts := by
  have hbs := feeBatch_balance_sheet p fee_bps amounts hbps
  omega

/-- BATCH OUTPUT CERTIFICATE: the total output is uniquely determined by
    initial and final ry, without replaying the batch.

    batchOutputSum = ry_init - ry_final

    This completes the audit toolkit: K-gap from balance sheet (Part 8),
    total output from ry conservation (Part 8), both verifiable from
    boundary data only. -/
theorem feeBatch_output_certificate_unique (p : FeePool) (fee_bps : ℕ) (amounts : List ℕ)
    (c : ℕ) (hcert : c + (feeBatch p fee_bps amounts).ry = p.ry) :
    c = batchOutputSum p fee_bps amounts := by
  have hoc := feeBatch_output_conservation p fee_bps amounts
  omega

/-! ## Part 8c: K-Gap Monotonicity in Fee Rate

Higher fee rate → higher K: the pool benefits MORE from higher fees at every trade.
This is the formal proof that fee collection is a monotone function of the fee schedule.

Proof architecture:
1. `computeFee` is monotone in `bps` (ceiling of bigger product)
2. `netAmount` is anti-monotone in `bps` (more fee → less net)
3. `swapOut` output DECREASES with less net input
4. Therefore `ry - out` INCREASES → K = (rx+gross) × (ry-out) INCREASES

The economic insight: higher fees reduce trader output but never reduce pool K.
The rx component (rx + gross) is fee-rate-independent — only the ry component
responds to fee changes, and it responds MONOTONICALLY. -/

/-- Fee is monotone in rate: higher bps → higher fee (for fixed amount).
    Proof: `a * bps₁ ≤ a * bps₂` + `ceilDiv_mono`. -/
private theorem fee_mono_bps (a : ℕ) {bps₁ bps₂ : ℕ} (h : bps₁ ≤ bps₂) :
    computeFee a bps₁ ≤ computeFee a bps₂ := by
  unfold computeFee ceilDiv
  apply Nat.div_le_div_right
  have : a * bps₁ ≤ a * bps₂ := Nat.mul_le_mul_left a h
  omega

/-- Net amount is anti-monotone in fee rate: higher bps → less net.
    Proof: higher fee deducted from same gross. -/
private theorem netAmount_anti_bps (a : ℕ) {bps₁ bps₂ : ℕ}
    (h : bps₁ ≤ bps₂) (hbps : bps₂ ≤ 10000) :
    netAmount a bps₂ ≤ netAmount a bps₁ := by
  unfold netAmount
  have := fee_mono_bps a h
  have := fee_le_amount a bps₁ (le_trans h hbps)
  have := fee_le_amount a bps₂ hbps
  omega

/-- POOL K MONOTONE IN FEE RATE: for any trade, higher fee rate produces
    higher K. The pool always benefits from higher fee collection.

    This is economically fundamental: rx + gross is fee-rate-independent
    (the pool receives the full gross regardless), while ry - out INCREASES
    with fee rate (less output extracted). Their product K therefore increases.

    Proof chain: bps₁ ≤ bps₂ → net₁ ≥ net₂ → out₁ ≥ out₂ → (ry−out₁) ≤ (ry−out₂)
    → (rx+gross)×(ry−out₁) ≤ (rx+gross)×(ry−out₂). -/
theorem feeSwap_K_mono_bps (p : FeePool) (gross : ℕ) {bps₁ bps₂ : ℕ}
    (h : bps₁ ≤ bps₂) (hbps : bps₂ ≤ 10000) :
    (feeSwap p gross bps₁).K ≤ (feeSwap p gross bps₂).K := by
  simp only [FeePool.K, feeSwap, kValue]
  apply Nat.mul_le_mul_left
  have hnet := netAmount_anti_bps gross h hbps
  have hmono := swapOut_mono_amount p.rx p.ry _ _ hnet
  have hle := swapOut_le_reserve p.rx p.ry (netAmount gross bps₁)
  omega

/-- Fee rate monotonicity witness: 0% < 3% < 5% < 100% all give increasing K. -/
theorem witness_K_mono_bps :
    let p : FeePool := ⟨1000, 1000⟩
    let gross := 100
    -- K increases with fee rate: 0bps < 300bps < 500bps < 10000bps
    (feeSwap p gross 0).K < (feeSwap p gross 300).K ∧
    (feeSwap p gross 300).K < (feeSwap p gross 500).K ∧
    (feeSwap p gross 500).K < (feeSwap p gross 10000).K ∧
    -- At 100% fee: no output extracted, K = (rx+gross)*ry
    (feeSwap p gross 10000).K = (p.rx + gross) * p.ry := by
  native_decide

/-- BATCH ORDER DEPENDENCE: permuting the same trades produces different K-gap
    accumulation. This is a BATCH-LEVEL phenomenon — single-step K-gap analysis
    cannot predict it. Over ℚ, same-direction swaps would commute (ry_final
    depends only on total gross). Over ℤ, floor division creates order-dependent
    rounding. Small pools amplify this effect.

    Mechanism: floor division `⌊y·a/(x+a)⌋` is NOT a homomorphism, so
    applying it in different orders produces different remainders. -/
theorem witness_batch_order_dependence :
    let p : FeePool := ⟨7, 10⟩
    let bps := 300
    -- Same trades, different order → different final pool states
    feeBatch p bps [3, 4] ≠ feeBatch p bps [4, 3] ∧
    -- Both batches have the same total volume
    [3, 4].sum = [4, 3].sum ∧
    -- Different final K values (98 vs 84)
    (feeBatch p bps [3, 4]).K ≠ (feeBatch p bps [4, 3]).K ∧
    -- Smaller-first yields higher K (preserves more ry)
    (feeBatch p bps [3, 4]).K > (feeBatch p bps [4, 3]).K := by
  native_decide

/-- Balance sheet witness: all three accounting identities hold simultaneously. -/
theorem witness_balance_sheet :
    let p : FeePool := ⟨1000, 1000⟩
    let bps := 300
    let amounts := [100, 200, 50]
    -- Input accounting: rx tracks gross volume
    (feeBatch p bps amounts).rx = p.rx + amounts.sum ∧
    -- Output accounting: outputs + final_ry = initial_ry
    batchOutputSum p bps amounts + (feeBatch p bps amounts).ry = p.ry ∧
    -- Balance sheet: rx_final * ry_final = K_init + K_gap_sum
    (p.rx + amounts.sum) * (feeBatch p bps amounts).ry =
      p.rx * p.ry + feeBatchKGapSum p bps amounts ∧
    -- Concrete values for auditing
    (feeBatch p bps amounts).rx = 1350 ∧
    (feeBatch p bps amounts).ry = 749 ∧
    batchOutputSum p bps amounts = 251 := by
  native_decide

/-! ## Part 9: Non-Vacuity Witnesses -/

/-- Single-step K-gap witness: pool (1000,1000), gross=100, 500bps fee.
    Verifies exact K-gap formula, fee retention bonus positivity, and strict K-increase. -/
theorem witness_single_step :
    let p : FeePool := ⟨1000, 1000⟩
    let gross := 100; let bps := 500
    -- K-gap exact
    (feeSwap p gross bps).K = p.K + feeAwareKGap p gross bps ∧
    -- Fee retention bonus is positive
    0 < feeRetentionBonus p gross bps ∧
    -- K-gap is strictly positive
    0 < feeAwareKGap p gross bps ∧
    -- K strictly increases
    (feeSwap p gross bps).K > p.K ∧
    -- Concrete values: gap = remainder(830) + bonus(4570)
    feeAwareKGap p gross bps = 5400 ∧
    feeRetentionBonus p gross bps = 4570 := by
  native_decide

/-- Batch K-gap telescoping witness: 3-swap batch on pool (1000,1000), 300bps.
    Verifies K(final) = K(init) + Σ gaps and K strictly increases. -/
theorem witness_batch_telescoping :
    let p : FeePool := ⟨1000, 1000⟩
    let bps := 300
    let amounts := [100, 50, 200]
    -- Telescoping: K(final) = K(init) + sum of gaps
    (feeBatch p bps amounts).K = p.K + feeBatchKGapSum p bps amounts ∧
    -- K strictly increases (gap sum > 0)
    feeBatchKGapSum p bps amounts > 0 ∧
    -- K monotone
    (feeBatch p bps amounts).K > p.K := by
  native_decide

/-- Fee vs zero-fee comparison witness: fee K > zero-fee K for same gross input.
    Pool (1000,1000), gross=100, 500bps fee. -/
theorem witness_fee_vs_nofee :
    let p : FeePool := ⟨1000, 1000⟩
    let gross := 100; let bps := 500
    -- Fee-in-pool K strictly exceeds zero-fee K
    (feeSwap p gross bps).K >
      kValue (p.rx + gross) (p.ry - swapOut p.rx p.ry gross) ∧
    -- The gap is the fee retention bonus
    (feeSwap p gross bps).K -
      kValue (p.rx + gross) (p.ry - swapOut p.rx p.ry gross) > 0 := by
  native_decide

/-- Edge case witness: zero-fee scenario (bps=0) collapses to zero-fee model.
    When fee_bps=0, the fee retention bonus vanishes and only the
    Euclidean remainder contributes to K-gap. -/
theorem witness_zero_fee_collapse :
    let p : FeePool := ⟨1000, 1000⟩
    let gross := 100; let bps := 0
    -- Fee bonus is zero
    feeRetentionBonus p gross bps = 0 ∧
    -- Matches zero-fee model exactly (no fee retained)
    (feeSwap p gross bps).K =
      kValue (p.rx + gross) (p.ry - swapOut p.rx p.ry gross) ∧
    -- K-gap is the pure Euclidean remainder (no fee bonus)
    feeAwareKGap p gross bps = (p.ry * gross) % (p.rx + gross) := by
  native_decide

end FeeAwareBatchKGap
