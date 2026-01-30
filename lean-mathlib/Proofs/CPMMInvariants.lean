import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# CPMM Security Invariants

This file proves critical security properties for Constant Product Market Maker (CPMM):

1. **K-Monotonicity**: The product invariant k = x * y never decreases after swaps
2. **LP Round-Trip Conservation**: Deposit → withdraw never profits the LP
3. **Swap Output Bound**: You can't extract more than the reserve

## Non-Vacuity Strategy

For each theorem, we provide:
- Explicit witnesses satisfying the hypotheses
- Computational verification that the hypotheses are satisfiable
- Consequential lemmas showing the theorem implies non-trivial facts

## Methodology

Using Numina-style agentic proving:
1. State goal with explicit hypotheses
2. Use LSP to examine proof state
3. Search for tactics via multi_attempt
4. Verify non-vacuity via witness construction
-/

namespace CPMMInvariants

/-! ## Basic Definitions -/

/-- Ceiling division: ⌈a/b⌉ = (a + b - 1) / b for b > 0 -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Fee computation: fee = ⌈amount × fee_bps / 10000⌉ -/
def computeFee (amount fee_bps : ℕ) : ℕ := ceilDiv (amount * fee_bps) 10000

/-- Net amount after fee deduction -/
def netAmount (gross fee_bps : ℕ) : ℕ := gross - computeFee gross fee_bps

/-- CPMM swap output: floor(reserve_out × net_in / (reserve_in + net_in)) -/
def swapOutput (reserve_in reserve_out net_in : ℕ) : ℕ :=
  (reserve_out * net_in) / (reserve_in + net_in)

/-- K-value (product invariant) -/
def kValue (x y : ℕ) : ℕ := x * y

/-! ## Theorem 1: Swap Output is Bounded by Reserve

This is a fundamental safety property: you can never extract more than exists.
-/

/-- The output of a swap is strictly less than the output reserve -/
theorem swap_output_lt_reserve {rin rout net : ℕ}
    (hrin : 0 < rin) (_hrout : 0 < rout) (_hnet : 0 < net) :
    swapOutput rin rout net < rout := by
  simp [swapOutput]; apply Nat.div_lt_of_lt_mul; ring_nf; nlinarith

/-- Non-vacuity witness: typical swap parameters satisfy hypotheses -/
example : 0 < (1000 : ℕ) ∧ 0 < (2000 : ℕ) ∧ 0 < (100 : ℕ) := by
  decide

/-! ## Theorem 2: K-Monotonicity for Zero-Fee Swaps

For zero-fee swaps, K is nondecreasing: `K(new) ≥ K(old)`.
In exact arithmetic (no floor division), K would be exactly preserved.
Integer division can only increase K beyond the exact value.
With fees, K increases further since fees are retained in the pool.
-/

/-- Zero-fee swap output: the simple CPMM formula -/
def swapOutputZeroFee (reserve_in reserve_out amount_in : ℕ) : ℕ :=
  (reserve_out * amount_in) / (reserve_in + amount_in)

/-- Key lemma: floor division property -/
lemma div_mul_le (a b : ℕ) : (a / b) * b ≤ a := Nat.div_mul_le_self a b

/-- For zero-fee swaps, K never decreases -/
theorem k_monotone_zero_fee
    {rin rout amount_in : ℕ}
    (hrin : 0 < rin)
    (_hrout : 0 < rout)
    (hamount : 0 < amount_in) :
    let amount_out := swapOutputZeroFee rin rout amount_in
    let new_rin := rin + amount_in
    let new_rout := rout - amount_out
    kValue new_rin new_rout ≥ kValue rin rout := by
  simp only [kValue, swapOutputZeroFee]
  -- Key: (rin + amount_in) * (rout - (rout * amount_in) / (rin + amount_in)) ≥ rin * rout
  -- Using the property that a/b * b ≤ a, so rout - out ≥ rout - (rout * amount_in)/(rin + amount_in)
  -- expanded: rout*rin / (rin + amount_in) ≤ rout - out
  set d := rin + amount_in with hd
  set out := (rout * amount_in) / d with hout
  have hd_pos : 0 < d := by omega
  -- Key inequality: d * (rout - out) ≥ rin * rout
  -- Equivalently: d * rout - d * out ≥ rin * rout
  -- Since d * out ≤ rout * amount_in (floor division property)
  -- d * rout - rout * amount_in = (rin + amount_in) * rout - rout * amount_in = rin * rout
  have hdiv : out * d ≤ rout * amount_in := Nat.div_mul_le_self (rout * amount_in) d
  have hdiv' : d * out ≤ rout * amount_in := by rw [Nat.mul_comm]; exact hdiv
  -- out ≤ rout because out = (rout * amount_in) / d ≤ rout * amount_in / amount_in = rout
  have hout_le_rout : out ≤ rout := by
    apply Nat.div_le_of_le_mul
    calc rout * amount_in ≤ rout * (rin + amount_in) := by
           apply Nat.mul_le_mul_left; omega
       _ = rout * d := by rw [hd]
       _ = d * rout := by ring
  -- Main calculation: d * (rout - out) ≥ rin * rout
  -- = d * rout - d * out ≥ rin * rout
  -- Since d * out ≤ rout * amount_in and d = rin + amount_in:
  -- d * rout - rout * amount_in = rin * rout + amount_in * rout - rout * amount_in = rin * rout
  -- So d * rout - d * out ≥ d * rout - rout * amount_in = rin * rout
  have hkey : d * rout - d * out ≥ rin * rout := by
    have h1 : d * rout - d * out ≥ d * rout - rout * amount_in := Nat.sub_le_sub_left hdiv' (d * rout)
    have h2 : d * rout - rout * amount_in = rin * rout := by
      simp only [hd]
      -- (rin + amount_in) * rout - rout * amount_in
      -- = rin * rout + amount_in * rout - rout * amount_in
      -- = rin * rout (since amount_in * rout = rout * amount_in)
      have heq : (rin + amount_in) * rout = rin * rout + amount_in * rout := by ring
      have heq2 : amount_in * rout = rout * amount_in := by ring
      rw [heq, heq2, Nat.add_sub_cancel]
    calc d * rout - d * out ≥ d * rout - rout * amount_in := h1
      _ = rin * rout := h2
  -- Convert to the form we need using Nat.mul_sub
  have hkey' : d * (rout - out) ≥ rin * rout := by
    have hsub : d * (rout - out) = d * rout - d * out := Nat.mul_sub d rout out
    omega
  exact hkey'

/-- Non-vacuity: witness satisfying all hypotheses -/
example : (0 < (1000 : ℕ)) ∧ (0 < (1000 : ℕ)) ∧ (0 < (100 : ℕ)) := by
  decide

/-- Computational verification: concrete K values -/
example : let rin := 1000; let rout := 1000; let amount_in := 100
          let amount_out := swapOutputZeroFee rin rout amount_in
          kValue (rin + amount_in) (rout - amount_out) ≥ kValue rin rout := by
  native_decide

/-! ## Theorem 3: LP Round-Trip Never Profits

If you deposit liquidity and immediately withdraw the same LP tokens,
you get back at most what you deposited (minus rounding).
-/

/-- LP tokens minted for first deposit -/
def lpMintFirst (amount0 amount1 min_lock : ℕ) : ℕ :=
  Nat.sqrt (amount0 * amount1) - min_lock

/-- LP tokens minted for subsequent deposit -/
def lpMintSubsequent (amount0 amount1 reserve0 reserve1 lp_supply : ℕ) : ℕ :=
  min ((amount0 * lp_supply) / reserve0) ((amount1 * lp_supply) / reserve1)

/-- Assets returned when burning LP tokens -/
def lpBurn (lp_amount reserve0 reserve1 lp_supply : ℕ) : ℕ × ℕ :=
  ((lp_amount * reserve0) / lp_supply, (lp_amount * reserve1) / lp_supply)

/-- Helper: LP mint for asset 0 is bounded -/
lemma lp_mint_le_amount0_ratio {amount0 reserve0 lp_supply : ℕ} (_hr0 : 0 < reserve0) :
    (amount0 * lp_supply) / reserve0 * reserve0 ≤ amount0 * lp_supply :=
  Nat.div_mul_le_self (amount0 * lp_supply) reserve0

/-- Round-trip LP provision never increases your assets -/
theorem lp_roundtrip_no_profit
    {amount0 amount1 reserve0 reserve1 lp_supply : ℕ}
    (_hr0 : 0 < reserve0) (_hr1 : 0 < reserve1) (hlp : 0 < lp_supply)
    (_ha0 : 0 < amount0) (_ha1 : 0 < amount1) :
    let lp_minted := lpMintSubsequent amount0 amount1 reserve0 reserve1 lp_supply
    let new_reserve0 := reserve0 + amount0
    let new_reserve1 := reserve1 + amount1
    let new_lp_supply := lp_supply + lp_minted
    let (return0, return1) := lpBurn lp_minted new_reserve0 new_reserve1 new_lp_supply
    return0 ≤ amount0 ∧ return1 ≤ amount1 := by
  simp only [lpMintSubsequent, lpBurn]
  set lp0 := (amount0 * lp_supply) / reserve0 with hlp0
  set lp1 := (amount1 * lp_supply) / reserve1 with hlp1
  set lp_minted := min lp0 lp1 with hlpm
  set new_r0 := reserve0 + amount0
  set new_r1 := reserve1 + amount1
  set new_lps := lp_supply + lp_minted
  constructor
  · -- return0 ≤ amount0
    -- return0 = lp_minted * new_r0 / new_lps
    -- lp_minted ≤ lp0 = (amount0 * lp_supply) / reserve0
    -- So lp_minted * reserve0 ≤ amount0 * lp_supply (floor property)
    have hlpm_le_lp0 : lp_minted ≤ lp0 := min_le_left lp0 lp1
    have hlpm_le_lp1 : lp_minted ≤ lp1 := min_le_right lp0 lp1
    -- Key: lp_minted * new_r0 / new_lps ≤ amount0
    -- Equivalent to: lp_minted * new_r0 ≤ amount0 * new_lps (when new_lps > 0)
    have hnew_lps_pos : 0 < new_lps := Nat.add_pos_left hlp lp_minted
    apply Nat.div_le_of_le_mul
    -- Need: lp_minted * (reserve0 + amount0) ≤ amount0 * (lp_supply + lp_minted)
    -- = lp_minted * reserve0 + lp_minted * amount0 ≤ amount0 * lp_supply + amount0 * lp_minted
    -- = lp_minted * reserve0 ≤ amount0 * lp_supply
    -- Since lp_minted ≤ (amount0 * lp_supply) / reserve0, we have lp_minted * reserve0 ≤ amount0 * lp_supply
    have hkey : lp_minted * reserve0 ≤ amount0 * lp_supply := by
      calc lp_minted * reserve0 ≤ lp0 * reserve0 := Nat.mul_le_mul_right reserve0 hlpm_le_lp0
        _ ≤ amount0 * lp_supply := Nat.div_mul_le_self (amount0 * lp_supply) reserve0
    calc lp_minted * new_r0
        = lp_minted * reserve0 + lp_minted * amount0 := by ring
      _ ≤ amount0 * lp_supply + lp_minted * amount0 := Nat.add_le_add_right hkey _
      _ = amount0 * lp_supply + amount0 * lp_minted := by ring
      _ = amount0 * (lp_supply + lp_minted) := by ring
      _ = amount0 * new_lps := by rfl
      _ = new_lps * amount0 := by ring
  · -- return1 ≤ amount1 (symmetric argument)
    have hlpm_le_lp1 : lp_minted ≤ lp1 := min_le_right lp0 lp1
    have hnew_lps_pos : 0 < new_lps := Nat.add_pos_left hlp lp_minted
    apply Nat.div_le_of_le_mul
    have hkey : lp_minted * reserve1 ≤ amount1 * lp_supply := by
      calc lp_minted * reserve1 ≤ lp1 * reserve1 := Nat.mul_le_mul_right reserve1 hlpm_le_lp1
        _ ≤ amount1 * lp_supply := Nat.div_mul_le_self (amount1 * lp_supply) reserve1
    calc lp_minted * new_r1
        = lp_minted * reserve1 + lp_minted * amount1 := by ring
      _ ≤ amount1 * lp_supply + lp_minted * amount1 := Nat.add_le_add_right hkey _
      _ = amount1 * lp_supply + amount1 * lp_minted := by ring
      _ = amount1 * (lp_supply + lp_minted) := by ring
      _ = amount1 * new_lps := by rfl
      _ = new_lps * amount1 := by ring

/-- Non-vacuity witness for LP round-trip theorem -/
theorem witness_lp_roundtrip :
    let amount0 := 100
    let amount1 := 200
    let reserve0 := 1000
    let reserve1 := 2000
    let lp_supply := 500
    let lp_minted := lpMintSubsequent amount0 amount1 reserve0 reserve1 lp_supply
    let new_reserve0 := reserve0 + amount0
    let new_reserve1 := reserve1 + amount1
    let new_lp_supply := lp_supply + lp_minted
    let (return0, return1) := lpBurn lp_minted new_reserve0 new_reserve1 new_lp_supply
    0 < reserve0 ∧ 0 < reserve1 ∧ 0 < lp_supply ∧ 0 < amount0 ∧ 0 < amount1 ∧
    return0 ≤ amount0 ∧ return1 ≤ amount1 := by
  native_decide

/-! ## Theorem 4: K-Monotonicity WITH Fees

With fees, K never decreases (≥) because fees are retained in the pool.
Strict increase (>) would require additional conditions on net > 0 and output > 0.
-/

/-- Fee is always less than or equal to the gross amount when fee_bps ≤ 10000 -/
lemma fee_le_gross (gross fee_bps : ℕ) (hfee : fee_bps ≤ 10000) :
    computeFee gross fee_bps ≤ gross := by
  simp only [computeFee, ceilDiv]
  -- Show: (gross * fee_bps + 9999) / 10000 ≤ gross
  have h1 : gross * fee_bps + (10000 - 1) ≤ gross * 10000 + (10000 - 1) := by
    have hmul : gross * fee_bps ≤ gross * 10000 := Nat.mul_le_mul_left gross hfee
    omega
  have h2 : (gross * fee_bps + (10000 - 1)) / 10000 ≤ (gross * 10000 + (10000 - 1)) / 10000 :=
    Nat.div_le_div_right h1
  have h3 : (gross * 10000 + (10000 - 1)) / 10000 = gross := by
    rw [Nat.mul_comm]
    have := Nat.mul_add_div (by omega : 10000 > 0) gross (10000 - 1)
    simp only [this, Nat.div_eq_of_lt (by omega : 10000 - 1 < 10000), Nat.add_zero]
  omega

/-- Net amount is non-negative (always true for Nat) -/
lemma net_nonneg (gross fee_bps : ℕ) : 0 ≤ netAmount gross fee_bps := Nat.zero_le _

/-- For typical fee ranges, net is positive -/
lemma net_positive_concrete : 0 < netAmount 100 30 := by native_decide

/-- K increases with fees: the fee retained in pool increases K.
    This is proven via the zero-fee case since fees only make K larger. -/
theorem k_monotone_with_fee
    {rin rout amount_in fee_bps : ℕ}
    (_hrin : 0 < rin)
    (_hrout : 0 < rout)
    (_hamount : 0 < amount_in)
    (_hfee_pos : 0 < fee_bps)
    (hfee_bound : fee_bps ≤ 10000) :
    let net := netAmount amount_in fee_bps
    let amount_out := swapOutput rin rout net
    let new_rin := rin + amount_in  -- Full amount_in goes to reserve (fee retained)
    let new_rout := rout - amount_out
    kValue new_rin new_rout ≥ kValue rin rout := by
  simp only [kValue, swapOutput, netAmount]
  set fee := computeFee amount_in fee_bps with hfee_def
  set net := amount_in - fee with hnet_def
  set d := rin + net with hd
  set out := (rout * net) / d with hout_def
  -- Key insight: new_rin = rin + amount_in ≥ rin + net = d (since fee ≥ 0)
  -- And the swap uses net (smaller), so output is smaller
  have hfee_le : fee ≤ amount_in := fee_le_gross amount_in fee_bps hfee_bound
  have hnet_le : net ≤ amount_in := Nat.sub_le amount_in fee
  have hd_le : d ≤ rin + amount_in := by omega
  -- out ≤ rout
  have hout_le : out ≤ rout := by
    apply Nat.div_le_of_le_mul
    calc rout * net ≤ rout * (rin + net) := Nat.mul_le_mul_left rout (Nat.le_add_left net rin)
      _ = rout * d := by rfl
      _ = d * rout := by ring
  -- Floor division property
  have hdiv' : d * out ≤ rout * net := by
    have : out * d ≤ rout * net := Nat.div_mul_le_self (rout * net) d
    rw [Nat.mul_comm]; exact this
  -- d * rout - d * out ≥ rin * rout
  have hkey : d * rout - d * out ≥ rin * rout := by
    have h1 : d * rout - d * out ≥ d * rout - rout * net := Nat.sub_le_sub_left hdiv' (d * rout)
    have h2 : d * rout - rout * net = rin * rout := by
      simp only [hd]
      have heq : (rin + net) * rout = rin * rout + net * rout := by ring
      have heq2 : net * rout = rout * net := by ring
      rw [heq, heq2, Nat.add_sub_cancel]
    omega
  -- Lift to (rin + amount_in) * (rout - out) ≥ d * (rout - out) ≥ rin * rout
  have hsub_eq : d * (rout - out) = d * rout - d * out := Nat.mul_sub d rout out
  have hd_bound : d * (rout - out) ≥ rin * rout := by omega
  have hfinal : (rin + amount_in) * (rout - out) ≥ d * (rout - out) := by
    apply Nat.mul_le_mul_right; omega
  omega

/-- Non-vacuity witness for K-monotonicity with fees -/
theorem witness_k_monotone_with_fee :
    let rin := 1000
    let rout := 1000
    let amount_in := 100
    let fee_bps := 30
    let net := netAmount amount_in fee_bps
    let amount_out := swapOutput rin rout net
    0 < rin ∧ 0 < rout ∧ 0 < amount_in ∧ 0 < fee_bps ∧ fee_bps < 10000 ∧
    kValue (rin + amount_in) (rout - amount_out) ≥ kValue rin rout := by
  native_decide

/-! ## Theorem 5: First Deposit Safety

The first LP deposit requires a minimum lock to prevent manipulation.
-/

/-- First deposit mints at least min_lock tokens if product is large enough.
    The condition (min_lock + 1)² ≤ prod ensures min_lock < sqrt(prod). -/
theorem first_deposit_safe
    {amount0 amount1 min_lock : ℕ}
    (hprod : (min_lock + 1) * (min_lock + 1) ≤ amount0 * amount1) :
    0 < lpMintFirst amount0 amount1 min_lock := by
  simp only [lpMintFirst]
  -- min_lock < sqrt(amount0 * amount1) follows from (min_lock + 1)² ≤ amount0 * amount1
  have hsqrt : min_lock + 1 ≤ Nat.sqrt (amount0 * amount1) := Nat.le_sqrt.mpr hprod
  omega

/-- Non-vacuity witness for first deposit -/
theorem witness_first_deposit :
    let amount0 := 10000
    let amount1 := 10000
    let min_lock := 1000
    (min_lock + 1) * (min_lock + 1) ≤ amount0 * amount1 ∧
    0 < lpMintFirst amount0 amount1 min_lock := by
  native_decide

/-! ## Theorem 6: Swap Output Underflow Protection

The swap output is always ≤ reserve, preventing underflow in reserve updates.
-/

/-- Swap output is bounded by reserve (prevents underflow) -/
theorem swap_output_le_reserve {rin rout net : ℕ} :
    swapOutput rin rout net ≤ rout := by
  simp only [swapOutput]
  apply Nat.div_le_of_le_mul
  calc rout * net ≤ rout * (rin + net) := by nlinarith [Nat.zero_le rin]
    _ = (rin + net) * rout := by ring

/-- Non-vacuity: the bound is tight (approaches rout as net → ∞) -/
theorem witness_swap_approaches_reserve :
    let rin := 1
    let rout := 1000
    let net := 1000000
    swapOutput rin rout net ≥ rout - 1 := by
  native_decide

/-! ## Removed: Sandwich Attack Theorem

The sandwich attack bound theorem has been removed as it requires:
1. Careful underflow guards for Nat subtraction
2. Multi-step state transition analysis
3. Fee accumulation accounting across legs

This is left for future work with a proper state machine model.
-/

/-! ## Theorem 7: The K-Gap Closed Form

**THE FUNDAMENTAL THEOREM OF CPMM K-GAP**:

For a zero-fee swap with input `a` on pool `(x, y)`:

    K_new - K_old = (y * a) % (x + a)

Equivalently: the K-increase is the Euclidean remainder when `y * a`
is divided by `x + a`.  This is always non-negative (K-monotonicity)
and bounded by `x + a` (bounded K-increase per swap).

**Proof sketch (algebraic)**:
  Let `d = x + a`, `q = (y*a) / d`, `r = (y*a) % d`.
  By Euclidean division: `d * q + r = y * a`.
  Then `K_new = d * (y - q) = d*y - d*q = d*y - (y*a - r) = y*x + r = K_old + r`.

**Properties proved in Lean** (see theorems below):
  1. Non-negative: remainder ≥ 0 (`k_gap_nonneg`)
  2. Bounded: K_gap < x + a (`k_gap_bounded`)
  3. Zero iff (x+a) | (y*a) (`k_gap_zero_iff`)
  4. Additive over sequential swaps (`executeBatchSwaps_K_gap_sum` in BatchCPMMUnification)

**Properties verified empirically** (GPU enumeration on H200, not proved in Lean):
  5. K_gap / (x+a) ∼ Uniform[0,1) for "random" inputs
  6. With fees: K_gap_fee ≥ K_gap_nofee
-/

/-- Output of a zero-fee swap is bounded by the output reserve.
    This is needed so that `y - output` does not underflow. -/
theorem swapOutputZeroFee_le (x y a : ℕ) :
    swapOutputZeroFee x y a ≤ y := by
  simp only [swapOutputZeroFee]
  apply Nat.div_le_of_le_mul
  calc y * a ≤ y * (x + a) := Nat.mul_le_mul_left y (Nat.le_add_left a x)
    _ = (x + a) * y := by ring

/-- THE K-GAP CLOSED FORM: K_new - K_old = (y * a) % (x + a).
    The exact amount by which K increases in a single zero-fee swap. -/
theorem k_gap_exact (x y a : ℕ) :
    (x + a) * (y - swapOutputZeroFee x y a) = x * y + (y * a) % (x + a) := by
  simp only [swapOutputZeroFee]
  set d := x + a with hd_def
  set q := (y * a) / d
  set r := (y * a) % d
  -- Euclidean division: d * q + r = y * a
  have heuc : d * q + r = y * a := Nat.div_add_mod (y * a) d
  -- q ≤ y (output bounded by reserve)
  have hq_le_y : q ≤ y := by
    apply Nat.div_le_of_le_mul
    calc y * a ≤ y * (x + a) := Nat.mul_le_mul_left y (Nat.le_add_left a x)
      _ = d * y := by rw [hd_def]; ring
  -- Main calculation via zify (lift to ℤ to avoid Nat subtraction issues)
  have hq_mul_le : d * q ≤ d * y := Nat.mul_le_mul_left d hq_le_y
  have hya_ge_r : r ≤ y * a := Nat.mod_le (y * a) d
  have hdq_le_dy : d * q ≤ y * a := by omega
  zify [hq_le_y, hq_mul_le, hya_ge_r, hdq_le_dy]
  -- Now in ℤ: d * (y - q) = x * y + r, given d * q + r = y * a, d = x + a
  have heuc_z : (d : ℤ) * q + r = y * a := by exact_mod_cast heuc
  have hd_z : (d : ℤ) = x + a := by exact_mod_cast hd_def
  nlinarith

/-- K-gap is non-negative (immediate from the closed form). -/
theorem k_gap_nonneg (x y a : ℕ) :
    (x + a) * (y - swapOutputZeroFee x y a) ≥ x * y := by
  rw [k_gap_exact x y a]
  omega

/-- K-gap is bounded: K_new - K_old < x + a. -/
theorem k_gap_bounded (x y a : ℕ) (hd : 0 < x + a) :
    (x + a) * (y - swapOutputZeroFee x y a) < x * y + (x + a) := by
  rw [k_gap_exact x y a]
  have : (y * a) % (x + a) < x + a := Nat.mod_lt (y * a) hd
  omega

/-- K-gap is zero iff (x+a) divides (y*a). -/
theorem k_gap_zero_iff (x y a : ℕ) :
    (x + a) * (y - swapOutputZeroFee x y a) = x * y ↔ (x + a) ∣ (y * a) := by
  rw [k_gap_exact x y a]
  constructor
  · intro h; exact Nat.dvd_of_mod_eq_zero (by omega)
  · intro h; rw [Nat.dvd_iff_mod_eq_zero.mp h]; omega

/-- Non-vacuity: K-gap with concrete values -/
theorem witness_k_gap :
    let x := 1000; let y := 1000; let a := 100
    (x + a) * (y - swapOutputZeroFee x y a) = x * y + (y * a) % (x + a) ∧
    (y * a) % (x + a) = 1000 ∧  -- The K-gap is exactly 1000
    (x + a) * (y - swapOutputZeroFee x y a) > x * y := by  -- K strictly increases
  native_decide

/-! ## Non-Vacuity Verification Section

We prove that our hypotheses are satisfiable with concrete values.
This ensures we haven't accidentally proven "False → anything".
-/

/-- Concrete computation showing swap_output_lt_reserve hypotheses are satisfiable -/
theorem witness_swap_output :
    let rin := 1000
    let rout := 2000
    let net := 100
    0 < rin ∧ 0 < rout ∧ 0 < net ∧ swapOutput rin rout net < rout := by
  native_decide

/-- Concrete computation for k_monotone hypotheses -/
theorem witness_k_monotone :
    let rin := 1000
    let rout := 1000
    let amount_in := 100
    let fee_bps := 30
    0 < rin ∧ 0 < rout ∧ 0 < amount_in ∧ fee_bps ≤ 10000 := by
  decide

end CPMMInvariants
