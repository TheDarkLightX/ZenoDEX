import Proofs.CPMMSandwichCertificate
import Proofs.CpmmSwapV8ExactOutMinimality
import Mathlib.Tactic

/-!
# Fee-Aware Sandwich Certificate for CPMM Split Routing

`CPMMConcavity` and `CPMMSandwichCertificate` treat the ZERO-FEE objective and
explicitly disclaim fee-adjusted routing. This file closes that gap.

The fee-adjusted output is `f(a) = cpmmOut x y (net a)` with
`net a = a − ⌈a·fee/10⁴⌉ = ⌊a·ψ/10⁴⌋`, `ψ = 10⁴ − fee` (the second equality is
the runtime identity proved in `CpmmSwapV8ExactOutMinimality`).

**The fee-adjusted output is NOT grade-O(1)** (`witness_fee_not_grade_one`:
when the net staircase steps, the output jumps by the local envelope slope —
up to 500 for pool (1, 1000) at 50% fee). So neither Part III's graded
certificate nor a constant-δ sandwich applies naively. The honest structure:

  f is sandwiched within `δ = 1 + y/(x+1)` below the concave envelope
  `a ↦ Hᵉ(c·a)`, `Hᵉ(t) = y·t/(x+t)`, `c = ψ/10⁴`,

because `y/(x+1)` is the GLOBAL slope cap of `Hᵉ` on `t ≥ 0`. Composing two
pools gives `SandwichConcave Δ` with `Δ = 2 + y₀/(x₀+1) + y₁/(x₁+1)`, and
`sandwich_certificate_linear` yields, for every pool configuration and fee:

  objFee(j) ≤ objFee(a★) + Δ·(d+1),   d = |j − a★|.

For deep pools (`yᵢ ≤ xᵢ + 1`) this collapses to the integer bound
`objFee(j) ≤ objFee(a★) + 4·d + 4`.

This also makes precise exactly when `SplitRoutingUnimodality`'s assumed
closeness hypothesis is satisfiable: the per-pool closeness constant is
`1 + y/(x+1)`, small iff the pool is deep relative to its output reserve.

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `netAmt` / `netAmt_eq_runtime` | Def/Bridge | ⌊a·ψ/10⁴⌋ = a − ⌈a·fee/10⁴⌉ (runtime form) |
| 2 | `HenvQ_mono` / `HenvQ_step_le` | Core | envelope monotone; global slope cap y/(x+1) |
| 3 | `HenvQ_affine_concave` | Core | a ↦ Hᵉ(c·a) is discretely concave (all x, c ≥ 0) |
| 4 | `cpmmOutFee_sandwich` | Main | per-pool sandwich with δ = 1 + y/(x+1) |
| 5 | `cpmm_fee_split_sandwich` | Bridge | split objective is SandwichConcave Δ |
| 6 | `cpmm_fee_split_certificate_linear` | Main | objFee(j) ≤ objFee(a★) + Δ·(d+1), ALL pools/fees |
| 7 | `cpmm_fee_split_certificate_deep_pools` | Main | y ≤ x+1 both pools ⟹ ℤ bound 4·d + 4 |
| 8 | `cpmmOutFee_zero_fee` | Bridge | fee = 0 recovers the zero-fee output |
| 9 | `witness_fee_not_grade_one` | Witness | fee-adjusted output has second difference 500 |
-/

namespace Proofs
namespace CPMMFeeAware

open CPMMConcavity (cpmmOut)
open CPMMSandwich (RatDiscreteConcave SandwichConcave sandwich_certificate_linear
  rat_discrete_concave_reverse)

/-- Basis-point denominator. -/
def BPS : ℕ := 10000

/-- Net amount after the fee, floor form: `⌊a·(BPS − fee)/BPS⌋`. -/
def netAmt (fee a : ℕ) : ℕ := a * (BPS - fee) / BPS

/-- The runtime computes `net = a − ⌈a·fee/BPS⌉`; this equals `netAmt`
    (the v8 kernel identity, re-exported for this surface). -/
theorem netAmt_eq_runtime (fee a : ℕ) :
    a - (a * fee) ⌈/⌉ BPS = netAmt fee a :=
  TauSwap.CPMM.V8.net_actual_eq_floor_mul a fee BPS (by norm_num [BPS])

/-- Fee-adjusted CPMM output: swap the post-fee net amount. -/
def cpmmOutFee (x y fee a : ℕ) : ℕ := cpmmOut x y (netAmt fee a)

/-- Zero fee recovers the raw output. -/
theorem cpmmOutFee_zero_fee (x y a : ℕ) : cpmmOutFee x y 0 a = cpmmOut x y a := by
  simp [cpmmOutFee, netAmt, BPS]

/-! ## The rational envelope at rational arguments -/

/-- `Hᵉ(t) = y·t/(x+t)` over ℚ (junk value 0 when the denominator vanishes,
    which for `t ≥ 0` happens only at `x = 0, t = 0`). -/
noncomputable def HenvQ (x y : ℕ) (t : ℚ) : ℚ := (y : ℚ) * t / ((x : ℚ) + t)

/-- At natural arguments the envelope agrees with `cpmmOutQ`. -/
theorem HenvQ_natCast (x y a : ℕ) : HenvQ x y (a : ℚ) = CPMMSandwich.cpmmOutQ x y a := by
  rw [HenvQ, CPMMSandwich.cpmmOutQ]
  push_cast
  ring_nf

/-- The envelope is monotone on `t ≥ 0` (including the junk point). -/
theorem HenvQ_mono (x y : ℕ) {s t : ℚ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HenvQ x y s ≤ HenvQ x y t := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · -- x = 0: H(0) = 0 and H(t) = y for t > 0.
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [HenvQ, ← hs0]
      simp
      rcases eq_or_lt_of_le (hs0.le.trans hst) with ht0 | ht0
      · rw [HenvQ, ← ht0]; simp
      · rw [HenvQ]
        push_cast
        rw [zero_add]
        rw [mul_div_assoc, div_self (ne_of_gt ht0), mul_one]
        positivity
    · have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
      rw [HenvQ, HenvQ]
      push_cast
      rw [zero_add, zero_add, mul_div_assoc, mul_div_assoc,
        div_self (ne_of_gt hs0), div_self (ne_of_gt ht0)]
  · have hxQ : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
    have hds : (0 : ℚ) < (x : ℚ) + s := by linarith
    have hdt : (0 : ℚ) < (x : ℚ) + t := by linarith
    rw [HenvQ, HenvQ, div_le_div_iff₀ hds hdt]
    have hy : (0 : ℚ) ≤ (y : ℚ) := by positivity
    nlinarith [mul_nonneg hy hxQ.le]

/-- **GLOBAL SLOPE CAP**: one unit step of the envelope is at most `y/(x+1)`
    everywhere on `t ≥ 0` (with equality at `x = 0, t = 0`). -/
theorem HenvQ_step_le (x y : ℕ) {t : ℚ} (ht : 0 ≤ t) :
    HenvQ x y (t + 1) ≤ HenvQ x y t + (y : ℚ) / ((x : ℚ) + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · -- x = 0: H jumps from 0 to y at t = 0 and is constant y afterwards;
    -- the cap y/(0+1) = y absorbs the jump.
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · rw [HenvQ, HenvQ, ← ht0]
      push_cast
      simp
    · have h1 : HenvQ 0 y (t + 1) = (y : ℚ) := by
        rw [HenvQ]
        push_cast
        rw [zero_add, mul_div_assoc, div_self (by linarith), mul_one]
      have h2 : HenvQ 0 y t = (y : ℚ) := by
        rw [HenvQ]
        push_cast
        rw [zero_add, mul_div_assoc, div_self (ne_of_gt ht0), mul_one]
      rw [h1, h2]
      push_cast
      have : (0 : ℚ) ≤ (y : ℚ) := by positivity
      linarith
  · have hxQ : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
    have hd0 : (0 : ℚ) < (x : ℚ) + t := by linarith
    have hd1 : (0 : ℚ) < (x : ℚ) + (t + 1) := by linarith
    have hx1 : (0 : ℚ) < (x : ℚ) + 1 := by linarith
    rw [HenvQ, HenvQ, div_add_div _ _ (ne_of_gt hd0) (ne_of_gt hx1),
      div_le_div_iff₀ hd1 (by positivity)]
    have hy : (0 : ℚ) ≤ (y : ℚ) := by positivity
    nlinarith [mul_nonneg hy ht, mul_nonneg (mul_nonneg hy ht) ht,
      mul_nonneg hy hxQ.le, mul_nonneg (mul_nonneg hy hxQ.le) ht]

/-- The envelope along any arithmetic progression `a ↦ Hᵉ(c·a)` (`c ≥ 0`) is
    discretely concave — for every pool including `x = 0`. -/
theorem HenvQ_affine_concave (x y D : ℕ) (c : ℚ) (hc : 0 ≤ c) :
    RatDiscreteConcave (fun a => HenvQ x y (c * a)) D := by
  intro i hi
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · -- x = 0: values are 0 at the junk point, y afterwards; slopes y,0,0,…
    have hval : ∀ t : ℚ, 0 < t → HenvQ 0 y t = (y : ℚ) := by
      intro t ht
      rw [HenvQ]
      push_cast
      rw [zero_add, mul_div_assoc, div_self (ne_of_gt ht), mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp only [Nat.cast_zero, zero_add, mul_zero]
      have h0 : HenvQ 0 y 0 = 0 := by
        rw [HenvQ]
        simp
      have h1 := hval (c * 1) (by nlinarith)
      have h2 := hval (c * 2) (by nlinarith)
      rw [h0, h1, h2]
      have hy : (0 : ℚ) ≤ (y : ℚ) := by positivity
      linarith
    · have hiQ : (0 : ℚ) < (i : ℚ) := by exact_mod_cast hipos
      have h0 := hval (c * i) (by nlinarith)
      have h1 := hval (c * ((i : ℚ) + 1)) (by nlinarith)
      have h2 := hval (c * ((i : ℚ) + 2)) (by nlinarith)
      rw [h0, h1, h2]
  · -- x ≥ 1: clear the (positive) denominators and reduce to 0 ≤ 2yxc².
    have hxQ : (0 : ℚ) < (x : ℚ) := by exact_mod_cast hx
    have hiQ : (0 : ℚ) ≤ (i : ℚ) := by positivity
    have hci0 : (0 : ℚ) ≤ c * i := mul_nonneg hcpos.le hiQ
    have hci1 : (0 : ℚ) ≤ c * ((i : ℚ) + 1) := mul_nonneg hcpos.le (by linarith)
    have hci2 : (0 : ℚ) ≤ c * ((i : ℚ) + 2) := mul_nonneg hcpos.le (by linarith)
    have d0 : (0 : ℚ) < (x : ℚ) + c * i := by linarith
    have d1 : (0 : ℚ) < (x : ℚ) + c * ((i : ℚ) + 1) := by linarith
    have d2 : (0 : ℚ) < (x : ℚ) + c * ((i : ℚ) + 2) := by linarith
    rw [HenvQ, HenvQ, HenvQ,
      div_sub_div _ _ (ne_of_gt d2) (ne_of_gt d1),
      div_sub_div _ _ (ne_of_gt d1) (ne_of_gt d0),
      div_le_div_iff₀ (mul_pos d2 d1) (mul_pos d1 d0)]
    have hy : (0 : ℚ) ≤ (y : ℚ) := by positivity
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hy hxQ.le) hcpos.le) hcpos.le,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hy hxQ.le) hcpos.le) hcpos.le) hiQ,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hy hxQ.le) hcpos.le) hcpos.le) hxQ.le,
      mul_pos (mul_pos d0 d1) d2, mul_pos d0 d1, mul_pos d1 d2]

/-! ## The per-pool fee-aware sandwich -/

/-- The fee ratio `c = (BPS − fee)/BPS ∈ [0, 1]` as a rational. -/
noncomputable def feeRatio (fee : ℕ) : ℚ := ((BPS - fee : ℕ) : ℚ) / (BPS : ℚ)

theorem feeRatio_nonneg (fee : ℕ) : 0 ≤ feeRatio fee := by
  rw [feeRatio]; positivity

/-- The net amount sits in the unit interval below `c·a`:
    `net ≤ c·a < net + 1`. -/
theorem netAmt_sandwich (fee a : ℕ) :
    ((netAmt fee a : ℕ) : ℚ) ≤ feeRatio fee * a ∧
      feeRatio fee * a < ((netAmt fee a : ℕ) : ℚ) + 1 := by
  have hB : (0 : ℚ) < (BPS : ℚ) := by norm_num [BPS]
  constructor
  · have h : netAmt fee a * BPS ≤ a * (BPS - fee) := by
      simp only [netAmt, BPS]
      omega
    have hQ : ((netAmt fee a * BPS : ℕ) : ℚ) ≤ ((a * (BPS - fee) : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [feeRatio, div_mul_eq_mul_div, le_div_iff₀ hB]
    push_cast at hQ ⊢
    nlinarith [hQ]
  · have h : a * (BPS - fee) < (netAmt fee a + 1) * BPS := by
      simp only [netAmt, BPS]
      omega
    have hQ : ((a * (BPS - fee) : ℕ) : ℚ) < (((netAmt fee a + 1) * BPS : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [feeRatio, div_mul_eq_mul_div, div_lt_iff₀ hB]
    push_cast at hQ ⊢
    nlinarith [hQ]

/-- **PER-POOL FEE-AWARE SANDWICH**: the fee-adjusted output sits within
    `1 + y/(x+1)` below the concave envelope `a ↦ Hᵉ(c·a)`, for every pool
    `(x, y)` and every fee. The constant is forced: `y/(x+1)` is the price of
    one staircase step of the net amount, and `1` is the price of the output
    floor. -/
theorem cpmmOutFee_sandwich (x y fee a : ℕ) :
    ((cpmmOutFee x y fee a : ℤ) : ℚ) ≤ HenvQ x y (feeRatio fee * a) ∧
      HenvQ x y (feeRatio fee * a) ≤
        ((cpmmOutFee x y fee a : ℤ) : ℚ) + (1 + (y : ℚ) / ((x : ℚ) + 1)) := by
  obtain ⟨hlo, hhi⟩ := netAmt_sandwich fee a
  set n := netAmt fee a with hn
  constructor
  · -- floor ≤ H(n) ≤ H(c·a)
    have h1 : ((cpmmOut x y n : ℤ) : ℚ) ≤ CPMMSandwich.cpmmOutQ x y n :=
      CPMMSandwich.cpmmOut_le_envelope x y n
    have h2 : HenvQ x y (n : ℚ) ≤ HenvQ x y (feeRatio fee * a) :=
      HenvQ_mono x y (by positivity) hlo
    rw [HenvQ_natCast] at h2
    exact le_trans (by exact_mod_cast h1) h2
  · -- H(c·a) ≤ H(n+1) ≤ H(n) + y/(x+1) < floor + 1 + y/(x+1)
    have h1 : HenvQ x y (feeRatio fee * a) ≤ HenvQ x y ((n : ℚ) + 1) :=
      HenvQ_mono x y (mul_nonneg (feeRatio_nonneg fee) (by positivity))
        (le_of_lt hhi)
    have h2 : HenvQ x y ((n : ℚ) + 1) ≤ HenvQ x y (n : ℚ) + (y : ℚ) / ((x : ℚ) + 1) :=
      HenvQ_step_le x y (by positivity)
    have h3 : CPMMSandwich.cpmmOutQ x y n < ((cpmmOut x y n : ℤ) : ℚ) + 1 :=
      CPMMSandwich.envelope_lt_cpmmOut_add_one x y n
    rw [HenvQ_natCast] at h2
    have : ((cpmmOutFee x y fee a : ℤ) : ℚ) = ((cpmmOut x y n : ℤ) : ℚ) := by
      rw [cpmmOutFee, hn]
    rw [this]
    linarith

/-! ## The fee-aware split objective and its certificates -/

/-- Fee-adjusted split objective: route `a` through pool 0 and `D − a`
    through pool 1, each charged its own fee. -/
def cpmmFeeSplitObj (x₀ y₀ fee₀ x₁ y₁ fee₁ D : ℕ) (a : ℕ) : ℤ :=
  (cpmmOutFee x₀ y₀ fee₀ a : ℤ) + (cpmmOutFee x₁ y₁ fee₁ (D - a) : ℤ)

/-- The fee-aware split objective is sandwiched with
    `Δ = 2 + y₀/(x₀+1) + y₁/(x₁+1)` — every pool, every fee. -/
theorem cpmm_fee_split_sandwich (x₀ y₀ fee₀ x₁ y₁ fee₁ D : ℕ) :
    SandwichConcave (2 + (y₀ : ℚ) / ((x₀ : ℚ) + 1) + (y₁ : ℚ) / ((x₁ : ℚ) + 1))
      (cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D) D := by
  refine ⟨fun a => HenvQ x₀ y₀ (feeRatio fee₀ * a)
    + HenvQ x₁ y₁ (feeRatio fee₁ * (D - a : ℕ)), ?_, ?_⟩
  · intro i hi
    have h0 := HenvQ_affine_concave x₀ y₀ D (feeRatio fee₀) (feeRatio_nonneg fee₀) i hi
    have h1 := rat_discrete_concave_reverse
      (fun a => HenvQ x₁ y₁ (feeRatio fee₁ * a)) D
      (HenvQ_affine_concave x₁ y₁ D (feeRatio fee₁) (feeRatio_nonneg fee₁)) i hi
    simp only at h0 h1
    linarith
  · intro i _
    obtain ⟨l0, u0⟩ := cpmmOutFee_sandwich x₀ y₀ fee₀ i
    obtain ⟨l1, u1⟩ := cpmmOutFee_sandwich x₁ y₁ fee₁ (D - i)
    constructor
    · simp only [cpmmFeeSplitObj]
      push_cast
      push_cast at l0 l1
      linarith
    · simp only [cpmmFeeSplitObj]
      push_cast
      push_cast at u0 u1
      linarith

/-- **FEE-AWARE LINEAR CERTIFICATE** (every pool configuration, every fee):
    the 2-comparison certificate at `a★` bounds every competitor by

      objFee(j) ≤ objFee(a★) + Δ·(d+1),
      Δ = 2 + y₀/(x₀+1) + y₁/(x₁+1),  d = |j − a★|.

    Δ is small exactly when the pools are deep relative to their output
    reserves — the quantitative content behind `SplitRoutingUnimodality`'s
    assumed closeness hypothesis. -/
theorem cpmm_fee_split_certificate_linear
    (x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star : ℕ) (ha : a_star ≤ D)
    (h_prev : 0 < a_star →
      cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star ≥
        cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D (a_star - 1))
    (h_next : a_star < D →
      cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star ≥
        cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D (a_star + 1)) :
    ∀ j, j ≤ D →
      ((cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D j : ℤ) : ℚ) ≤
        ((cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star : ℤ) : ℚ)
          + (2 + (y₀ : ℚ) / ((x₀ : ℚ) + 1) + (y₁ : ℚ) / ((x₁ : ℚ) + 1))
              * (|(j : ℚ) - (a_star : ℚ)| + 1) :=
  sandwich_certificate_linear _ _ D a_star ha
    (cpmm_fee_split_sandwich x₀ y₀ fee₀ x₁ y₁ fee₁ D) h_prev h_next

/-- **DEEP-POOL COROLLARY** (`yᵢ ≤ xᵢ + 1` for both pools): the fee-aware
    certificate error collapses to the clean integer bound `4·d + 4`. -/
theorem cpmm_fee_split_certificate_deep_pools
    (x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star : ℕ) (ha : a_star ≤ D)
    (hdeep₀ : y₀ ≤ x₀ + 1) (hdeep₁ : y₁ ≤ x₁ + 1)
    (h_prev : 0 < a_star →
      cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star ≥
        cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D (a_star - 1))
    (h_next : a_star < D →
      cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star ≥
        cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D (a_star + 1)) :
    ∀ j, j ≤ D →
      cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D j ≤
        cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star
          + 4 * |(j : ℤ) - (a_star : ℤ)| + 4 := by
  intro j hj
  have h := cpmm_fee_split_certificate_linear x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star ha
    h_prev h_next j hj
  have hr₀ : (y₀ : ℚ) / ((x₀ : ℚ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hdeep₀
  have hr₁ : (y₁ : ℚ) / ((x₁ : ℚ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hdeep₁
  have habs : (0 : ℚ) ≤ |(j : ℚ) - (a_star : ℚ)| := abs_nonneg _
  have hZ : ((cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D j : ℤ) : ℚ) ≤
      ((cpmmFeeSplitObj x₀ y₀ fee₀ x₁ y₁ fee₁ D a_star
        + 4 * |(j : ℤ) - (a_star : ℤ)| + 4 : ℤ) : ℚ) := by
    push_cast
    nlinarith [h, hr₀, hr₁, habs]
  exact_mod_cast hZ

/-- **THE FEE-ADJUSTED OUTPUT IS NOT GRADE-1** (why a fee-aware certificate
    cannot reuse Part III's constants): pool (1, 1000) at 50% fee has
    net(0..3) = 0,0,1,1 and outputs 0,0,500,500 — a second difference of 500.
    The sandwich constant 1 + y/(x+1) = 501 absorbs exactly this jump. -/
theorem witness_fee_not_grade_one :
    netAmt 5000 0 = 0 ∧ netAmt 5000 1 = 0 ∧ netAmt 5000 2 = 1 ∧
    cpmmOutFee 1 1000 5000 0 = 0 ∧
    cpmmOutFee 1 1000 5000 1 = 0 ∧
    cpmmOutFee 1 1000 5000 2 = 500 ∧
    ¬ ((cpmmOutFee 1 1000 5000 2 : ℤ) + cpmmOutFee 1 1000 5000 0 ≤
        2 * cpmmOutFee 1 1000 5000 1 + 1) := by
  native_decide

end CPMMFeeAware
end Proofs
