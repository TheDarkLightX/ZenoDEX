import Proofs.AntiFragmentation
import Proofs.CPMMInvariants
import Mathlib.Tactic

/-!
# Fee-Aware Anti-Fragmentation for CPMM

**ShapeForge promotion**: `fee_aware_fragmentation_elimination` (TESTED_ONLY → PROVED)

**THEOREM**: For a CPMM pool (x, y) with ceiling-based fee rate `fee_bps ≤ 10000`,
executing a single swap of gross amount (a₁ + a₂) always produces output ≥ the
total output of executing a₁ then a₂ sequentially through the fee pipeline.

  feeAwareOut(a₁ + a₂) ≥ feeAwareOut₁(a₁) + feeAwareOut₂(a₂)

**Proof architecture** (three-layer composition):
1. **Ceiling algebra**: `ceilDiv` is subadditive — `⌈(a+b)/d⌉ ≤ ⌈a/d⌉ + ⌈b/d⌉`
2. **Fee algebra**: ceiling-fee subadditivity lifts to net-amount superadditivity
3. **Composition**: net-amount advantage + swap monotonicity + zero-fee anti-fragmentation

**Key insight**: The ceiling-based fee `computeFee` is subadditive (splitting input
increases total fees), so the net amount after fees is superadditive (combining input
preserves more net value). This compounds with the zero-fee anti-fragmentation
advantage from `AntiFragmentation.lean`.

## Evidence chain
- Python: 0/50,000+ empirical violations (random testing with fees 1–10000 bps)
- `AntiFragmentation.lean`: zero-fee case (Lean proof, 0 sorry)
- `FeeSplitRoundingGap.lean`: floor-fee splitting gap ≤ 1 (Lean proof)
- This file: fee-aware case via ceiling algebra (Lean proof, 0 sorry)
-/

namespace FeeAwareAntiFragmentation

open CPMMInvariants
open AntiFragmentation

/-! ## Section 1: Ceiling Division Algebra

The algebraic core: ceiling division is SUBADDITIVE (dual to floor division's
superadditivity from `AntiFragmentation.lean`). This duality is the bridge
between the zero-fee and fee-aware worlds.

  Floor: ⌊(a+b)/d⌋ ≥ ⌊a/d⌋ + ⌊b/d⌋  (splitting LOSES — good for output)
  Ceil:  ⌈(a+b)/d⌉ ≤ ⌈a/d⌉ + ⌈b/d⌉  (splitting GAINS — bad for fees)
-/

/-- CEILING PROPERTY: `⌈a/d⌉ * d ≥ a` — the ceiling rounds up to a multiple of d.
    Proof: from Euclidean division of (a + d - 1), the remainder is ≤ d - 1,
    so the quotient × d ≥ (a + d - 1) - (d - 1) = a.
    For the upper bound `⌈a/d⌉ * d < a + d`, see `ceil_div_mul_lt`. -/
theorem ceil_div_mul_ge (a d : ℕ) (hd : 0 < d) :
    ceilDiv a d * d ≥ a := by
  unfold ceilDiv
  have hmod_lt : (a + d - 1) % d < d := Nat.mod_lt _ hd
  have hdm := Nat.div_add_mod (a + d - 1) d
  have hcomm : (a + d - 1) / d * d = d * ((a + d - 1) / d) := by ring
  rw [hcomm]
  omega

/-- CEILING OVERSHOOT BOUND: `⌈a/d⌉ * d < a + d`.
    Combined with ceil_div_mul_ge, this gives `a ≤ ⌈a/d⌉ * d < a + d`. -/
theorem ceil_div_mul_lt (a d : ℕ) (hd : 0 < d) :
    ceilDiv a d * d < a + d := by
  unfold ceilDiv
  have hdm := Nat.div_add_mod (a + d - 1) d
  have hcomm : (a + d - 1) / d * d = d * ((a + d - 1) / d) := by ring
  rw [hcomm]
  omega

/-- CEILING MONOTONICITY: a₁ ≤ a₂ → ⌈a₁/d⌉ ≤ ⌈a₂/d⌉.
    Combined with subadditivity, this gives a complete order-theoretic
    characterization of ceiling division. -/
theorem ceilDiv_mono {a₁ a₂ d : ℕ} (h : a₁ ≤ a₂) :
    ceilDiv a₁ d ≤ ceilDiv a₂ d := by
  unfold ceilDiv
  exact Nat.div_le_div_right (by omega)

/-- CEILING SUBADDITIVITY: `⌈(a₁+a₂)/d⌉ ≤ ⌈a₁/d⌉ + ⌈a₂/d⌉`.
    Splitting a numerator across two ceiling divisions can only INCREASE the total.
    This is the fee-world dual of floor_div_subadditive.

    Proof: from ceil_div_mul_ge, the sum of ceilings × d covers a₁ + a₂.
    Any n with n*d ≥ a₁+a₂ satisfies ⌈(a₁+a₂)/d⌉ ≤ n, because
    a₁+a₂+d-1 < n*d + d = (n+1)*d. -/
theorem ceil_div_subadditive (a₁ a₂ d : ℕ) (hd : 0 < d) :
    ceilDiv (a₁ + a₂) d ≤ ceilDiv a₁ d + ceilDiv a₂ d := by
  set n := ceilDiv a₁ d + ceilDiv a₂ d
  have h1 := ceil_div_mul_ge a₁ d hd
  have h2 := ceil_div_mul_ge a₂ d hd
  have hexpand : n * d = ceilDiv a₁ d * d + ceilDiv a₂ d * d := by ring
  have hnd : n * d ≥ a₁ + a₂ := by omega
  -- (a₁+a₂+d-1)/d < n+1, hence ≤ n
  unfold ceilDiv
  have hlt : a₁ + a₂ + d - 1 < d * (n + 1) := by
    have : d * (n + 1) = n * d + d := by ring
    omega
  exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul hlt)

/-- CEILING GAP BOUND: the gap between sum-of-ceilings and ceiling-of-sum is ≤ 1.
    This is the ceiling analogue of AntiFragmentation.floor_div_carry_le_one.

    Proof by contradiction: if gap ≥ 2, then (sum_of_ceilings) * d gives both
    an upper bound (< a₁+a₂+2d from individual overshoot) and a lower bound
    (≥ a₁+a₂+2d from ceiling property of sum + gap ≥ 2), which is impossible. -/
theorem ceil_div_gap_le_one (a₁ a₂ d : ℕ) (hd : 0 < d) :
    ceilDiv a₁ d + ceilDiv a₂ d ≤ ceilDiv (a₁ + a₂) d + 1 := by
  by_contra h
  push_neg at h
  -- h : ceilDiv a₁ d + ceilDiv a₂ d ≥ ceilDiv (a₁ + a₂) d + 2
  have hlt1 := ceil_div_mul_lt a₁ d hd
  have hlt2 := ceil_div_mul_lt a₂ d hd
  have hge := ceil_div_mul_ge (a₁ + a₂) d hd
  -- Upper bound: (ceilDiv a₁ d + ceilDiv a₂ d) * d < a₁ + a₂ + 2d
  have hsum_lt : (ceilDiv a₁ d + ceilDiv a₂ d) * d < a₁ + a₂ + 2 * d := by
    have hexpand : (ceilDiv a₁ d + ceilDiv a₂ d) * d =
        ceilDiv a₁ d * d + ceilDiv a₂ d * d := by ring
    omega
  -- Lower bound: (ceilDiv (a₁+a₂) d + 2) * d ≥ a₁ + a₂ + 2d
  have hlow : (ceilDiv (a₁ + a₂) d + 2) * d ≥ a₁ + a₂ + 2 * d := by
    have hexpand : (ceilDiv (a₁ + a₂) d + 2) * d =
        ceilDiv (a₁ + a₂) d * d + 2 * d := by ring
    omega
  -- From h: sum_of_ceilings ≥ ceil_of_sum + 2, so sum_of_ceilings * d ≥ (ceil_of_sum + 2) * d
  have hmono : (ceilDiv (a₁ + a₂) d + 2) * d ≤ (ceilDiv a₁ d + ceilDiv a₂ d) * d :=
    Nat.mul_le_mul_right d h
  -- Contradiction: a₁+a₂+2d ≤ ... < a₁+a₂+2d
  omega

/-! ## Section 2: Fee Algebra

The fee pipeline: `computeFee(amount, bps) = ⌈amount × bps / 10000⌉`.
Since `ceilDiv` is subadditive, so is `computeFee` (in the amount argument).
This makes `netAmount = gross - fee` superadditive: combining inputs preserves
more net value than splitting them.
-/

/-- FEE BOUNDED BY AMOUNT: for fee rates ≤ 100% (bps ≤ 10000),
    the fee never exceeds the gross amount.

    Proof: `computeFee a bps = ⌈a·bps/10000⌉`. When bps ≤ 10000,
    a·bps ≤ a·10000, so ⌈a·bps/10000⌉ ≤ ⌈a·10000/10000⌉ = a.
    The last step uses Nat.div_lt_of_lt_mul to convert ⌊x/d⌋ ≤ a
    into x < (a+1)·d, a pure linear inequality. -/
theorem fee_le_amount (a fee_bps : ℕ) (hbps : fee_bps ≤ 10000) :
    computeFee a fee_bps ≤ a := by
  unfold computeFee ceilDiv
  have hD : 0 < (10000 : ℕ) := by decide
  have hmul : a * fee_bps ≤ a * 10000 := Nat.mul_le_mul_left a hbps
  -- Need: (a * fee_bps + 9999) / 10000 ≤ a
  -- ⟺ (a * fee_bps + 9999) < 10000 * (a + 1)  [by div_lt → lt_succ]
  suffices h : a * fee_bps + 10000 - 1 < 10000 * (a + 1) by
    exact Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul h)
  have : 10000 * (a + 1) = a * 10000 + 10000 := by ring
  omega

/-- FEE SUBADDITIVITY: splitting an order does not decrease total fees (ceiling effect).
    `computeFee(a₁+a₂, bps) ≤ computeFee(a₁, bps) + computeFee(a₂, bps)`.

    Proof: `computeFee` is `ceilDiv` composed with the linear map `a ↦ a·bps`.
    Since `(a₁+a₂)·bps = a₁·bps + a₂·bps`, ceiling subadditivity applies directly. -/
theorem fee_subadditive (a₁ a₂ fee_bps : ℕ) :
    computeFee (a₁ + a₂) fee_bps ≤ computeFee a₁ fee_bps + computeFee a₂ fee_bps := by
  unfold computeFee
  have hmul : (a₁ + a₂) * fee_bps = a₁ * fee_bps + a₂ * fee_bps := by ring
  rw [hmul]
  exact ceil_div_subadditive (a₁ * fee_bps) (a₂ * fee_bps) 10000 (by decide)

/-- FEE GAP TIGHT: the gap between split fees and combined fee is at most 1.
    `computeFee(a₁, bps) + computeFee(a₂, bps) ≤ computeFee(a₁+a₂, bps) + 1`.

    Combined with fee_subadditive, this fully characterizes the fee splitting effect:
    the extra cost of splitting is EXACTLY 0 or 1 unit. -/
theorem fee_gap_le_one (a₁ a₂ fee_bps : ℕ) :
    computeFee a₁ fee_bps + computeFee a₂ fee_bps ≤ computeFee (a₁ + a₂) fee_bps + 1 := by
  unfold computeFee
  have hmul : (a₁ + a₂) * fee_bps = a₁ * fee_bps + a₂ * fee_bps := by ring
  rw [hmul]
  exact ceil_div_gap_le_one (a₁ * fee_bps) (a₂ * fee_bps) 10000 (by decide)

/-- FEE MONOTONICITY: higher gross amount → higher fee (ceiling fees are monotone).
    Immediate from `ceilDiv_mono` composed with multiplication monotonicity. -/
theorem fee_mono {a₁ a₂ : ℕ} (fee_bps : ℕ) (h : a₁ ≤ a₂) :
    computeFee a₁ fee_bps ≤ computeFee a₂ fee_bps := by
  unfold computeFee
  exact ceilDiv_mono (Nat.mul_le_mul_right fee_bps h)

/-- NET AMOUNT SUPERADDITIVITY: combining gross inputs preserves at least as much net value.
    `netAmount(a₁+a₂, bps) ≥ netAmount(a₁, bps) + netAmount(a₂, bps)`.

    This is the key bridge between fee algebra and swap algebra: the single
    execution feeds a LARGER net amount into the pool than the sum of individual
    net amounts, compounding the zero-fee anti-fragmentation advantage.

    Requires `fee_bps ≤ 10000` (fee rate ≤ 100%) so that ℕ subtractions don't
    truncate. This is economically meaningful — no DEX charges > 100% fee. -/
theorem net_amount_superadditive (a₁ a₂ fee_bps : ℕ) (hbps : fee_bps ≤ 10000) :
    netAmount (a₁ + a₂) fee_bps ≥ netAmount a₁ fee_bps + netAmount a₂ fee_bps := by
  unfold netAmount
  set f := computeFee (a₁ + a₂) fee_bps
  set f₁ := computeFee a₁ fee_bps
  set f₂ := computeFee a₂ fee_bps
  have hfee := fee_subadditive a₁ a₂ fee_bps       -- f ≤ f₁ + f₂
  have hf₁ := fee_le_amount a₁ fee_bps hbps         -- f₁ ≤ a₁
  have hf₂ := fee_le_amount a₂ fee_bps hbps         -- f₂ ≤ a₂
  -- With fee ≤ amount, ℕ subtractions are exact:
  -- (a₁+a₂) - f ≥ (a₁+a₂) - (f₁+f₂) = (a₁-f₁) + (a₂-f₂)
  omega

/-- NET AMOUNT GAP TIGHT CHARACTERIZATION: the superadditivity gap is EXACTLY 0 or 1.
    This is the **equality** version of the superadditivity inequality — it fully
    characterizes the rounding behavior of the fee pipeline.

    netAmount(a₁+a₂) - (netAmount(a₁) + netAmount(a₂)) ∈ {0, 1}

    Proof: the gap equals `(f₁ + f₂) - f` where f = computeFee. By
    `fee_subadditive`, f ≤ f₁ + f₂. By `fee_gap_le_one`, f₁ + f₂ ≤ f + 1.
    So the gap is 0 or 1, and both are achievable (see witnesses in Section 6). -/
theorem net_amount_gap_tight (a₁ a₂ fee_bps : ℕ) (hbps : fee_bps ≤ 10000) :
    ∃ gap : ℕ, gap ≤ 1 ∧
      netAmount (a₁ + a₂) fee_bps = netAmount a₁ fee_bps + netAmount a₂ fee_bps + gap := by
  set f := computeFee (a₁ + a₂) fee_bps
  set f₁ := computeFee a₁ fee_bps
  set f₂ := computeFee a₂ fee_bps
  have hfee := fee_subadditive a₁ a₂ fee_bps       -- f ≤ f₁ + f₂
  have hgap := fee_gap_le_one a₁ a₂ fee_bps         -- f₁ + f₂ ≤ f + 1
  have hf₁ := fee_le_amount a₁ fee_bps hbps
  have hf₂ := fee_le_amount a₂ fee_bps hbps
  have hf := fee_le_amount (a₁ + a₂) fee_bps hbps
  unfold netAmount
  exact ⟨(f₁ + f₂) - f, by omega, by omega⟩

/-! ## Section 2b: N-Way Fee Algebra

Extending the 2-way fee results to arbitrary lists. The key insight:
ceiling subadditivity composes via list induction, giving an n-way net-amount
superadditivity with a TIGHT gap bound of at most (n − 1) units.

These are the reusable algebraic building blocks for batch verification:
any system that splits an amount into n pieces and applies ceiling fees
to each piece can use these results to bound the total fee overhead. -/

/-- N-WAY CEILING SUBADDITIVITY: splitting a sum across n ceiling divisions
    can only increase the total.
    `⌈(Σ aᵢ)/d⌉ ≤ Σ ⌈aᵢ/d⌉`

    Proof: induction on the list using 2-way `ceil_div_subadditive` at each step. -/
theorem ceilDiv_list_subadditive (amounts : List ℕ) (d : ℕ) (hd : 0 < d) :
    ceilDiv amounts.sum d ≤ (amounts.map (ceilDiv · d)).sum := by
  induction amounts with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.sum_nil]
    have : ceilDiv 0 d = 0 := by unfold ceilDiv; exact Nat.div_eq_of_lt (by omega)
    omega
  | cons a rest ih =>
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    calc ceilDiv (a + rest.sum) d
        ≤ ceilDiv a d + ceilDiv rest.sum d := ceil_div_subadditive a rest.sum d hd
      _ ≤ ceilDiv a d + (rest.map (ceilDiv · d)).sum := Nat.add_le_add_left ih _

/-- N-WAY CEILING GAP BOUND: the total overhead from n ceiling divisions
    is at most (n − 1) units.
    `Σ ⌈aᵢ/d⌉ ≤ ⌈(Σ aᵢ)/d⌉ + (n − 1)`

    This is TIGHT: n divisions can each contribute at most 1 unit of overhead,
    but the first one contributes 0 (it agrees with the single ceiling).
    Combined with `ceilDiv_list_subadditive`, this gives:
    `|Σ ⌈aᵢ/d⌉ − ⌈(Σ aᵢ)/d⌉| ≤ n − 1`

    Proof: induction on list, splitting the cons case on whether the tail is
    empty (trivial) or nonempty (the +1 from 2-way gap fits within tail length). -/
theorem ceilDiv_list_gap (amounts : List ℕ) (d : ℕ) (hd : 0 < d) :
    (amounts.map (ceilDiv · d)).sum ≤ ceilDiv amounts.sum d + (amounts.length - 1) := by
  induction amounts with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_sub_one]
    -- Target: ceilDiv a d + map_sum(rest) ≤ ceilDiv(a + rest.sum, d) + rest.length
    have h2 := ceil_div_gap_le_one a rest.sum d hd
    cases rest with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero]; omega
    | cons b rest' =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_sub_one] at ih h2 ⊢
      omega

/-- N-WAY FEE SUBADDITIVITY: splitting an order into n pieces does not decrease
    total fees.
    `computeFee(Σ aᵢ, bps) ≤ Σ computeFee(aᵢ, bps)`

    Proof: `computeFee(a, bps) = ceilDiv(a·bps, 10000)` is a ceilDiv composed
    with the additive map `a ↦ a·bps`, so n-way ceiling subadditivity applies. -/
theorem fee_list_subadditive (amounts : List ℕ) (fee_bps : ℕ) :
    computeFee amounts.sum fee_bps ≤ (amounts.map (computeFee · fee_bps)).sum := by
  unfold computeFee
  have hmul : amounts.sum * fee_bps = (amounts.map (· * fee_bps)).sum := by
    induction amounts with
    | nil => simp
    | cons a rest ih => simp [List.sum_cons, List.map_cons, Nat.add_mul, ih]
  rw [hmul]
  have hmap : (amounts.map (· * fee_bps)).map (ceilDiv · 10000) =
      amounts.map (fun a => ceilDiv (a * fee_bps) 10000) := by
    simp [List.map_map, Function.comp]
  rw [← hmap]
  exact ceilDiv_list_subadditive (amounts.map (· * fee_bps)) 10000 (by decide)

/-- N-WAY FEE GAP BOUND: the overhead from splitting fees into n pieces
    is at most (n − 1) units.
    `Σ computeFee(aᵢ, bps) ≤ computeFee(Σ aᵢ, bps) + (n − 1)` -/
theorem fee_list_gap (amounts : List ℕ) (fee_bps : ℕ) :
    (amounts.map (computeFee · fee_bps)).sum ≤
      computeFee amounts.sum fee_bps + (amounts.length - 1) := by
  unfold computeFee
  have hmul : amounts.sum * fee_bps = (amounts.map (· * fee_bps)).sum := by
    induction amounts with
    | nil => simp
    | cons a rest ih => simp [List.sum_cons, List.map_cons, Nat.add_mul, ih]
  rw [hmul]
  have hmap : (amounts.map (· * fee_bps)).map (ceilDiv · 10000) =
      amounts.map (fun a => ceilDiv (a * fee_bps) 10000) := by
    simp [List.map_map, Function.comp]
  rw [← hmap]
  have hlen : (amounts.map (· * fee_bps)).length = amounts.length := List.length_map ..
  rw [← hlen]
  exact ceilDiv_list_gap (amounts.map (· * fee_bps)) 10000 (by decide)

/-- N-WAY NET AMOUNT SUPERADDITIVITY: combining all gross inputs into one
    preserves at least as much net value as splitting into n pieces.
    `netAmount(Σ aᵢ, bps) ≥ Σ netAmount(aᵢ, bps)`

    This is the n-way generalization of the main bridge theorem
    (`net_amount_superadditive`). It follows directly from n-way fee
    subadditivity: less total fee → more total net. -/
theorem net_amount_list_superadditive (amounts : List ℕ) (fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    netAmount amounts.sum fee_bps ≥ (amounts.map (netAmount · fee_bps)).sum := by
  induction amounts with
  | nil => simp [netAmount]
  | cons a rest ih =>
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    have h2 := net_amount_superadditive a rest.sum fee_bps hbps
    have hf₁ := fee_le_amount a fee_bps hbps
    have hfr := fee_le_amount rest.sum fee_bps hbps
    omega

/-- Helper: net amount of zero gross is zero. -/
private theorem netAmount_zero (bps : ℕ) : netAmount 0 bps = 0 := by
  unfold netAmount computeFee ceilDiv; simp

/-- N-WAY NET AMOUNT GAP — TIGHT CHARACTERIZATION: the superadditivity gap
    for n-way splitting is EXACTLY between 0 and (n − 1).

    `netAmount(Σ aᵢ) = Σ netAmount(aᵢ) + gap` where `0 ≤ gap ≤ n − 1`

    Proof: the gap equals the total fee overhead `Σ fee(aᵢ) − fee(Σ aᵢ)`,
    which is bounded by n-way fee gap. Both bounds 0 and n−1 are achievable
    (see n-way witness below). -/
theorem net_amount_list_gap (amounts : List ℕ) (fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    ∃ gap : ℕ, gap ≤ amounts.length - 1 ∧
      netAmount amounts.sum fee_bps =
        (amounts.map (netAmount · fee_bps)).sum + gap := by
  -- Inline proof by induction, using 2-way gap at each step
  induction amounts with
  | nil => exact ⟨0, by omega, by simp [netAmount]⟩
  | cons a rest ih =>
    obtain ⟨g_rest, hg_bound, hg_eq⟩ := ih
    -- 2-way gap on (a, rest.sum)
    have hnet := net_amount_superadditive a rest.sum fee_bps hbps
    have hg2 := net_amount_gap_tight a rest.sum fee_bps hbps
    obtain ⟨g_2way, hg2_bound, hg2_eq⟩ := hg2
    simp only [List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_sub_one]
    refine ⟨g_2way + g_rest, ?_, ?_⟩
    · -- gap ≤ rest.length
      cases rest with
      | nil =>
        simp only [List.sum_nil, Nat.add_zero, List.length_nil] at hg2_eq hg_bound ⊢
        have h0 := netAmount_zero fee_bps; rw [h0] at hg2_eq; omega
      | cons _ _ =>
        clear hg2_eq hg_eq hnet
        simp only [List.length_cons] at hg_bound ⊢; omega
    · -- net(a + rest.sum) = net(a) + net(rest.sum) + g_2way [from hg2_eq]
      -- net(rest.sum) = map_sum + g_rest [from hg_eq]
      -- So: net(a + rest.sum) = net(a) + map_sum + g_rest + g_2way
      linarith

/-- N-way gap tightness witness:
    - Gap = 0: aligned divisions where ceiling carries don't accumulate
    - Gap = 3 (maximum for 4-way): each ceiling individually rounds up by 1
      fee(1, 2500) = ⌈2500/10000⌉ = 1, but fee(4, 2500) = ⌈10000/10000⌉ = 1
      So 4 × fee(1) = 4 while fee(4) = 1, giving gap = 4 − 1 = 3 = n − 1.
    - N-way superadditivity holds: netAmount(sum) ≥ sum of netAmounts -/
theorem witness_nway_gap :
    -- Gap = 0: 400→200+200 at 30bps: fees align
    netAmount 400 30 = netAmount 200 30 + netAmount 200 30 ∧
    -- Gap = 3 (maximum for n=4): splitting 4 into [1,1,1,1] at 2500bps
    -- fee(4, 2500) = 1, fee(1, 2500) = 1 each, 4×1 - 1 = 3
    netAmount 4 2500 = netAmount 1 2500 + netAmount 1 2500 +
      netAmount 1 2500 + netAmount 1 2500 + 3 ∧
    -- N-way subadditivity holds for 4-way split at 100bps
    netAmount 400 100 ≥
      netAmount 100 100 + netAmount 100 100 +
      netAmount 100 100 + netAmount 100 100 := by
  native_decide

/-! ## Section 3: Fee-Aware Anti-Fragmentation

The main theorem composes three results:
1. `net_amount_superadditive`: combined net input ≥ sum of individual net inputs
2. `swapOut_mono_amount`: larger input → (weakly) larger output
3. `anti_fragmentation_general`: single swap dominates sequential swap

Chain: `feeAwareOut(a₁+a₂) ≥ swapOut(x, y, n₁+n₂) ≥ out₁ + out₂`
where `n₁, n₂` are individual net amounts and the first ≥ uses monotonicity,
the second uses zero-fee anti-fragmentation.
-/

/-- Fee-aware swap output: deduct ceiling fee, then apply CPMM formula. -/
def feeAwareSwapOut (x y gross fee_bps : ℕ) : ℕ :=
  AntiFragmentation.swapOut x y (netAmount gross fee_bps)

/-- FEE-AWARE ANTI-FRAGMENTATION (Main Theorem):
    Single execution of gross amount (a₁ + a₂) through the fee pipeline produces
    at least as much output as executing a₁ then a₂ sequentially, where the
    second swap faces reserves depleted by the first.

    This is a THREE-LAYER composition:
    Layer 1 (fee): netAmount(a₁+a₂) ≥ netAmount(a₁) + netAmount(a₂)
    Layer 2 (monotonicity): swapOut(x, y, n) ≥ swapOut(x, y, n₁+n₂) when n ≥ n₁+n₂
    Layer 3 (anti-frag): swapOut(x, y, n₁+n₂) ≥ swapOut(x,y,n₁) + swapOut(x',y',n₂)

    Requires fee_bps ≤ 10000 (economically: fee rate ≤ 100%). -/
theorem fee_aware_anti_fragmentation (x y a₁ a₂ fee_bps : ℕ)
    (hbps : fee_bps ≤ 10000) :
    feeAwareSwapOut x y (a₁ + a₂) fee_bps ≥
    feeAwareSwapOut x y a₁ fee_bps +
      feeAwareSwapOut (x + netAmount a₁ fee_bps)
        (y - feeAwareSwapOut x y a₁ fee_bps) a₂ fee_bps := by
  unfold feeAwareSwapOut
  set n := netAmount (a₁ + a₂) fee_bps
  set n₁ := netAmount a₁ fee_bps
  set n₂ := netAmount a₂ fee_bps
  have hnet := net_amount_superadditive a₁ a₂ fee_bps hbps  -- n ≥ n₁ + n₂
  -- Layer 2 + 3: monotonicity + zero-fee anti-fragmentation
  have hmono := AntiFragmentation.swapOut_mono_amount x y (n₁ + n₂) n hnet
  have hanti := AntiFragmentation.anti_fragmentation_general x y n₁ n₂
  -- Chain: swapOut x y n ≥ swapOut x y (n₁+n₂) ≥ out₁ + out₂
  omega

/-- FEE-AWARE K-MONOTONICITY: K is non-decreasing after a fee-aware swap.
    This is a DELEGATION to `k_nondecreasing` from AntiFragmentation.lean —
    the fee only reduces the effective input, so the zero-fee K-monotonicity
    proof applies directly. Not counted as a substantive theorem. -/
theorem fee_aware_k_nondecreasing (x y gross fee_bps : ℕ) :
    AntiFragmentation.kValue
      (x + netAmount gross fee_bps)
      (y - feeAwareSwapOut x y gross fee_bps) ≥
    AntiFragmentation.kValue x y := by
  unfold feeAwareSwapOut
  exact AntiFragmentation.k_nondecreasing x y (netAmount gross fee_bps)

/-! ## Section 4: Fee-Aware Batch Extension

Extend to n-way splits: the batch gap for fee-aware swaps is bounded
by the zero-fee batch gap plus the fee splitting overhead. -/

/-- Fee-aware batch output: sequential fee-aware swaps through a pool. -/
def feeAwareBatchOutput (x y : ℕ) (fee_bps : ℕ) : List ℕ → ℕ
  | [] => 0
  | gross :: rest =>
      let out := feeAwareSwapOut x y gross fee_bps
      let net := netAmount gross fee_bps
      out + feeAwareBatchOutput (x + net) (y - out) fee_bps rest

/-- FEE-AWARE BATCH DOMINANCE: single fee-aware swap dominates any split.
    Proof by list induction using fee_aware_anti_fragmentation at each step. -/
theorem feeAwareBatchOutput_le_single (x y fee_bps : ℕ) (hbps : fee_bps ≤ 10000)
    (amounts : List ℕ) :
    feeAwareBatchOutput x y fee_bps amounts ≤
      feeAwareSwapOut x y amounts.sum fee_bps := by
  induction amounts generalizing x y with
  | nil => simp [feeAwareBatchOutput, feeAwareSwapOut, AntiFragmentation.swapOut]
  | cons a rest ih =>
    simp only [feeAwareBatchOutput, List.sum_cons]
    exact le_trans
      (Nat.add_le_add_left
        (ih (x + netAmount a fee_bps) (y - feeAwareSwapOut x y a fee_bps))
        (feeAwareSwapOut x y a fee_bps))
      (fee_aware_anti_fragmentation x y a rest.sum fee_bps hbps)

/-! ## Section 5: Fee-In-Pool K-Gap Ordering

In the **fee-in-pool** model (Uniswap-style), the trader sends `gross` to the pool,
the output is computed on `net = gross - fee`, and the pool retains the full `gross`
in its reserves. This gives a STRONGER K-increase than zero-fee swaps.

  K_fee = (x + gross) * (y - swapOut(x, y, net))
  K_nofee = (x + gross) * (y - swapOut(x, y, gross))
  K_fee ≥ K_nofee

This promotes optimization notes item #6 ("K_gap_fee ≥ K_gap_nofee") from
empirically verified (GPU enumeration) to formally proved.
-/

/-- Helper: net amount never exceeds gross amount. -/
private theorem net_le_gross (gross fee_bps : ℕ) : netAmount gross fee_bps ≤ gross := by
  unfold netAmount; omega

/-- FEE-IN-POOL K-GAP DECOMPOSITION: K after a fee-in-pool swap equals the
    zero-fee K-increase (on net amount) plus a fee retention bonus.

    K(x+gross, y-out) = K(x+net, y-out) + fee × (y - out)

    The first term is the K-increase from the net swap (floor-division remainder).
    The second term is the ADDITIONAL K-increase from retaining the fee in
    the input reserve — this is the pool's fee income expressed as K units.

    This is a structural accounting identity (distributive law), not an inequality. -/
theorem fee_in_pool_K_decomposition (x y gross fee_bps : ℕ) (hbps : fee_bps ≤ 10000) :
    let net := netAmount gross fee_bps
    let fee := computeFee gross fee_bps
    let out := AntiFragmentation.swapOut x y net
    AntiFragmentation.kValue (x + gross) (y - out) =
      AntiFragmentation.kValue (x + net) (y - out) + fee * (y - out) := by
  simp only [AntiFragmentation.kValue]
  have hfee := fee_le_amount gross fee_bps hbps
  -- gross = net + fee (exact decomposition, no ℕ truncation)
  have hsum : x + gross = (x + netAmount gross fee_bps) + computeFee gross fee_bps := by
    unfold netAmount; omega
  rw [hsum]
  ring

/-- FEE-IN-POOL K ORDERING: in the fee-in-pool model, K increases MORE with
    fees than without — the pool benefits from fee retention.

    K(x+gross, y-swapOut(x,y,net)) ≥ K(x+gross, y-swapOut(x,y,gross))

    Proof: net ≤ gross → swapOut(net) ≤ swapOut(gross) (monotonicity) →
    y-swapOut(gross) ≤ y-swapOut(net) → multiply by (x+gross) preserves ≤.

    This is the formal proof of optimization notes item #6, previously
    only verified by GPU enumeration on H200. -/
theorem fee_in_pool_K_ge_nofee (x y gross fee_bps : ℕ) :
    AntiFragmentation.kValue (x + gross)
      (y - AntiFragmentation.swapOut x y (netAmount gross fee_bps)) ≥
    AntiFragmentation.kValue (x + gross)
      (y - AntiFragmentation.swapOut x y gross) := by
  simp only [AntiFragmentation.kValue]
  apply Nat.mul_le_mul_left
  -- Need: y - swapOut(x,y,gross) ≤ y - swapOut(x,y,net)
  -- From: swapOut(x,y,net) ≤ swapOut(x,y,gross) (monotonicity, net ≤ gross)
  have hnet_le := net_le_gross gross fee_bps
  have hmono := AntiFragmentation.swapOut_mono_amount x y
    (netAmount gross fee_bps) gross hnet_le
  have hle_y := AntiFragmentation.swapOut_le_reserve x y gross
  omega

/-- FEE-IN-POOL EXACT K FORMULA: combining the decomposition with the zero-fee
    K-gap closed form gives the complete K accounting for fee-in-pool swaps.

    K(x+gross, y-out) = x*y + (y*net) % (x+net) + fee * (y - out)

    This is the fee-aware generalization of k_gap_exact from CPMMInvariants. -/
theorem fee_in_pool_K_exact (x y gross fee_bps : ℕ) (hbps : fee_bps ≤ 10000) :
    let net := netAmount gross fee_bps
    let fee := computeFee gross fee_bps
    let out := AntiFragmentation.swapOut x y net
    AntiFragmentation.kValue (x + gross) (y - out) =
      AntiFragmentation.kValue x y + (y * net) % (x + net) + fee * (y - out) := by
  -- Work with swapOut as abstract (don't unfold to raw division)
  simp only [AntiFragmentation.kValue]
  set net := netAmount gross fee_bps with hnet_def
  set fee := computeFee gross fee_bps with hfee_def
  set out := AntiFragmentation.swapOut x y net with hout_def
  have hfee_le := fee_le_amount gross fee_bps hbps
  -- gross = net + fee (exact ℕ decomposition, no truncation)
  have hsum : x + gross = (x + net) + fee := by
    rw [hnet_def, hfee_def]; unfold netAmount; omega
  -- K-gap closed form from swap_euclidean (keeping swapOut abstract)
  have hk_gap : (x + net) * (y - out) = x * y + (y * net) % (x + net) := by
    have hout_le : out ≤ y := AntiFragmentation.swapOut_le_reserve x y net
    -- swap_euclidean: (x + net) * out + (y * net) % (x + net) = y * net
    have hsw := AntiFragmentation.swap_euclidean x y net
    -- out * (x + net) ≤ y * net (floor property, via swapOut definition)
    have hfloor : out * (x + net) ≤ y * net := by
      rw [hout_def]; simp [AntiFragmentation.swapOut]
      exact Nat.div_mul_le_self (y * net) (x + net)
    -- Lift to ℤ where subtraction is well-behaved
    zify [hout_le] at hsw hfloor ⊢
    nlinarith [mul_sub (↑(x + net) : ℤ) (↑y : ℤ) (↑out : ℤ),
               mul_comm (↑out : ℤ) (↑(x + net) : ℤ)]
  -- Main calc: distributive law + K-gap substitution
  calc (x + gross) * (y - out)
      = ((x + net) + fee) * (y - out) := by rw [hsum]
    _ = (x + net) * (y - out) + fee * (y - out) := by ring
    _ = (x * y + (y * net) % (x + net)) + fee * (y - out) := by rw [hk_gap]

/-! ## Section 6: Non-Vacuity Witnesses

Every key theorem has concrete witnesses verified by `native_decide`. -/

/-- Ceiling algebra witnesses: subadditivity is tight (gap can be 0 or 1). -/
theorem witness_ceiling_algebra :
    -- Gap = 1: ceilDiv(3,2) + ceilDiv(3,2) = 4, ceilDiv(6,2) = 3
    ceilDiv 3 2 + ceilDiv 3 2 = ceilDiv 6 2 + 1 ∧
    -- Gap = 0: ceilDiv(4,2) + ceilDiv(4,2) = 4 = ceilDiv(8,2)
    ceilDiv 4 2 + ceilDiv 4 2 = ceilDiv 8 2 ∧
    -- Ceiling property: ceilDiv(7,3) * 3 = 9 ≥ 7
    ceilDiv 7 3 * 3 ≥ 7 ∧ ceilDiv 7 3 * 3 < 7 + 3 := by
  native_decide

/-- Fee algebra witnesses: fee splitting increases total fees by 0 or 1. -/
theorem witness_fee_algebra :
    -- Fee subadditivity: split(100+200, 30bps) ≤ fee(100,30) + fee(200,30)
    computeFee 300 30 ≤ computeFee 100 30 + computeFee 200 30 ∧
    -- Fee gap = 1: fee(1,5000) + fee(1,5000) = fee(2,5000) + 1
    computeFee 1 5000 + computeFee 1 5000 = computeFee 2 5000 + 1 ∧
    -- Net superadditivity with strict gap: net(3,3000) > net(1,3000) + net(2,3000)
    netAmount 3 3000 > netAmount 1 3000 + netAmount 2 3000 ∧
    -- Fee ≤ amount for 30bps
    computeFee 1000 30 ≤ 1000 := by
  native_decide

/-- Fee-aware anti-fragmentation witnesses across fee tiers and pool shapes. -/
theorem witness_fee_aware_anti_fragmentation :
    -- 30bps fee, symmetric pool, equal split
    feeAwareSwapOut 1000 1000 200 30 ≥
      feeAwareSwapOut 1000 1000 100 30 +
      feeAwareSwapOut (1000 + netAmount 100 30) (1000 - feeAwareSwapOut 1000 1000 100 30) 100 30 ∧
    -- 100bps fee (1%), asymmetric pool, unequal split
    feeAwareSwapOut 500 2000 300 100 ≥
      feeAwareSwapOut 500 2000 50 100 +
      feeAwareSwapOut (500 + netAmount 50 100) (2000 - feeAwareSwapOut 500 2000 50 100) 250 100 ∧
    -- 500bps fee (5%), large trade
    feeAwareSwapOut 100 100 90 500 ≥
      feeAwareSwapOut 100 100 45 500 +
      feeAwareSwapOut (100 + netAmount 45 500) (100 - feeAwareSwapOut 100 100 45 500) 45 500 ∧
    -- Batch dominance: 4-way split loses value
    feeAwareBatchOutput 1000 1000 30 [40, 60, 20, 80] ≤
      feeAwareSwapOut 1000 1000 200 30 := by
  native_decide

/-- Fee-in-pool K ordering witnesses: fees increase K more than zero-fee swaps.
    Verifies the decomposition K_fee = K_nofee_on_net + fee*(y-out) and the
    ordering K_fee_in_pool > K_nofee for concrete pool states. -/
theorem witness_fee_in_pool_K :
    let x := 1000; let y := 1000; let gross := 100; let bps := 500
    let net := netAmount gross bps
    let out := AntiFragmentation.swapOut x y net
    -- K_fee_in_pool strictly exceeds K_nofee (5% fee → outputs differ)
    AntiFragmentation.kValue (x + gross) (y - out) >
      AntiFragmentation.kValue (x + gross) (y - AntiFragmentation.swapOut x y gross) ∧
    -- K decomposition: K_fee = K_net + fee*(y-out)
    AntiFragmentation.kValue (x + gross) (y - out) =
      AntiFragmentation.kValue (x + net) (y - out) + computeFee gross bps * (y - out) ∧
    -- Fee retention bonus is positive (fee > 0 and out < y)
    computeFee gross bps * (y - out) > 0 := by
  native_decide

end FeeAwareAntiFragmentation
