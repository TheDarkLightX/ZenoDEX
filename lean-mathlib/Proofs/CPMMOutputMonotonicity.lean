import Proofs.FeeAwareAntiFragmentation
import Proofs.OppositeDirectionNoncommutativity
import Mathlib.Tactic

/-!
# CPMM Output Monotonicity and Reserve Sensitivity

**world-model promotion**: `cpmm_reserve_sensitivity` (NEW → PROVED)

**THEOREM**: The CPMM swap output function `swapOut(x, y, a) = y * a / (x + a)` is:
1. **Monotone increasing in y** (output reserve): more Y reserve → more Y output
2. **Monotone decreasing in x** (input reserve): more X reserve → less Y output
3. **Jointly monotone**: bigger numerator AND smaller denominator → bigger output

These are the fundamental **reserve sensitivity** properties of constant-product AMMs.
They underlie:
- Second-mover advantage (OppositeDirectionNoncommutativity.lean)
- Anti-fragmentation (AntiFragmentation.lean) — depleted reserves reduce subsequent output
- Fee-aware K-gap ordering (FeeAwareBatchKGap.lean) — fee retention helps the pool

## Key results (15 substantive + Mathlib integrations)

| # | Name | Grade | Statement |
|---|------|-------|-----------|
| 1 | `swapOut_mono_y` | Real | y₁ ≤ y₂ → out(x,y₁,a) ≤ out(x,y₂,a) (Nat.div_le_div_right) |
| 2 | `swapOut_anti_x` | Real | x₁ ≤ x₂ → out(x₂,y,a) ≤ out(x₁,y,a) (Nat.div_le_div_left) |
| 3 | `swapOut_strict_y` | Real | (y₂−y₁)·a ≥ x+a → strict increase (nat_div_lt_of_add_le) |
| 4 | `swapOut_joint_mono` | Real | 2-variable composition of mono_y + anti_x |
| 5 | `swapOut_shift_exact` | Real | shift = δ·a/(x+a) + carry, carry ∈ {0,1} (tight bounds) |
| 6 | `swapOut_contraction` | Real | 1-Lipschitz: shift ≤ δ (no rounding slack, exact division) |
| 7 | `swapOut_contraction_tight` | Real | Tightness: equality at x=0 proves bound is best possible |
| 8 | `swapOut_le_input` | Real | y ≤ x+a → out ≤ a (balanced-pool no-free-tokens) |
| 9 | `swapOut_approx_additive` | Real | 1-approx AddMonoidHom: f(y₁+y₂) = f(y₁)+f(y₂)+carry |
| 10 | `swapOut_shift_carry_formula` | Real | Carry = remainder-overflow indicator (exact, not ≤) |
| 11 | `swapOut_route_monotone` | Real | Route mono: a₁≤a₂ → pipeline(a₁)≤pipeline(a₂) via amount |
| 12 | `swapOut_diminishing_returns` | Real | Price impact: depleted pool gives less output |
| 13 | `swapOut_zero_iff` | Real | Complete zero characterization: out=0 ↔ y·a < x+a |
| 14 | `swapOut_sublinear` | Real | Spot price bound: out ≤ y·a/x (sublinearity) |
| 15 | `fee_reduces_output` | Real | Fee-reduced input → less output |
| — | `swapOut_monotone_y` | Lift | Mathlib `Monotone` instance (wraps mono_y) |
| — | `swapOut_antitone_x` | Lift | Mathlib `Antitone` instance (wraps anti_x) |
| — | `multiHop_monotone` | Lift | `Monotone.comp` — reserve-parameter pipeline |

## Evidence chain
- `AntiFragmentation.lean`: swapOut_mono_amount, floor_div_subadditive
- `OppositeDirectionNoncommutativity.lean`: second-mover advantage (div_mono_both)
- This file: reserve sensitivity (formal, 0 sorry)
-/

namespace CPMMOutputMonotonicity

open AntiFragmentation (swapOut kValue swapOut_le_reserve swapOut_mono_amount
  floor_div_subadditive floor_div_carry_le_one)

/-! ## Part 1: Output Reserve Monotonicity

The numerator of `swapOut(x, y, a) = y * a / (x + a)` is linear in y.
So more output reserve → more output, with the same denominator. -/

/-- RESERVE OUTPUT MONOTONICITY: increasing the output reserve (y) increases output.
    Proof: bigger numerator with same denominator. -/
theorem swapOut_mono_y (x a : ℕ) {y₁ y₂ : ℕ} (h : y₁ ≤ y₂) :
    swapOut x y₁ a ≤ swapOut x y₂ a := by
  simp only [swapOut]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right a h)

/-- Helper: for ℕ division, if a + d ≤ b and 0 < d, then a/d < b/d.
    Proof: (a+d)/d = a/d + 1, and (a+d)/d ≤ b/d. -/
private lemma nat_div_lt_of_add_le {a b d : ℕ} (h : a + d ≤ b) (hd : 0 < d) :
    a / d < b / d := by
  have step : (a + d) / d = a / d + 1 := Nat.add_div_right a hd
  have mono : (a + d) / d ≤ b / d := Nat.div_le_div_right h
  omega

/-- STRICT RESERVE MONOTONICITY: when (y₂ - y₁) * a ≥ x + a (the increase in y*a
    is at least one denominator-width), the output strictly increases.

    Proof: y₂*a ≥ y₁*a + (x+a), so y₁*a/(x+a) + 1 ≤ y₂*a/(x+a). -/
theorem swapOut_strict_y (x a : ℕ) {y₁ y₂ : ℕ}
    (hpos : 0 < x + a) (hgap : x + a ≤ (y₂ - y₁) * a) :
    swapOut x y₁ a < swapOut x y₂ a := by
  simp only [swapOut]
  have hle : y₁ ≤ y₂ := by
    by_contra hlt; push_neg at hlt
    have : y₂ - y₁ = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    rw [this, zero_mul] at hgap; omega
  apply nat_div_lt_of_add_le _ hpos
  calc y₁ * a + (x + a)
      ≤ y₁ * a + (y₂ - y₁) * a := Nat.add_le_add_left hgap _
    _ = (y₁ + (y₂ - y₁)) * a := by ring
    _ = y₂ * a := by congr 1; omega

/-! ## Part 2: Input Reserve Anti-Monotonicity

The denominator of `swapOut(x, y, a) = y * a / (x + a)` increases with x.
So more input reserve → smaller output (bigger denominator → smaller quotient). -/

/-- INPUT RESERVE ANTI-MONOTONICITY: increasing the input reserve (x) decreases output.
    Holds unconditionally (when x₁ + a = 0 both outputs are 0).
    Proof: bigger denominator with same numerator.
    Uses Nat.div_le_div_left: c ≤ b → 0 < c → a/b ≤ a/c. -/
theorem swapOut_anti_x (y a : ℕ) {x₁ x₂ : ℕ} (h : x₁ ≤ x₂) :
    swapOut x₂ y a ≤ swapOut x₁ y a := by
  simp only [swapOut]
  rcases Nat.eq_zero_or_pos (x₁ + a) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : x₁ = 0 ∧ a = 0 := by omega
    simp
  · exact Nat.div_le_div_left (by omega : x₁ + a ≤ x₂ + a) hpos

/-! ## Part 3: Joint Monotonicity

Combining both effects: bigger Y reserve AND smaller X reserve gives bigger output.
This is the two-variable version used by the second-mover advantage. -/

/-- JOINT MONOTONICITY: bigger numerator AND smaller denominator → bigger output.
    Holds unconditionally. This is the core engine behind the second-mover
    advantage. -/
theorem swapOut_joint_mono {x₁ x₂ y₁ y₂ a : ℕ}
    (hy : y₁ ≤ y₂) (hx : x₂ ≤ x₁) :
    swapOut x₁ y₁ a ≤ swapOut x₂ y₂ a := by
  calc swapOut x₁ y₁ a
      ≤ swapOut x₁ y₂ a := swapOut_mono_y x₁ a hy
    _ ≤ swapOut x₂ y₂ a := swapOut_anti_x y₂ a hx

/-! ## Part 4: Reserve Shift Bounds

How much does the output change when reserves shift? The shift is bounded
both above and below by δ*a/(x+a) with ±1 rounding slack. -/

/-- SHIFT LOWER BOUND: increasing Y by δ increases output by at least δ*a/(x+a).
    This is floor-division super-additivity applied to the numerator. -/
theorem swapOut_shift_lower (x y a δ : ℕ) :
    swapOut x y a + δ * a / (x + a) ≤ swapOut x (y + δ) a := by
  simp only [swapOut]
  have hmul : (y + δ) * a = y * a + δ * a := by ring
  rw [hmul]
  exact floor_div_subadditive (y * a) (δ * a) (x + a)

/-- SHIFT UPPER BOUND: increasing Y by δ increases output by at most δ*a/(x+a) + 1.
    The +1 accounts for the carry from combining Euclidean remainders. -/
theorem swapOut_shift_upper (x y a δ : ℕ) :
    swapOut x (y + δ) a ≤ swapOut x y a + δ * a / (x + a) + 1 := by
  simp only [swapOut]
  have hmul : (y + δ) * a = y * a + δ * a := by ring
  rw [hmul]
  have hcarry := floor_div_carry_le_one (y * a) (δ * a) (x + a)
  -- From floor_div_exact_decomposition: (a+b)/d = a/d + b/d + carry, carry ≤ 1
  have hdecomp := AntiFragmentation.floor_div_exact_decomposition
    (y * a) (δ * a) (x + a)
  omega

/-! ## Part 5: Reserve Shift Exact Decomposition

The shift bounds (Part 4) give `δ*a/(x+a) ≤ shift ≤ δ*a/(x+a) + 1`.
This part proves the EXACT decomposition: `shift = δ*a/(x+a) + carry`
where `carry ∈ {0, 1}`. This is the tightness proof. -/

/-- SHIFT EXACT DECOMPOSITION: the output shift from adding δ to Y reserve
    decomposes as `quotient + carry` where carry is exactly 0 or 1.

    This fully characterizes the rounding behavior: the continuous shift is
    `δ*a/(x+a)`, and integer division adds a carry ∈ {0, 1} from remainder
    overflow when the numerator's mod terms combine.

    Proof: existence from shift_lower (carry ≥ 0) and shift_upper (carry ≤ 1). -/
theorem swapOut_shift_exact (x y a δ : ℕ) :
    ∃ carry : ℕ, carry ≤ 1 ∧
      swapOut x (y + δ) a = swapOut x y a + δ * a / (x + a) + carry := by
  have hlower := swapOut_shift_lower x y a δ
  have hupper := swapOut_shift_upper x y a δ
  exact ⟨swapOut x (y + δ) a - (swapOut x y a + δ * a / (x + a)), by omega, by omega⟩

/-- SHIFT TIGHTNESS — carry = 0 case: for some pool configurations the carry
    vanishes (shift exactly equals the quotient). -/
theorem witness_shift_carry_zero :
    -- Pool (1000, 1000), a=100, δ=1100: carry = 0
    swapOut 1000 (1000 + 1100) 100 = swapOut 1000 1000 100 + 1100 * 100 / (1000 + 100) ∧
    -- Concrete: 190 = 90 + 100
    swapOut 1000 1000 100 = 90 ∧
    swapOut 1000 2100 100 = 190 ∧
    1100 * 100 / 1100 = 100 := by
  decide

/-- SHIFT TIGHTNESS — carry = 1 case: for some configurations the carry is 1. -/
theorem witness_shift_carry_one :
    -- Pool (1000, 1000), a=100, δ=500: carry = 1
    swapOut 1000 (1000 + 500) 100 = swapOut 1000 1000 100 + 500 * 100 / (1000 + 100) + 1 ∧
    -- Concrete: 136 = 90 + 45 + 1
    swapOut 1000 1000 100 = 90 ∧
    swapOut 1000 1500 100 = 136 ∧
    500 * 100 / 1100 = 45 := by
  decide

/-! ## Part 5b: Carry Characterization

The shift exact decomposition (Part 5) shows `shift = quotient + carry` with carry ≤ 1.
This part gives the NECESSARY AND SUFFICIENT condition for carry = 1:
the carry is 1 iff the combined remainders overflow the denominator.

  carry = 1  ⟺  (y·a) mod (x+a) + (δ·a) mod (x+a) ≥ (x+a)

This fully classifies the rounding behavior of the CPMM formula. -/

/-- CARRY CHARACTERIZATION: the carry in the shift decomposition equals
    the combined-remainder overflow indicator.

    carry = ((y*a) % d + (δ*a) % d) / d

    where d = x + a. This is 1 when the remainders sum to ≥ d, and 0 otherwise.
    Proof: from `floor_div_exact_decomposition`, which gives the carry exactly,
    then rearrange via omega. -/
theorem swapOut_shift_carry_formula (x y a δ : ℕ) :
    swapOut x (y + δ) a - (swapOut x y a + δ * a / (x + a)) =
      (y * a % (x + a) + δ * a % (x + a)) / (x + a) := by
  simp only [swapOut]
  have hmul : (y + δ) * a = y * a + δ * a := by ring
  rw [hmul]
  have hdecomp := AntiFragmentation.floor_div_exact_decomposition (y * a) (δ * a) (x + a)
  have hle := AntiFragmentation.floor_div_subadditive (y * a) (δ * a) (x + a)
  omega

/-! ## Part 5c: Output Contraction (1-Lipschitz in Y)

The shift bounds (Part 4) give `δ*a/(x+a) ≤ shift ≤ δ*a/(x+a) + 1`.
This part proves the STRONGER statement: `shift ≤ δ` (no rounding slack).
The CPMM formula is a **contraction** (1-Lipschitz) in the output reserve. -/

/-- OUTPUT CONTRACTION (1-Lipschitz in y): the output shift from adding δ to
    the Y reserve never exceeds δ. The CPMM formula CANNOT amplify reserve changes.

    This is stronger than shift_upper (which allows +1 slack) because the
    exact-division step absorbs the rounding: `δ*(x+a)/(x+a) = δ` exactly.

    Proof: `(y+δ)*a ≤ y*a + δ*(x+a)` since `a ≤ x+a`. Then
    `Nat.add_div_of_dvd_left` decomposes into `y*a/(x+a) + δ*(x+a)/(x+a)`,
    and `Nat.mul_div_cancel` gives `δ*(x+a)/(x+a) = δ`. -/
theorem swapOut_contraction (x y a δ : ℕ) :
    swapOut x (y + δ) a ≤ swapOut x y a + δ := by
  simp only [swapOut]
  by_cases hd : 0 < x + a
  · have h1 : (y + δ) * a = y * a + δ * a := by ring
    have h2 : δ * a ≤ δ * (x + a) := Nat.mul_le_mul_left δ (Nat.le_add_left a x)
    calc (y + δ) * a / (x + a)
        ≤ (y * a + δ * (x + a)) / (x + a) := Nat.div_le_div_right (by omega)
      _ = y * a / (x + a) + δ * (x + a) / (x + a) :=
          Nat.add_div_of_dvd_left (dvd_mul_left _ _)
      _ = y * a / (x + a) + δ := by rw [Nat.mul_div_cancel δ hd]
  · simp [show x + a = 0 by omega]

/-- Contraction witness: output shift never exceeds reserve shift δ. -/
theorem witness_contraction :
    -- Pool (1000, 1000), a=100, δ=500: shift = 46 ≤ 500
    swapOut 1000 (1000 + 500) 100 ≤ swapOut 1000 1000 100 + 500 ∧
    -- Tight: pool (0, 100), a=100, δ=1: shift = 1 = δ (equality achieved)
    swapOut 0 (100 + 1) 100 = swapOut 0 100 100 + 1 ∧
    -- Concrete values
    swapOut 1000 1000 100 = 90 ∧ swapOut 1000 1500 100 = 136 ∧
    swapOut 0 100 100 = 100 ∧ swapOut 0 101 100 = 101 := by
  decide

/-- CONTRACTION TIGHTNESS: when x = 0, the contraction bound is achieved as
    EQUALITY: `swapOut(0, y+δ, a) = swapOut(0, y, a) + δ`. This proves the
    bound `≤ δ` in `swapOut_contraction` is best possible.

    Proof: `swapOut(0, y, a) = y*a/a = y` by exact division, so shift = δ. -/
theorem swapOut_contraction_tight (y a δ : ℕ) (ha : 0 < a) :
    swapOut 0 (y + δ) a = swapOut 0 y a + δ := by
  simp only [swapOut, Nat.zero_add]
  rw [Nat.mul_div_cancel (y + δ) ha, Nat.mul_div_cancel y ha]

/-! ## Part 6: Output Bounded by Input (Balanced Pools) -/

/-- NO FREE TOKENS (balanced case): when y ≤ x + a, the trader gets at most
    as many tokens out as they put in.

    Proof: y * a / (x + a) ≤ (x + a) * a / (x + a) = a. -/
theorem swapOut_le_input (x y a : ℕ) (hbal : y ≤ x + a) :
    swapOut x y a ≤ a := by
  simp only [swapOut]
  calc y * a / (x + a)
      ≤ (x + a) * a / (x + a) :=
        Nat.div_le_div_right (Nat.mul_le_mul_right a hbal)
    _ = a := by
        by_cases h : x + a = 0
        · simp [h]; omega
        · rw [show (x + a) * a = a * (x + a) from Nat.mul_comm _ _]
          exact Nat.mul_div_cancel a (Nat.pos_of_ne_zero h)

/-! ## Part 7: Mathlib Algebraic Connections

The pointwise monotonicity results (Parts 1–3) lift to standard Mathlib
predicates `Monotone` and `Antitone`, and package into `OrderHom`.
This connects the CPMM formula to the order theory infrastructure:
- `Monotone.comp` chains sensitivity through multi-hop routes
- `OrderHom.comp` composes with Mathlib's order-preserving maps
- `Antitone` enables Galois connection reasoning for reserve depletion -/

/-- swapOut is Monotone in the output reserve (y): the Mathlib-standard
    form of `swapOut_mono_y`, usable with `Monotone.comp`, `Monotone.add`, etc. -/
theorem swapOut_monotone_y (x a : ℕ) : Monotone (fun y => swapOut x y a) :=
  fun _ _ h => swapOut_mono_y x a h

/-- swapOut is Antitone in the input reserve (x): larger input reserve →
    smaller output.

    Combined with `swapOut_monotone_y`, this gives: enriching the output reserve
    and depleting the input reserve both benefit the trader — the formal
    two-variable monotonicity that underlies second-mover advantage. -/
theorem swapOut_antitone_x (y a : ℕ) : Antitone (fun x => swapOut x y a) :=
  fun _ _ h => swapOut_anti_x y a h

/-- The output-reserve sensitivity as a Mathlib OrderHom (order-preserving map).
    Packages monotonicity into a first-class composable algebraic structure.

    Usage: `(swapOutOrderHom x a).comp g` chains with any other OrderHom `g`,
    and `(swapOutOrderHom x a).monotone` recovers the Monotone proof.
    This enables reasoning about multi-hop routing as OrderHom composition:
    if each hop is order-preserving, so is the pipeline. -/
def swapOutOrderHom (x a : ℕ) : ℕ →o ℕ where
  toFun := fun y => swapOut x y a
  monotone' := swapOut_monotone_y x a

/-- OrderHom computes correctly: the OrderHom agrees with raw swapOut. -/
@[simp]
theorem swapOutOrderHom_apply (x a y : ℕ) :
    swapOutOrderHom x a y = swapOut x y a := rfl

/-- NESTED OUTPUT-RESERVE MONOTONICITY: composing `swapOut` in the output-reserve
    (y) parameter preserves monotonicity end-to-end.

    Concretely: `y ↦ swapOut x₂ (swapOut x₁ y a₁) a₂` is monotone in y.
    This is `Monotone.comp` applied to two `swapOut_monotone_y` instances.

    NOTE: This composes in the y parameter only. A true multi-hop routing
    theorem (where hop₁'s output amount feeds hop₂'s input amount a) would
    require `swapOut_mono_amount` composition, which lives in AntiFragmentation. -/
theorem multiHop_monotone (x₁ a₁ x₂ a₂ : ℕ) :
    Monotone (fun y => swapOut x₂ (swapOut x₁ y a₁) a₂) :=
  (swapOut_monotone_y x₂ a₂).comp (swapOut_monotone_y x₁ a₁)

/-- Nested composition as a first-class OrderHom (wraps multiHop_monotone). -/
def multiHopOrderHom (x₁ a₁ x₂ a₂ : ℕ) : ℕ →o ℕ :=
  (swapOutOrderHom x₂ a₂).comp (swapOutOrderHom x₁ a₁)

/-- Multi-hop composition agrees with sequential swapOut application. -/
@[simp]
theorem multiHopOrderHom_apply (x₁ a₁ x₂ a₂ y : ℕ) :
    multiHopOrderHom x₁ a₁ x₂ a₂ y = swapOut x₂ (swapOut x₁ y a₁) a₂ := rfl

/-- Multi-hop monotonicity witness: 3-pool pipeline, varying initial Y reserve. -/
theorem witness_multihop :
    -- Pipeline: pool₁(500,·,100) → pool₂(800,·,50)
    -- More initial Y → more final output
    swapOut 800 (swapOut 500 1000 100) 50 <
      swapOut 800 (swapOut 500 2000 100) 50 ∧
    -- Concrete: 1000→166→9 vs 2000→333→19
    swapOut 500 1000 100 = 166 ∧
    swapOut 800 166 50 = 9 ∧
    swapOut 500 2000 100 = 333 ∧
    swapOut 800 333 50 = 19 := by
  decide

/-! ## Part 7b: Approximate Additivity (Hyers–Ulam Stability)

Over ℚ, the map `y ↦ y·a/(x+a)` is an exact AddMonoidHom (linear in y).
Over ℤ/ℕ, floor division perturbs additivity by at most 1 unit. This
makes `swapOut` a **1-approximate AddMonoidHom** in the sense of Hyers–Ulam
stability theory: the integer formula satisfies the homomorphism equation
`f(y₁ + y₂) = f(y₁) + f(y₂)` up to a carry ∈ {0, 1}.

This characterization is the algebraic dual of anti-fragmentation:
- Anti-fragmentation (AntiFragmentation.lean): `f(y₁+y₂) ≥ f(y₁) + f(y₂)` (superadditive)
- Carry bound: `f(y₁+y₂) ≤ f(y₁) + f(y₂) + 1`
- Together: `f(y₁+y₂) = f(y₁) + f(y₂) + carry`, `carry ∈ {0, 1}` -/

/-- APPROXIMATE ADDITIVITY: swapOut is a 1-approximate AddMonoidHom in y.

    swapOut(x, y₁+y₂, a) = swapOut(x, y₁, a) + swapOut(x, y₂, a) + carry

    where carry ∈ {0, 1}. This fully characterizes the rounding behavior:
    the CPMM integer formula deviates from the exact rational formula
    by at most 1 unit per addition, which is optimal (tight at both 0 and 1).

    Proof: unfold swapOut, factor the numerator `(y₁+y₂)*a = y₁*a + y₂*a`,
    then combine `floor_div_subadditive` (lower bound) with
    `floor_div_carry_le_one` (upper bound) to extract the carry. -/
theorem swapOut_approx_additive (x y₁ y₂ a : ℕ) :
    ∃ carry : ℕ, carry ≤ 1 ∧
      swapOut x (y₁ + y₂) a = swapOut x y₁ a + swapOut x y₂ a + carry := by
  simp only [swapOut]
  have hmul : (y₁ + y₂) * a = y₁ * a + y₂ * a := by ring
  rw [hmul]
  -- floor_div_exact_decomposition: a/d + b/d + carry = (a+b)/d where carry = (a%d + b%d)/d
  have hdecomp := AntiFragmentation.floor_div_exact_decomposition
    (y₁ * a) (y₂ * a) (x + a)
  -- floor_div_carry_le_one: carry ≤ 1
  have hcarry := floor_div_carry_le_one (y₁ * a) (y₂ * a) (x + a)
  exact ⟨(y₁ * a % (x + a) + y₂ * a % (x + a)) / (x + a), hcarry, hdecomp⟩

/-- Approximate additivity tightness: both carry=0 and carry=1 are achievable,
    so the bound is optimal (the CPMM formula is as close to additive as possible). -/
theorem witness_approx_additive_tight :
    -- carry = 0: swapOut(1000, 500+500, 100) = 45 + 45 = 90
    swapOut 1000 (500 + 500) 100 = swapOut 1000 500 100 + swapOut 1000 500 100 ∧
    -- carry = 1: swapOut(1000, 501+501, 100) = 45 + 45 + 1 = 91
    swapOut 1000 (501 + 501) 100 = swapOut 1000 501 100 + swapOut 1000 501 100 + 1 ∧
    -- concrete values
    swapOut 1000 500 100 = 45 ∧
    swapOut 1000 1000 100 = 90 ∧   -- 45 + 45 = 90, carry = 0
    swapOut 1000 501 100 = 45 ∧
    swapOut 1000 1002 100 = 91 := by -- 45 + 45 + 1 = 91, carry = 1
  decide

/-! ## Part 7c: True Routing Monotonicity (Trade Amount)

The `multiHop_monotone` theorem (Part 7) composes through the reserve parameter y.
TRUE routing composes through the TRADE AMOUNT: hop₁'s output becomes hop₂'s
input amount `a`. This requires `swapOut_mono_amount` from AntiFragmentation,
which gives monotonicity in the amount parameter.

This is the routing theorem that matters for DEX engineering: if a trader
sends more input, they get more output through any multi-hop route. -/

/-- TRUE ROUTING MONOTONICITY: the multi-hop swap pipeline
    `a ↦ swapOut(x₂, y₂, swapOut(x₁, y₁, a))` is monotone in the trade
    amount `a`, matching how real DEX routes work.

    Proof: compose two `swapOut_mono_amount` instances — hop₁ maps
    a₁ ≤ a₂ to out₁ ≤ out₂, then hop₂ maps out₁ ≤ out₂ to final₁ ≤ final₂. -/
theorem swapOut_route_monotone (x₁ y₁ x₂ y₂ : ℕ) :
    Monotone (fun a => swapOut x₂ y₂ (swapOut x₁ y₁ a)) :=
  fun _ _ h => swapOut_mono_amount x₂ y₂ _ _ (swapOut_mono_amount x₁ y₁ _ _ h)

/-- Routing as a first-class Mathlib OrderHom.
    `(routeOrderHom x₁ y₁ x₂ y₂).comp (routeOrderHom x₃ y₃ x₄ y₄)` chains
    four-hop routes via OrderHom composition. -/
def routeOrderHom (x₁ y₁ x₂ y₂ : ℕ) : ℕ →o ℕ where
  toFun := fun a => swapOut x₂ y₂ (swapOut x₁ y₁ a)
  monotone' := swapOut_route_monotone x₁ y₁ x₂ y₂

/-- Routing monotonicity witness: larger trade → larger output through 2-hop route. -/
theorem witness_route_mono :
    -- Larger input → larger output through pool₁(1000,1000) → pool₂(800,1000)
    swapOut 800 1000 (swapOut 1000 1000 50) <
      swapOut 800 1000 (swapOut 1000 1000 100) ∧
    swapOut 1000 1000 50 = 47 ∧
    swapOut 800 1000 47 = 55 ∧
    swapOut 1000 1000 100 = 90 ∧
    swapOut 800 1000 90 = 101 := by
  decide

/-! ## Part 7d: Diminishing Returns

The fundamental economic property of CPMM: each additional unit of input
produces less output than the previous one, because the pool becomes more
imbalanced after each trade. Formally: trading against a DEPLETED pool
gives less output than trading against the original pool. -/

/-- DIMINISHING RETURNS: trading against a pool that has already processed
    a swap gives LESS output than trading against the original pool.

    swapOut(x + a₁, y − out₁, a₂) ≤ swapOut(x, y, a₂)

    The depleted pool has higher x (by a₁) and lower y (by out₁),
    both of which reduce the output. This is the formal statement of
    "price impact" — the pool worsens for the trader after each trade.

    Proof: compose `swapOut_joint_mono` with the natural bounds
    `y − out₁ ≤ y` (numerator shrinks) and `x ≤ x + a₁` (denominator grows). -/
theorem swapOut_diminishing_returns (x y a₁ a₂ : ℕ) :
    swapOut (x + a₁) (y - swapOut x y a₁) a₂ ≤ swapOut x y a₂ :=
  swapOut_joint_mono (Nat.sub_le _ _) (Nat.le_add_right _ _)

/-- ROUTE OUTPUT CEILING: two-hop output is bounded by the second pool's
    output at the first pool's full reserve.

    swapOut(x₂, y₂, swapOut(x₁, y₁, a)) ≤ swapOut(x₂, y₂, y₁)

    Since hop₁ output ≤ y₁ (from `swapOut_le_reserve`), and `swapOut` is
    monotone in the trade amount, the second hop operates on at most y₁.
    This gives a POOL-PARAMETER-INDEPENDENT ceiling on route output:
    no matter how large the trade, the two-hop pipeline is bounded
    by the second pool's response to the first pool's full reserve. -/
theorem swapOut_compose_upper (x₁ y₁ x₂ y₂ a : ℕ) :
    swapOut x₂ y₂ (swapOut x₁ y₁ a) ≤ swapOut x₂ y₂ y₁ := by
  exact swapOut_mono_amount x₂ y₂ _ y₁ (swapOut_le_reserve x₁ y₁ a)

/-- Diminishing returns witness: pool (1000,1000), trade 100 then 100.
    Second trade gets 75 (< 90 from first trade). -/
theorem witness_diminishing_returns :
    let x := 1000; let y := 1000; let a := 100
    let out₁ := swapOut x y a
    -- First trade: 90 tokens
    out₁ = 90 ∧
    -- Second trade on depleted pool: only 75 tokens (< 90)
    swapOut (x + a) (y - out₁) a = 75 ∧
    -- Formally: second < first
    swapOut (x + a) (y - out₁) a < swapOut x y a := by
  decide

/-- Route ceiling witness: 2-hop route bounded by single-pool output. -/
theorem witness_compose_upper :
    -- Route: pool₁(1000,1000,a=200) → pool₂(500,2000,out₁)
    swapOut 500 2000 (swapOut 1000 1000 200) ≤ swapOut 500 2000 1000 ∧
    -- Concrete: route gives 460 ≤ 1333
    swapOut 1000 1000 200 = 166 ∧
    swapOut 500 2000 166 = 498 ∧
    swapOut 500 2000 1000 = 1333 := by
  decide

/-! ## Part 7e: Swap Output Positivity

When is the CPMM output non-zero? Exactly when the numerator `y * a` is at
least the denominator `x + a` — i.e., when `y ≥ (x + a) / a ≈ x/a + 1`.
Below this threshold, floor division kills the output entirely. -/

/-- SWAP OUTPUT POSITIVE: the output is positive when `y * a ≥ x + a`.
    This condition is SHARP: `y * a < x + a` implies `swapOut = 0`.

    The condition means: the "fair value" of the trade `y * a` must be at
    least one denominator-width. For balanced pools (y ≈ x), this holds
    whenever `a ≥ 2`. For imbalanced pools (y ≪ x), larger trades are needed. -/
theorem swapOut_pos (x y a : ℕ) (ha : 0 < a) (h : x + a ≤ y * a) :
    0 < swapOut x y a := by
  simp only [swapOut]
  exact Nat.div_pos h (by omega)

/-- SWAP OUTPUT ZERO: when `y * a < x + a`, the output is zero.
    This is the negation of the positivity criterion — floor division
    kills sub-denominator numerators entirely. -/
theorem swapOut_eq_zero (x y a : ℕ) (h : y * a < x + a) :
    swapOut x y a = 0 := by
  simp only [swapOut]
  exact Nat.div_eq_of_lt h

/-- Positivity threshold witness: the criterion is tight at the boundary. -/
theorem witness_positivity_threshold :
    -- Below threshold: y*a = 1*1 = 1 < 101 = x+a → output = 0
    swapOut 100 1 1 = 0 ∧
    -- At threshold: y*a = 2*1 = 2 < 101 → still 0
    swapOut 100 2 1 = 0 ∧
    -- Above threshold: y*a = 101*1 = 101 ≥ 101 → output = 1
    swapOut 100 101 1 = 1 ∧
    -- Larger trade: y*a = 10*100 = 1000 ≥ 110 → output = 9
    0 < swapOut 100 10 100 := by
  decide

/-- ZERO OUTPUT CHARACTERIZATION (iff): `swapOut = 0` precisely when the
    numerator `y*a` is sub-denominator. This combines `swapOut_eq_zero` (←)
    and `swapOut_pos` (→ by contrapositive) into a single biconditional.

    Classifies "dust trades": small trades against large pools that produce
    zero output because floor division kills sub-denominator numerators. -/
theorem swapOut_zero_iff (x y a : ℕ) (ha : 0 < a) :
    swapOut x y a = 0 ↔ y * a < x + a := by
  simp only [swapOut]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have := Nat.div_pos hlt (by omega : 0 < x + a)
    omega
  · exact Nat.div_eq_of_lt

/-- Zero characterization witness: boundary is exact. -/
theorem witness_zero_iff :
    -- Below: 100*1 = 100 < 1001 → output = 0
    swapOut 1000 100 1 = 0 ∧
    -- At boundary: 1001*1 = 1001 ≥ 1001 → output > 0
    0 < swapOut 1000 1001 1 ∧
    -- Just below: 10*10 = 100 < 110 → output = 0
    swapOut 100 10 10 = 0 ∧
    -- At boundary: 11*10 = 110 ≥ 110 → output > 0
    0 < swapOut 100 11 10 := by
  decide

/-! ## Part 7f: Sublinearity (Spot Price Bound)

Over ℚ, `y·a/(x+a) ≤ y·a/x` always (since x+a ≥ x). This means the swap
output is bounded by the "spot price" `y/x` times the trade size `a`.
The spot price bound is the best linear approximation of the output function
and is useful for gas estimation and slippage prediction. -/

/-- SUBLINEARITY: the swap output is at most the spot-price estimate `y·a/x`.
    The output-per-unit never exceeds the spot exchange rate.

    Proof: `x ≤ x + a` so `(y·a)/(x+a) ≤ (y·a)/x` by `Nat.div_le_div_left`. -/
theorem swapOut_sublinear (x y a : ℕ) (hx : 0 < x) :
    swapOut x y a ≤ y * a / x := by
  simp only [swapOut]
  exact Nat.div_le_div_left (by omega : x ≤ x + a) hx

/-- Sublinearity witness: output always below spot price estimate. -/
theorem witness_sublinear :
    -- Pool (1000, 2000), a=100: output 181, spot estimate 200
    swapOut 1000 2000 100 = 181 ∧ 2000 * 100 / 1000 = 200 ∧
    swapOut 1000 2000 100 ≤ 2000 * 100 / 1000 ∧
    -- Large trade: pool (10, 1000), a=100: output 909, spot estimate 10000
    swapOut 10 1000 100 = 909 ∧ 1000 * 100 / 10 = 10000 ∧
    -- Small trade: pool (1000, 1000), a=1: output 0, spot estimate 1
    swapOut 1000 1000 1 = 0 ∧ 1000 * 1 / 1000 = 1 := by
  decide

/-! ## Part 8: Fee Reduces Output -/

/-- FEE REDUCES OUTPUT: swapOut with fee-reduced input gives less output.
    Since netAmount(a, bps) ≤ a, fee-aware output ≤ zero-fee output. -/
theorem fee_reduces_output (x y a fee_bps : ℕ) :
    swapOut x y (CPMMInvariants.netAmount a fee_bps) ≤ swapOut x y a := by
  apply swapOut_mono_amount
  simp only [CPMMInvariants.netAmount]
  exact Nat.sub_le _ _

/-! ## Part 9: Non-Vacuity Witnesses -/

/-- Reserve monotonicity witness: various pools, swap 100. -/
theorem witness_reserve_mono :
    -- More Y reserve → more output
    swapOut 1000 1000 100 < swapOut 1000 2000 100 ∧
    -- More X reserve → less output
    swapOut 2000 1000 100 < swapOut 1000 1000 100 ∧
    -- Joint: enriched Y AND depleted X → even more output
    swapOut 2000 500 100 < swapOut 500 2000 100 ∧
    -- Concrete values
    swapOut 1000 1000 100 = 90 ∧
    swapOut 1000 2000 100 = 181 ∧
    swapOut 2000 1000 100 = 47 ∧
    swapOut 500 2000 100 = 333 := by
  decide

/-- Shift bound witness: pool (1000, 1000), a=100, δ=500. -/
theorem witness_shift_bound :
    let x := 1000; let y := 1000; let a := 100; let δ := 500
    -- Lower bound: shift ≥ δ*a/(x+a)
    swapOut x y a + δ * a / (x + a) ≤ swapOut x (y + δ) a ∧
    -- Upper bound: shift ≤ δ*a/(x+a) + 1
    swapOut x (y + δ) a ≤ swapOut x y a + δ * a / (x + a) + 1 ∧
    -- Concrete: output 90 → 136, bound 45 ≤ 46 ≤ 46
    swapOut x y a = 90 ∧
    swapOut x (y + δ) a = 136 ∧
    δ * a / (x + a) = 45 := by
  decide

/-- Fee reduces output witness: pool (1000, 1000), gross=100, 500bps fee. -/
theorem witness_fee_reduces :
    let x := 1000; let y := 1000; let gross := 100; let bps := 500
    swapOut x y (CPMMInvariants.netAmount gross bps) <
      swapOut x y gross ∧
    swapOut x y gross = 90 ∧
    swapOut x y (CPMMInvariants.netAmount gross bps) = 86 := by
  decide

/-- Balanced pool no-free-tokens witness. -/
theorem witness_no_free_tokens :
    -- Balanced: output ≤ input
    swapOut 1000 1000 100 ≤ 100 ∧
    swapOut 1000 1000 100 = 90 ∧
    -- Unbalanced: output can exceed input
    swapOut 1 1000000 1 = 500000 ∧
    500000 > 1 := by
  decide

/-- Strict monotonicity witness: gap ≥ denominator triggers strict increase. -/
theorem witness_strict :
    -- Pool (100, 100) → (100, 200), swap 10. Gap = 100*10 = 1000 ≥ 110.
    swapOut 100 100 10 < swapOut 100 200 10 ∧
    swapOut 100 100 10 = 9 ∧
    swapOut 100 200 10 = 18 := by
  decide

end CPMMOutputMonotonicity
