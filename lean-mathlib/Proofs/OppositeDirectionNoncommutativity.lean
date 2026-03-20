import Proofs.AntiFragmentation
import Mathlib.Tactic

/-!
# Opposite-Direction Noncommutativity

**ShapeForge promotion**: `noncommutative_ordering` (TESTED_ONLY → PROVED)

## What this file proves

### Generic theorems (universally quantified, no concrete witnesses)

1. **Second-mover advantage (weak)**: Executing a swap AFTER the opposite direction
   gives at least as much output, because the pool has been enriched with the
   desired token. (`second_mover_advantage_Y`, `second_mover_advantage_X`)

2. **Strict second-mover advantage**: Under a denominator-width condition
   (`b·a ≥ x+a`), the advantage is STRICT — the second mover gets strictly
   more output. (`second_mover_strict_Y`, `second_mover_strict_X`)

3. **Exact K-gap formulas**: K-increase from any swap is exactly the Euclidean
   remainder. These compose additively over two-swap paths, and the K-gap
   DIFFERENCE between paths depends only on cross-remainder terms from
   intermediate states. (`swapXtoY_K_exact`, `swapYtoX_K_exact`,
   `path1_K_gap_exact`, `path2_K_gap_exact`, `K_gap_path_difference`)

### Concrete witnesses (noncommutativity of outputs, states, and K values)

Strict noncommutativity of outputs and pool states is proved via `native_decide`
on concrete pool configurations. These witnesses demonstrate that the weak
second-mover advantage is generically STRICT for non-dust trades.

## Key results (15 substantive)

| # | Name | Grade | Statement |
|---|------|-------|-----------|
| 1 | `second_mover_advantage_Y` | Real | outY ≥ when done after YtoX (div_mono_both chain) |
| 2 | `second_mover_advantage_X` | Real | outX ≥ when done after XtoY (symmetric) |
| 3 | `second_mover_strict_Y` | Real | outY strictly > under denominator-width gap |
| 4 | `second_mover_strict_X` | Real | outX strictly > under denominator-width gap |
| 5 | `swapXtoY_K_exact` | Real | K = K₀ + (y·a) mod (x+a) via zify/nlinarith |
| 6 | `swapYtoX_K_exact` | Real | K = K₀ + (x·b) mod (y+b) via zify/nlinarith |
| 7 | `path1_K_gap_exact` | Real | Two-swap K decomposes as sum of remainders |
| 8 | `K_gap_path_difference` | Real | K-difference = cross-remainder difference (ℕ) |
| 9 | `K_gap_path_difference_Z` | Real | Signed ℤ K-gap: ↑K₁-↑K₂ = ↑r₁-↑r₂ (exact_mod_cast) |
| 10 | `first_swap_K_dominance_iff` | Real | K-ordering iff remainder dominance (single swap) |
| 11 | `path_rx_strict_order` | Real | Reserve ordering from strict second-mover advantage |
| 12 | `generic_path_noncommutativity` | Real | ∀-quantified path noncommutativity (no witnesses) |
| 13 | `path_K_ordering_iff` | Real | Complete iff: K(path₁)≥K(path₂) ⟺ rem-sum ordering |
| 14 | `path_K_noncommutative_iff` | Real | Complete iff: K(path₁)≠K(path₂) ⟺ rem-sums differ |
| 15 | `path2_K_gap_exact` | Real | Two-swap K composition (YtoX first) |

## Evidence chain
- Python: `experimental/math_discovery_pipeline/src/swap_commutativity.py`
- Shape notes: section 2.1.E (opposite-direction commutativity quarantine)
- This file: Lean proof (formal, 0 sorry)
-/

namespace OppositeDirectionNoncommutativity

/-! ## Part 1: Bidirectional Swap Model -/

/-- A two-token pool state. -/
structure Pool where
  x : ℕ  -- reserve of token X
  y : ℕ  -- reserve of token Y
  deriving Repr, DecidableEq

/-- Product invariant K = x * y. -/
def Pool.K (p : Pool) : ℕ := AntiFragmentation.kValue p.x p.y

/-- XtoY swap output: how much Y the trader receives. -/
def outY (p : Pool) (a : ℕ) : ℕ := AntiFragmentation.swapOut p.x p.y a

/-- YtoX swap output: how much X the trader receives. -/
def outX (p : Pool) (b : ℕ) : ℕ := AntiFragmentation.swapOut p.y p.x b

/-- XtoY swap: trader sends `a` of token X, receives Y output. -/
def swapXtoY (p : Pool) (a : ℕ) : Pool :=
  ⟨p.x + a, p.y - outY p a⟩

/-- YtoX swap: trader sends `b` of token Y, receives X output. -/
def swapYtoX (p : Pool) (b : ℕ) : Pool :=
  ⟨p.x - outX p b, p.y + b⟩

/-! ## Part 2: Two-Swap Paths -/

/-- Path 1: XtoY first, then YtoX. -/
def path_XY_YX (p : Pool) (a b : ℕ) : ℕ × ℕ × Pool :=
  let p₁ := swapXtoY p a
  (outY p a, outX p₁ b, swapYtoX p₁ b)

/-- Path 2: YtoX first, then XtoY. -/
def path_YX_XY (p : Pool) (a b : ℕ) : ℕ × ℕ × Pool :=
  let p₁ := swapYtoX p b
  (outX p b, outY p₁ a, swapXtoY p₁ a)

/-! ## Part 3: Second-Mover Advantage

Executing a swap second (after the opposite direction) gives at least as much
output, because the pool has been enriched with the token you want to extract.

Proof technique: two-step chain via Nat.div_le_div_right (bigger numerator)
and Nat.div_le_div_left (smaller denominator).
-/

/-- Helper: if n₁ ≥ n₂ and d₁ ≤ d₂ with 0 < d₁, then n₁/d₁ ≥ n₂/d₂.
    Chains: n₂/d₂ ≤ n₁/d₂ (bigger numerator) ≤ n₁/d₁ (smaller denominator). -/
private lemma div_mono_both {n₁ n₂ d₁ d₂ : ℕ}
    (hn : n₂ ≤ n₁) (hd : d₁ ≤ d₂) (hpos : 0 < d₁) :
    n₂ / d₂ ≤ n₁ / d₁ := by
  calc n₂ / d₂ ≤ n₁ / d₂ := Nat.div_le_div_right hn
    _ ≤ n₁ / d₁ := Nat.div_le_div_left hd hpos

/-- SECOND-MOVER ADVANTAGE (Y output): executing XtoY after YtoX gives at least
    as much Y output as executing XtoY first.

    After YtoX(b), the Y reserve is y+b ≥ y → bigger numerator.
    The X reserve is x-outX ≤ x → smaller denominator.
    Both effects benefit the XtoY trader. -/
theorem second_mover_advantage_Y (p : Pool) (a b : ℕ) :
    outY (swapYtoX p b) a ≥ outY p a := by
  simp only [outY, swapYtoX, outX, AntiFragmentation.swapOut]
  -- Goal: (p.y+b)*a / (p.x - (p.x*b)/(p.y+b) + a) ≥ p.y*a / (p.x+a)
  by_cases ha : a = 0
  · simp [ha]
  · apply div_mono_both
    · -- Numerator: (p.y + b) * a ≥ p.y * a
      exact Nat.mul_le_mul_right a (Nat.le_add_right p.y b)
    · -- Denominator: p.x - outX + a ≤ p.x + a
      have : p.x - p.x * b / (p.y + b) ≤ p.x := Nat.sub_le _ _
      omega
    · -- Positivity: a ≠ 0 so a ≥ 1, and Nat.sub ≥ 0
      have := Nat.pos_of_ne_zero ha
      omega

/-- SECOND-MOVER ADVANTAGE (X output): executing YtoX after XtoY gives at least
    as much X output as executing YtoX first.

    Symmetric: after XtoY(a), X reserve is x+a ≥ x → bigger numerator,
    and Y reserve is y-outY ≤ y → smaller denominator. -/
theorem second_mover_advantage_X (p : Pool) (a b : ℕ) :
    outX (swapXtoY p a) b ≥ outX p b := by
  simp only [outX, swapXtoY, outY, AntiFragmentation.swapOut]
  by_cases hb : b = 0
  · simp [hb]
  · apply div_mono_both
    · exact Nat.mul_le_mul_right b (Nat.le_add_right p.x a)
    · have : p.y - p.y * a / (p.x + a) ≤ p.y := Nat.sub_le _ _
      omega
    · have := Nat.pos_of_ne_zero hb
      omega

/-! ## Part 3b: Strict Second-Mover Advantage

The weak advantage (Part 3) uses `≥`. Under a **denominator-width gap** condition
— the product `b·a` must be at least one pool width `(x+a)` — the advantage
becomes STRICT. The proof chains two independent monotonicity steps:

1. `nat_div_lt_of_add_le`: strict numerator increase at fixed denominator
2. `Nat.div_le_div_left`: weakly smaller denominator amplifies the quotient

Condition `b·a ≥ x+a` is tight: trades below this threshold can be zeroed
by floor division (e.g., x=10, a=3, b=1: b·a=3 < 13=x+a gives equal output). -/

/-- Helper: if a + d ≤ b and 0 < d, then a/d < b/d.
    Proof: (a+d)/d = a/d + 1, and (a+d)/d ≤ b/d. -/
private lemma nat_div_lt_of_add_le {a b d : ℕ} (h : a + d ≤ b) (hd : 0 < d) :
    a / d < b / d := by
  have step : (a + d) / d = a / d + 1 := Nat.add_div_right a hd
  have mono : (a + d) / d ≤ b / d := Nat.div_le_div_right h
  omega

/-- STRICT SECOND-MOVER ADVANTAGE (Y output): when the Y-input `b` satisfies
    `b·a ≥ x+a` (one denominator-width of numerator increase), executing XtoY
    after YtoX gives STRICTLY more Y output than executing XtoY first.

    Proof architecture (3-step chain):
    1. Numerator gap: `(y+b)·a ≥ y·a + (x+a)` (from `b·a ≥ x+a`)
    2. Strict at fixed denom: `y·a/(x+a) < (y+b)·a/(x+a)` [`nat_div_lt_of_add_le`]
    3. Smaller denom amplifies: `(y+b)·a/(x+a) ≤ (y+b)·a/(x−outX+a)` [`div_le_div_left`]

    The condition is sufficient (not necessary): `b·a < x+a` can yield equal
    quotients when floor division absorbs the numerator gap. -/
theorem second_mover_strict_Y (p : Pool) (a b : ℕ)
    (ha : 0 < a) (hgap : p.x + a ≤ b * a) :
    outY p a < outY (swapYtoX p b) a := by
  simp only [outY, swapYtoX, outX, AntiFragmentation.swapOut]
  have hpos : 0 < p.x + a := by omega
  -- Step 1: numerator gap of one denominator-width
  have hnum : p.y * a + (p.x + a) ≤ (p.y + b) * a := by nlinarith
  -- Step 2: strict increase at fixed denominator (x+a)
  have hfixed := nat_div_lt_of_add_le hnum hpos
  -- Step 3: denominator after YtoX ≤ original (Nat.sub truncates ≤ minuend)
  have hsub : p.x - p.x * b / (p.y + b) ≤ p.x := Nat.sub_le _ _
  have hdsub : p.x - p.x * b / (p.y + b) + a ≤ p.x + a := Nat.add_le_add_right hsub a
  have hdpos : 0 < p.x - p.x * b / (p.y + b) + a := by omega
  -- Chain: strict at (x+a), then ≤ at smaller divisor via div_mono_both
  have hstep : (p.y + b) * a / (p.x + a) ≤
      (p.y + b) * a / (p.x - p.x * b / (p.y + b) + a) :=
    div_mono_both le_rfl hdsub hdpos
  exact lt_of_lt_of_le hfixed hstep

/-- STRICT SECOND-MOVER ADVANTAGE (X output): symmetric to `second_mover_strict_Y`.
    When `a·b ≥ y+b`, executing YtoX after XtoY gives strictly more X output. -/
theorem second_mover_strict_X (p : Pool) (a b : ℕ)
    (hb : 0 < b) (hgap : p.y + b ≤ a * b) :
    outX p b < outX (swapXtoY p a) b := by
  simp only [outX, swapXtoY, outY, AntiFragmentation.swapOut]
  have hpos : 0 < p.y + b := by omega
  have hnum : p.x * b + (p.y + b) ≤ (p.x + a) * b := by nlinarith
  have hfixed := nat_div_lt_of_add_le hnum hpos
  have hsub : p.y - p.y * a / (p.x + a) ≤ p.y := Nat.sub_le _ _
  have hdsub : p.y - p.y * a / (p.x + a) + b ≤ p.y + b := Nat.add_le_add_right hsub b
  have hdpos : 0 < p.y - p.y * a / (p.x + a) + b := by omega
  have hstep : (p.x + a) * b / (p.y + b) ≤
      (p.x + a) * b / (p.y - p.y * a / (p.x + a) + b) :=
    div_mono_both le_rfl hdsub hdpos
  exact lt_of_lt_of_le hfixed hstep

/-- Strict conditions witness: for pool (1000,1000) with a=100, b=80,
    both denominator-width conditions hold, confirming the strict theorems
    apply to the canonical test configuration. -/
theorem witness_strict_conditions :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    -- b·a = 8000 ≥ 1100 = x+a ✓
    p.x + a ≤ b * a ∧
    -- a·b = 8000 ≥ 1080 = y+b ✓
    p.y + b ≤ a * b ∧
    -- Edge case: a=3, b=1, p=(10,10) does NOT satisfy (3 < 13)
    ¬(10 + 3 ≤ 1 * 3) := by
  native_decide

/-! ## Part 4: Exact K-Gap Formulas

The K-increase from a swap is EXACTLY the Euclidean remainder of the
numerator divided by the denominator. This connects the Pool structure
to the underlying integer arithmetic of constant-product AMMs.

  K(XtoY(p, a)) = K(p) + (y*a) mod (x+a)
  K(YtoX(p, b)) = K(p) + (x*b) mod (y+b)

These are derived (not assumed) from `swap_euclidean` via `zify`/`nlinarith`. -/

/-- K-GAP EXACT FORMULA (XtoY): the K-increase from an XtoY swap equals
    the Euclidean remainder `(y*a) mod (x+a)`.

    Proof architecture:
    1. swap_euclidean: `(x+a) * out + (y*a)%(x+a) = y*a`
    2. Rearrange: `(x+a) * out = y*a - rem`
    3. Expand: `(x+a)*(y-out) = x*y + a*y - y*a + rem = x*y + rem`
    4. The lift to ℤ (via zify) handles the ℕ subtraction safely. -/
theorem swapXtoY_K_exact (p : Pool) (a : ℕ) :
    (swapXtoY p a).K = p.K + (p.y * a) % (p.x + a) := by
  unfold Pool.K swapXtoY outY AntiFragmentation.kValue
  simp only [AntiFragmentation.swapOut]
  -- Goal: (p.x + a) * (p.y - p.y * a / (p.x + a)) = p.x * p.y + (p.y * a) % (p.x + a)
  have hout : p.y * a / (p.x + a) ≤ p.y :=
    AntiFragmentation.swapOut_le_reserve p.x p.y a
  have hsw := AntiFragmentation.swap_euclidean p.x p.y a
  simp only [AntiFragmentation.swapOut] at hsw
  -- hsw: (p.x + a) * (p.y * a / (p.x + a)) + (p.y * a) % (p.x + a) = p.y * a
  zify [hout] at hsw ⊢
  nlinarith [mul_sub (↑(p.x + a) : ℤ) (↑p.y : ℤ) (↑(p.y * a / (p.x + a)) : ℤ),
             mul_comm (↑(p.y * a / (p.x + a)) : ℤ) (↑(p.x + a) : ℤ)]

/-- K-GAP EXACT FORMULA (YtoX): the K-increase from a YtoX swap equals
    the Euclidean remainder `(x*b) mod (y+b)`.

    Symmetric to swapXtoY_K_exact with x↔y swapped, plus a final
    commutativity step `(y+b)*(x - outX) = (x - outX)*(y+b)`. -/
theorem swapYtoX_K_exact (p : Pool) (b : ℕ) :
    (swapYtoX p b).K = p.K + (p.x * b) % (p.y + b) := by
  unfold Pool.K swapYtoX outX AntiFragmentation.kValue
  simp only [AntiFragmentation.swapOut]
  have hout : p.x * b / (p.y + b) ≤ p.x :=
    AntiFragmentation.swapOut_le_reserve p.y p.x b
  have hsw := AntiFragmentation.swap_euclidean p.y p.x b
  simp only [AntiFragmentation.swapOut] at hsw
  zify [hout] at hsw ⊢
  nlinarith [mul_sub (↑(p.y + b) : ℤ) (↑p.x : ℤ) (↑(p.x * b / (p.y + b)) : ℤ),
             mul_comm (↑(p.x * b / (p.y + b)) : ℤ) (↑(p.y + b) : ℤ),
             mul_comm (↑p.x : ℤ) (↑p.y : ℤ)]

/-- K-MONOTONICITY (XtoY): immediate corollary of the exact formula. -/
theorem swapXtoY_K_mono (p : Pool) (a : ℕ) :
    (swapXtoY p a).K ≥ p.K := by
  rw [swapXtoY_K_exact]; omega

/-- K-MONOTONICITY (YtoX): immediate corollary of the exact formula. -/
theorem swapYtoX_K_mono (p : Pool) (b : ℕ) :
    (swapYtoX p b).K ≥ p.K := by
  rw [swapYtoX_K_exact]; omega

/-- K is non-decreasing along Path 1 (XtoY then YtoX). -/
theorem path1_K_mono (p : Pool) (a b : ℕ) :
    (path_XY_YX p a b).2.2.K ≥ p.K := by
  simp only [path_XY_YX]
  exact le_trans (swapXtoY_K_mono p a) (swapYtoX_K_mono (swapXtoY p a) b)

/-- K is non-decreasing along Path 2 (YtoX then XtoY). -/
theorem path2_K_mono (p : Pool) (a b : ℕ) :
    (path_YX_XY p a b).2.2.K ≥ p.K := by
  simp only [path_YX_XY]
  exact le_trans (swapYtoX_K_mono p b) (swapXtoY_K_mono (swapYtoX p b) a)

/-! ## Part 4b: K-Gap Ordering Classification

The K-gap between paths depends on Euclidean remainders at intermediate states.
This section provides ordering criteria: conditions under which one path
accumulates more K than the other after the FIRST swap. -/

/-- FIRST-SWAP K DOMINANCE: after one swap, the path whose swap produces a
    larger Euclidean remainder has higher K.

    If `(y*a) mod (x+a) ≥ (x*b) mod (y+b)`, then K after XtoY ≥ K after YtoX.
    This is DERIVED from the exact K-gap formulas — it connects pool-level
    K ordering to a COMPUTABLE number-theoretic criterion (compare two mods).

    Usage: to determine which single swap benefits the pool more, just
    compare `(y*a) % (x+a)` vs `(x*b) % (y+b)` — no full K computation needed. -/
theorem first_swap_K_dominance (p : Pool) (a b : ℕ)
    (h : (p.x * b) % (p.y + b) ≤ (p.y * a) % (p.x + a)) :
    (swapYtoX p b).K ≤ (swapXtoY p a).K := by
  rw [swapXtoY_K_exact, swapYtoX_K_exact]; omega

/-- Symmetric: XtoY first has higher K iff its remainder dominates. -/
theorem first_swap_K_dominance_iff (p : Pool) (a b : ℕ) :
    (swapYtoX p b).K ≤ (swapXtoY p a).K ↔
    (p.x * b) % (p.y + b) ≤ (p.y * a) % (p.x + a) := by
  constructor
  · intro h; rw [swapXtoY_K_exact, swapYtoX_K_exact] at h; omega
  · exact first_swap_K_dominance p a b

/-! ## Part 4c: Generic Strict Noncommutativity

Under denominator-width conditions, the two paths produce DIFFERENT final pools.
This is the generic version of the concrete `witness_final_state_differs`. -/

/-- STRICT RESERVE ORDERING: under the denominator-width condition for the
    X-direction, Path 1 (XtoY first) ends with STRICTLY LESS input reserve
    than Path 2 (YtoX first).

    Proof: In Path 1, the X trader goes second and extracts MORE from enriched
    reserves (`second_mover_strict_X`). Both paths add the same `a` to rx,
    so more X-extraction in Path 1 → less final rx.

    This is the structural mechanism behind noncommutativity: second-mover
    advantage asymmetrically depletes reserves depending on path order. -/
theorem path_rx_strict_order (p : Pool) (a b : ℕ)
    (hb : 0 < b) (hgap : p.y + b ≤ a * b) :
    (path_XY_YX p a b).2.2.x < (path_YX_XY p a b).2.2.x := by
  simp only [path_XY_YX, path_YX_XY, swapXtoY, swapYtoX, outX, outY]
  have hstrict := second_mover_strict_X p a b hb hgap
  simp only [outX, swapXtoY, outY] at hstrict
  have hle := AntiFragmentation.swapOut_le_reserve p.y p.x b
  have hle' := AntiFragmentation.swapOut_le_reserve
    (p.y - AntiFragmentation.swapOut p.x p.y a) (p.x + a) b
  omega

/-- GENERIC STRICT PATH NONCOMMUTATIVITY: under denominator-width conditions
    for the X-direction, the final pool states from the two paths ALWAYS differ.

    Immediate from `path_rx_strict_order`: different rx ⇒ different pools.
    No concrete witnesses needed — this is a universally quantified theorem. -/
theorem generic_path_noncommutativity (p : Pool) (a b : ℕ)
    (hb : 0 < b) (hgap : p.y + b ≤ a * b) :
    (path_XY_YX p a b).2.2 ≠ (path_YX_XY p a b).2.2 := by
  intro heq
  have hrx := path_rx_strict_order p a b hb hgap
  rw [heq] at hrx
  exact Nat.lt_irrefl _ hrx

/-! ## Part 5: K-Gap Composition (Two-Swap Paths)

The exact K-gap formulas (Part 4) compose: the total K-increase along a
two-swap path decomposes as the SUM of individual Euclidean remainders.
Each remainder is independently computable from the pool state at its step.

This is the algebraic insight: for a two-step path, the total K equals
`K₀ + rem₁ + rem₂` where each remainder depends on the intermediate pool state.
The noncommutativity manifests as different intermediate states producing
different remainders, even though each step's K-gap formula is the same. -/

/-- PATH 1 K-GAP COMPOSITION: the total K-increase along XtoY→YtoX decomposes
    as the sum of two Euclidean remainders at their respective pool states.

    K(XtoY→YtoX(p, a, b)) = K(p) + (y·a) mod (x+a) + (x'·b) mod (y'+b)

    where (x', y') = (x+a, y−outY) is the intermediate state after XtoY.
    Each term is the "rounding bonus" the pool earns from integer division. -/
theorem path1_K_gap_exact (p : Pool) (a b : ℕ) :
    (path_XY_YX p a b).2.2.K = p.K + (p.y * a) % (p.x + a) +
      ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b) := by
  simp only [path_XY_YX]
  have h1 := swapXtoY_K_exact p a
  have h2 := swapYtoX_K_exact (swapXtoY p a) b
  omega

/-- PATH 2 K-GAP COMPOSITION: symmetric to path 1, with YtoX first.

    K(YtoX→XtoY(p, a, b)) = K(p) + (x·b) mod (y+b) + (y'·a) mod (x'+a)

    where (x', y') = (x−outX, y+b) is the intermediate state after YtoX. -/
theorem path2_K_gap_exact (p : Pool) (a b : ℕ) :
    (path_YX_XY p a b).2.2.K = p.K + (p.x * b) % (p.y + b) +
      ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a) := by
  simp only [path_YX_XY]
  have h1 := swapYtoX_K_exact p b
  have h2 := swapXtoY_K_exact (swapYtoX p b) a
  omega

/-- K-GAP PATH DIFFERENCE (ℕ truncated): the K-difference between the two paths
    via truncated ℕ subtraction.

    NOTE: This uses ℕ subtraction, which truncates to 0 when path2.K > path1.K.
    For the SIGNED (ℤ) difference that correctly handles both directions, see
    `K_gap_path_difference_Z`.

    The base K cancels because both paths start from the same pool. Only the
    CROSS-TERMS (which depend on intermediate pool states) contribute. -/
theorem K_gap_path_difference (p : Pool) (a b : ℕ) :
    (path_XY_YX p a b).2.2.K - (path_YX_XY p a b).2.2.K =
      ((p.y * a) % (p.x + a) + ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b)) -
      ((p.x * b) % (p.y + b) + ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a)) := by
  have h1 := path1_K_gap_exact p a b
  have h2 := path2_K_gap_exact p a b
  omega

/-- K-GAP PATH DIFFERENCE (signed ℤ): the TRUE signed K-difference, without
    ℕ truncation. Over ℤ, the difference equals the difference of cross-remainder
    sums from intermediate pool states.

    This is the algebraically clean version of `K_gap_path_difference`:
      ↑K₁ - ↑K₂ = (↑rem1_a + ↑rem1_b) - (↑rem2_a + ↑rem2_b)
    The base K cancels exactly because both paths start from the same pool.

    For a witness showing the sign can go either way, see `witness_K_gap_both_signs`. -/
theorem K_gap_path_difference_Z (p : Pool) (a b : ℕ) :
    (↑(path_XY_YX p a b).2.2.K : ℤ) - ↑(path_YX_XY p a b).2.2.K =
      (↑((p.y * a) % (p.x + a)) : ℤ) +
      ↑(((swapXtoY p a).x * b) % ((swapXtoY p a).y + b)) -
      ↑((p.x * b) % (p.y + b)) -
      ↑(((swapYtoX p b).y * a) % ((swapYtoX p b).x + a)) := by
  have h1 := path1_K_gap_exact p a b
  have h2 := path2_K_gap_exact p a b
  have h1z : (↑(path_XY_YX p a b).2.2.K : ℤ) =
      ↑p.K + ↑((p.y * a) % (p.x + a)) +
      ↑(((swapXtoY p a).x * b) % ((swapXtoY p a).y + b)) := by exact_mod_cast h1
  have h2z : (↑(path_YX_XY p a b).2.2.K : ℤ) =
      ↑p.K + ↑((p.x * b) % (p.y + b)) +
      ↑(((swapYtoX p b).y * a) % ((swapYtoX p b).x + a)) := by exact_mod_cast h2
  linarith

/-- COMPLETE PATH K-ORDERING (iff): Path 1 (XtoY first) accumulates at least
    as much K as Path 2 iff its cross-remainder sum dominates.

    K(path₁) ≥ K(path₂) ⟺ rem₁_XtoY + rem₁_YtoX ≥ rem₂_YtoX + rem₂_XtoY

    This reduces the K-ordering question to a COMPUTABLE number-theoretic
    criterion: evaluate 4 Euclidean remainders at intermediate states.
    The base K cancels (both paths start from the same pool), so only
    the cross-terms from intermediate states matter.

    Usage: to maximize protocol K-accumulation from two opposite-direction
    trades, evaluate both remainder sums and execute the dominant path first. -/
theorem path_K_ordering_iff (p : Pool) (a b : ℕ) :
    (path_XY_YX p a b).2.2.K ≥ (path_YX_XY p a b).2.2.K ↔
    (p.y * a) % (p.x + a) + ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b) ≥
      (p.x * b) % (p.y + b) + ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a) := by
  have h1 := path1_K_gap_exact p a b
  have h2 := path2_K_gap_exact p a b
  constructor <;> intro h <;> omega

/-- PATH K-NONCOMMUTATIVITY CRITERION (iff): the two paths have different K
    iff their cross-remainder sums differ.

    K(path₁) ≠ K(path₂) ⟺ rem-sum₁ ≠ rem-sum₂

    Combined with `path_K_ordering_iff`, this fully classifies the
    K-relationship between paths: either equal (when remainder sums
    coincide, typically at dust-level trades) or strictly ordered
    (with the direction determined by which sum dominates). -/
theorem path_K_noncommutative_iff (p : Pool) (a b : ℕ) :
    (path_XY_YX p a b).2.2.K ≠ (path_YX_XY p a b).2.2.K ↔
    (p.y * a) % (p.x + a) + ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b) ≠
      (p.x * b) % (p.y + b) + ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a) := by
  have h1 := path1_K_gap_exact p a b
  have h2 := path2_K_gap_exact p a b
  constructor
  · intro hk hr; exact hk (by omega)
  · intro hr hk; exact hr (by omega)

/-- K-GAP COMPOSITION WITNESS: concrete verification that the composition
    formula correctly predicts total K-increase for both paths. -/
theorem witness_K_gap_composition :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    -- Path 1 exact decomposition
    (path_XY_YX p a b).2.2.K =
      p.K + (p.y * a) % (p.x + a) + ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b) ∧
    -- Path 2 exact decomposition
    (path_YX_XY p a b).2.2.K =
      p.K + (p.x * b) % (p.y + b) + ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a) ∧
    -- The remainders are different (noncommutativity source)
    (p.y * a) % (p.x + a) + ((swapXtoY p a).x * b) % ((swapXtoY p a).y + b) ≠
      (p.x * b) % (p.y + b) + ((swapYtoX p b).y * a) % ((swapYtoX p b).x + a) := by
  native_decide

/-! ## Part 6: Concrete Noncommutativity Witnesses -/

/-- STRICT NONCOMMUTATIVITY WITNESS: For pool (1000, 1000) with swaps a=100, b=80.

    Path 1 (XtoY first): outY₁ = 90, then outX₁ = 88
    Path 2 (YtoX first): outX₂ = 74, then outY₂ = 105

    The second execution in each path sees enriched reserves → larger output. -/
theorem witness_strict_noncommutativity :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    -- Y output increases when done second
    outY p a < outY (swapYtoX p b) a ∧
    -- X output increases when done second
    outX p b < outX (swapXtoY p a) b ∧
    -- Concrete values
    outY p a = 90 ∧
    outY (swapYtoX p b) a = 105 ∧
    outX p b = 74 ∧
    outX (swapXtoY p a) b = 88 := by
  native_decide

/-- FINAL STATE DIFFERS: the final pool states are different between the two paths. -/
theorem witness_final_state_differs :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    (path_XY_YX p a b).2.2 ≠ (path_YX_XY p a b).2.2 ∧
    (path_XY_YX p a b).2.2 = Pool.mk 1012 990 ∧
    (path_YX_XY p a b).2.2 = Pool.mk 1026 975 := by
  native_decide

/-- K VALUES DIFFER: both paths increase K, but by different amounts. -/
theorem witness_K_values_differ :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    (path_XY_YX p a b).2.2.K > p.K ∧
    (path_YX_XY p a b).2.2.K > p.K ∧
    (path_XY_YX p a b).2.2.K ≠ (path_YX_XY p a b).2.2.K ∧
    p.K = 1000000 ∧
    (path_XY_YX p a b).2.2.K = 1001880 ∧
    (path_YX_XY p a b).2.2.K = 1000350 := by
  native_decide

/-- TOTAL OUTPUT DIFFERS: combined trader surplus differs between paths.
    Path 1: 90 + 88 = 178. Path 2: 74 + 105 = 179. -/
theorem witness_total_output_differs :
    let p : Pool := ⟨1000, 1000⟩
    let a := 100; let b := 80
    let (out_y₁, out_x₁, _) := path_XY_YX p a b
    let (out_x₂, out_y₂, _) := path_YX_XY p a b
    out_y₁ + out_x₁ ≠ out_x₂ + out_y₂ ∧
    out_y₁ + out_x₁ = 178 ∧
    out_x₂ + out_y₂ = 179 := by
  native_decide

/-- ASYMMETRIC POOL WITNESS: noncommutativity holds for unbalanced pools. -/
theorem witness_asymmetric_pool :
    let p : Pool := ⟨500, 2000⟩
    let a := 50; let b := 100
    outY p a < outY (swapYtoX p b) a ∧
    outX p b < outX (swapXtoY p a) b ∧
    (path_XY_YX p a b).2.2 ≠ (path_YX_XY p a b).2.2 := by
  native_decide

/-- SMALL AMOUNTS WITNESS: noncommutativity holds even for tiny swaps. -/
theorem witness_small_amounts :
    let p : Pool := ⟨100, 100⟩
    let a := 1; let b := 1
    (path_XY_YX p a b).2.2 ≠ (path_YX_XY p a b).2.2 := by
  native_decide

/-- SIGNED K-GAP WITNESS: neither path universally dominates — the sign of
    ΔK depends on pool asymmetry.
    - Symmetric (1000,1000): XtoY-first accumulates more K
    - Asymmetric (100,10000): YtoX-first accumulates more K -/
theorem witness_K_gap_both_signs :
    (path_XY_YX ⟨1000, 1000⟩ 100 80).2.2.K > (path_YX_XY ⟨1000, 1000⟩ 100 80).2.2.K ∧
    (path_YX_XY ⟨100, 10000⟩ 5 500).2.2.K > (path_XY_YX ⟨100, 10000⟩ 5 500).2.2.K := by
  native_decide

/-! ## Part 7: ShapeForge Quarantine Rule

The results above formally justify the shape quarantine from
SHAPE_OPTIMIZATION_NOTES section 2.1.E:

  OppositeDirection(s1, s2) → ¬AssumeCommutes(s1, s2)

### Conservatively safe orderings

1. **Same-direction same-pool**: Commutative up to rounding gap ∈ {0,1}
   (proved in AntiFragmentation.lean)
2. **Different-pool any-direction**: Commutative (pools are independent)
3. **Opposite-direction same-pool**: NOT commutative (this file)

The safe canonicalization rule: only reorder within class (1) or (2).
Never reorder across (3).
-/

end OppositeDirectionNoncommutativity
