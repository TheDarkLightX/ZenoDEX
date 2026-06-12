import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Rounding Error Bound for Multi-Hop Floor Division

Bounds for accumulated rounding error when floor division outputs
are composed across multiple hops. Applicable to CPMM multi-hop
routes and any system where floor-division outputs feed into subsequent
floor-division computations.

The bounds are proved on ABSTRACT gap sequences satisfying recurrence
conditions; the caller must verify that their concrete system satisfies
these conditions (see `single_hop_gap` for the per-hop CPMM floor bound).

## Two Error Models

1. **Conservative model** (`gap(k+1) ≤ gap(k) + 2`):
   Each hop adds at most 2 units of error (1 from Lipschitz propagation
   of previous error + 1 from new floor division). Yields `gap(k) ≤ 2k - 1`.

2. **Tight Lipschitz model** (`gap(k+1) ≤ gap(k) + 1`):
   When the composition function has Lipschitz constant ≤ 1, rounding
   errors do not amplify. Yields `gap(k) ≤ k`.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `floor_div_remainder` | Core | `n - (n/d)*d < d` (floor division remainder bound) |
| 2 | `rounding_gap_bound` | Main | Abstract recurrence → gap(k) ≤ 2k-1 by induction |
| 3 | `rounding_gap_lipschitz_bound` | Main | Abstract recurrence → gap(k) ≤ k by induction |
| 4 | `rounding_gap_bound_general` | Main | Parameterized: step C → gap(k) ≤ C·k-(C-1) |
| 5 | `conservative_is_general_C2` | Unification | Conservative bound = C=2 specialization |
| 6 | `lipschitz_is_general_C1` | Unification | Lipschitz bound = C=1 specialization |
| 7 | `general_bound_tight` | Tightness | ∃ sequence achieving C·k-(C-1) for any C≥1 |
| 8 | `lipschitz_implies_conservative` | Corollary | Lipschitz model implies conservative model |

## Scope limitation

The main theorems (`rounding_gap_bound`, `rounding_gap_lipschitz_bound`)
prove bounds on abstract sequences satisfying recurrence hypotheses.
They do NOT define CPMM route composition or derive the recurrence
from CPMM floor division properties. That bridge is a separate obligation.
-/

namespace Proofs
namespace RoundingErrorBound

/-! ### Layer 1: Floor Division Remainder Bound -/

/-- Floor division remainder is strictly less than the divisor.
    This is the fundamental source of per-hop rounding error:
    `n - (n / d) * d < d` for any `0 < d`. -/
theorem floor_div_remainder (n d : Nat) (hd : 0 < d) :
    n - (n / d) * d < d := by
  have hmod := Nat.mod_lt n hd
  have hcomm : d * (n / d) = (n / d) * d := Nat.mul_comm d (n / d)
  have hdef := Nat.mod_def n d
  omega

/-! ### Layer 2: Single-Hop CPMM Rounding Error -/

/-- For a single CPMM hop with output `y * dx / d`, the remainder
    `y * dx - (y * dx / d) * d` is strictly less than `d`.
    This bounds the raw rounding error in numerator units. -/
theorem single_hop_gap (y dx d : Nat) (hd : 0 < d) :
    y * dx - (y * dx / d) * d < d :=
  floor_div_remainder (y * dx) d hd

/-- The floor division output is at most the numerator divided by the
    denominator: `(n / d) * d <= n`. This ensures floor never over-reports. -/
theorem floor_div_no_overcount (n d : Nat) (_hd : 0 < d) :
    (n / d) * d ≤ n := by
  have hcomm : d * (n / d) = (n / d) * d := Nat.mul_comm d (n / d)
  have := Nat.div_mul_le_self n d
  omega

/-! ### Layer 3: Conservative Multi-Hop Bound (2k - 1) -/

/-- **Main theorem (conservative model).**
    Given a gap sequence `g` where:
    - `g 1 ≤ 1` (single hop: floor division contributes at most 1 unit),
    - `g (k+1) ≤ g k + 2` (each additional hop adds at most 2 units of error),

    the total rounding gap satisfies `g k ≤ 2k - 1`.

    Proved by induction on `k` with case split at k=1. -/
theorem rounding_gap_bound (g : Nat -> Int)
    (h_base : g 1 ≤ 1)
    (h_step : forall k, 1 ≤ k -> g (k + 1) ≤ g k + 2)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ 2 * ↑k - 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- k = 1: g 1 ≤ 1 = 2*1 - 1
      simpa using h_base
    | succ m =>
      -- k = m + 2: use IH on m + 1 and step from m + 1 to m + 2
      have hm : 1 ≤ m + 1 := by omega
      have ih_applied := ih hm
      have hstep := h_step (m + 1) hm
      push_cast at *
      omega

/-! ### Layer 3': Tight Lipschitz Multi-Hop Bound (k) -/

/-- **Main theorem (Lipschitz model).**
    When the composition function has Lipschitz constant ≤ 1 (so rounding
    errors do not amplify across hops), each hop contributes at most 1 unit
    of new error from floor division, giving the tighter bound `g k ≤ k`.

    Preconditions:
    - `g 1 ≤ 1` (single hop),
    - `g (k+1) ≤ g k + 1` (Lipschitz-1 propagation + floor division).

    The caller must verify that their concrete system satisfies the Lipschitz
    condition. For CPMM, this holds when input ≤ pool reserve (not proved here). -/
theorem rounding_gap_lipschitz_bound (g : Nat -> Int)
    (h_base : g 1 ≤ 1)
    (h_step : forall k, 1 ≤ k -> g (k + 1) ≤ g k + 1)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ ↑k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa using h_base
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      have ih_applied := ih hm
      have hstep := h_step (m + 1) hm
      push_cast at *
      omega

/-- The conservative bound dominates the Lipschitz bound:
    `k <= 2k - 1` for all `k >= 1`. This confirms that the Lipschitz
    model is strictly tighter. -/
theorem lipschitz_bound_le_conservative (k : Nat) (hk : 1 ≤ k) :
    (↑k : Int) ≤ 2 * ↑k - 1 := by
  omega

/-! ### Layer 4: Non-Vacuity Witnesses -/

/-- The gap sequence `g(k) = 2k - 1` satisfies the base case. -/
theorem witness_conservative_base :
    let g : Nat -> Int := fun k => 2 * ↑k - 1
    g 1 = 1 := by norm_num

/-- The gap sequence `g(k) = 2k - 1` satisfies the step condition
    with equality, showing the conservative bound is tight. -/
theorem witness_conservative_step :
    let g : Nat -> Int := fun k => 2 * ↑k - 1
    forall k, 1 ≤ k -> g (k + 1) = g k + 2 := by
  intro _g_unused k _hk
  show 2 * (↑(k + 1) : Int) - 1 = 2 * (↑k : Int) - 1 + 2
  push_cast
  ring

/-- Concrete witness: the abstract sequence g(k) = 2k-1 gives g(3) = 5.
    This demonstrates the conservative bound is achievable (for the abstract model). -/
theorem witness_3hop_gap :
    let g : Nat -> Int := fun k => 2 * ↑k - 1
    g 3 = 5 := by norm_num

/-- The Lipschitz gap sequence `g(k) = k` satisfies the base case. -/
theorem witness_lipschitz_base :
    let g : Nat -> Int := fun k => ↑k
    g 1 = 1 := by norm_num

/-- The Lipschitz gap sequence `g(k) = k` satisfies the step condition
    with equality, showing the Lipschitz bound is tight. -/
theorem witness_lipschitz_step :
    let g : Nat -> Int := fun k => ↑k
    forall k, 1 ≤ k -> g (k + 1) = g k + 1 := by
  intro _g_unused k _hk
  show (↑(k + 1) : Int) = ↑k + 1
  push_cast
  ring

/-- Concrete witness: floor division remainder can equal `d - 1`,
    showing the per-hop bound is tight. `6 mod 7 = 6 = 7 - 1`. -/
theorem witness_remainder_tight :
    6 - (6 / 7) * 7 = 6 := by native_decide

/-- Concrete witness: floor division remainder is 0 when `d` divides `n`.
    `14 mod 7 = 0`. Shows the gap can be zero (best case). -/
theorem witness_remainder_zero :
    14 - (14 / 7) * 7 = 0 := by native_decide

/-- Concrete floor division example: 200*50 / 150 = 66.
    Shows `single_hop_gap` applied to CPMM-like parameters. -/
theorem witness_cpmm_hop :
    200 * 50 / 150 = 66 := by native_decide

/-! ### Composition: Connecting Floor Division to Gap Sequences -/

/-- Any gap sequence satisfying the conservative step condition also
    satisfies the Lipschitz step condition when the Lipschitz constant
    is at most 1. This lemma shows how to weaken the step hypothesis
    when moving from the tight to the conservative model. -/
theorem step_weaken (g : Nat -> Int)
    (h_lip : forall k, 1 ≤ k -> g (k + 1) ≤ g k + 1) :
    forall k, 1 ≤ k -> g (k + 1) ≤ g k + 2 := by
  intro k hk
  have := h_lip k hk
  omega

/-- Corollary: the Lipschitz bound implies the conservative bound. -/
theorem lipschitz_implies_conservative (g : Nat -> Int)
    (h_base : g 1 ≤ 1)
    (h_step : forall k, 1 ≤ k -> g (k + 1) ≤ g k + 1)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ 2 * ↑k - 1 := by
  exact rounding_gap_bound g h_base (step_weaken g h_step) k hk

/-! ### Layer 5: Generalized Bound (parameterized by step constant C)

The conservative (C=2) and Lipschitz (C=1) bounds are both instances of
a single parameterized family: if each hop adds at most C units of error,
then `g(k) ≤ C·k - (C-1)`. This unification reveals the *linear* structure
of rounding error propagation. -/

/-- **GENERALIZED ROUNDING GAP BOUND**: for any step constant `C ≥ 1`,
    if `g(1) ≤ 1` and `g(k+1) ≤ g(k) + C` for all `k ≥ 1`,
    then `g(k) ≤ C·k - (C-1)`.

    The conservative model (C=2, bound 2k-1) and Lipschitz model (C=1, bound k)
    are both special cases. -/
theorem rounding_gap_bound_general (g : Nat → Int) (C : Int)
    (_hC : 1 ≤ C)
    (h_base : g 1 ≤ 1)
    (h_step : ∀ k, 1 ≤ k → g (k + 1) ≤ g k + C)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ C * ↑k - (C - 1) := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- g 1 ≤ 1 = C*1 - (C-1) = 1
      have : C * (1 : Int) - (C - 1) = 1 := by ring
      push_cast at *; linarith
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      have ih_applied := ih hm
      have hstep := h_step (m + 1) hm
      push_cast at *
      -- C*(m+2) - (C-1) = C*(m+1) - (C-1) + C
      nlinarith

/-- The conservative bound `2k-1` is the `C=2` specialization of the
    generalized bound `C·k - (C-1)`. -/
theorem conservative_is_general_C2 (g : Nat → Int)
    (h_base : g 1 ≤ 1)
    (h_step : ∀ k, 1 ≤ k → g (k + 1) ≤ g k + 2)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ 2 * ↑k - 1 :=
  rounding_gap_bound_general g 2 (by omega) h_base h_step k hk

/-- The Lipschitz bound `k` is the `C=1` specialization of the
    generalized bound `C·k - (C-1) = 1·k - 0 = k`. -/
theorem lipschitz_is_general_C1 (g : Nat → Int)
    (h_base : g 1 ≤ 1)
    (h_step : ∀ k, 1 ≤ k → g (k + 1) ≤ g k + 1)
    (k : Nat) (hk : 1 ≤ k) :
    g k ≤ ↑k := by
  have h := rounding_gap_bound_general g 1 (by omega) h_base h_step k hk
  push_cast at *; omega

/-! ### Tightness: bounds are optimal -/

/-- **GENERALIZED BOUND IS TIGHT**: for any step constant `C ≥ 1`, the
    sequence `g(k) = C·k - (C-1)` satisfies the recurrence and achieves
    the bound with equality. This subsumes both conservative and Lipschitz
    tightness as `C=2` and `C=1` cases. -/
theorem general_bound_tight (C : Int) (_hC : 1 ≤ C) (k : Nat) (_hk : 1 ≤ k) :
    ∃ g : Nat → Int,
      g 1 ≤ 1 ∧
      (∀ j, 1 ≤ j → g (j + 1) ≤ g j + C) ∧
      g k = C * ↑k - (C - 1) := by
  refine ⟨fun j => C * ↑j - (C - 1), ?_, ?_, by ring⟩
  · dsimp only; push_cast; nlinarith
  · intro j _; dsimp only; push_cast; nlinarith

/-- **CONSERVATIVE BOUND IS TIGHT**: There exists a gap sequence satisfying
    the recurrence that achieves `g(k) = 2k - 1` (the upper bound) for any k.
    This proves the bound `2k - 1` cannot be improved. -/
theorem conservative_bound_tight (k : Nat) (hk : 1 ≤ k) :
    ∃ g : Nat → Int,
      g 1 ≤ 1 ∧
      (∀ j, 1 ≤ j → g (j + 1) ≤ g j + 2) ∧
      g k = 2 * ↑k - 1 :=
  general_bound_tight 2 (by omega) k hk

/-- **LIPSCHITZ BOUND IS TIGHT**: There exists a gap sequence satisfying
    the Lipschitz recurrence that achieves `g(k) = k` for any k.
    This proves the bound `k` cannot be improved. -/
theorem lipschitz_bound_tight (k : Nat) (hk : 1 ≤ k) :
    ∃ g : Nat → Int,
      g 1 ≤ 1 ∧
      (∀ j, 1 ≤ j → g (j + 1) ≤ g j + 1) ∧
      g k = ↑k := by
  obtain ⟨g, hb, hs, hval⟩ := general_bound_tight 1 (by omega) k hk
  exact ⟨g, hb, hs, by push_cast at *; omega⟩

/-- **LIPSCHITZ STRICTLY BETTER**: For k ≥ 2, the Lipschitz bound k is
    strictly smaller than the conservative bound 2k - 1. -/
theorem lipschitz_strictly_better (k : Nat) (hk : 2 ≤ k) :
    (↑k : Int) < 2 * ↑k - 1 := by
  omega

/-! ## CPMM hop bridge for the Lipschitz recurrence

`rounding_gap_lipschitz_bound` leaves the per-hop Lipschitz condition as a
caller obligation.  `cpmm_hop_lipschitz` discharges it for CPMM hops with
`y ≤ x` (output reserve at most input reserve, i.e. spot price at most one
output unit per input unit): perturbing the input of such a hop by `g`
perturbs the floored output by at most `g`, so per-hop gap growth is at
most one rounding unit and the `g(k) ≤ k` route bound applies on routes
made of such hops — halving the conservative `2k − 1` bound.

`witness_hop_not_lipschitz` shows the price bound is necessary: on an
imbalanced pool (`y > x`) a one-unit input difference can move the floored
output by hundreds of units, so the Lipschitz route bound must NOT be
assumed on up-price hops. -/

/-- CPMM floored output is 1-Lipschitz in the input on hops with `y ≤ x`:
    `y·(z+g)/(x+z+g) ≤ y·z/(x+z) + g`. -/
theorem cpmm_hop_lipschitz (x y z g : Nat) (hx : 0 < x) (hyx : y ≤ x) :
    y * (z + g) / (x + (z + g)) ≤ y * z / (x + z) + g := by
  have hxz : 0 < x + z := by omega
  have hxzg : 0 < x + (z + g) := by omega
  have hq : y * z < (y * z / (x + z) + 1) * (x + z) := by
    have hdm : (x + z) * (y * z / (x + z)) + y * z % (x + z) = y * z :=
      Nat.div_add_mod (y * z) (x + z)
    have hmod : y * z % (x + z) < x + z := Nat.mod_lt _ hxz
    have hexp : (y * z / (x + z) + 1) * (x + z)
        = (x + z) * (y * z / (x + z)) + (x + z) := by ring
    linarith
  have hgoal : y * (z + g) < (y * z / (x + z) + g + 1) * (x + (z + g)) := by
    have hexp : (y * z / (x + z) + g + 1) * (x + (z + g))
        = (y * z / (x + z) + 1) * (x + z) + (y * z / (x + z) + 1) * g
          + g * (x + (z + g)) := by ring
    have hsplit : y * (z + g) = y * z + y * g := by ring
    have hgx : y * g ≤ g * (x + (z + g)) := by
      calc y * g ≤ (x + (z + g)) * g := Nat.mul_le_mul_right g (by omega)
        _ = g * (x + (z + g)) := Nat.mul_comm _ _
    omega
  have hlt := (Nat.div_lt_iff_lt_mul hxzg).mpr hgoal
  exact Nat.lt_succ_iff.mp hlt

/-- Positive witness for the hop bridge: pool (100, 50) with `y ≤ x`,
    inputs 10 and 17 (`g = 7`): outputs 4 and 7, difference 3 ≤ 7. -/
theorem witness_hop_lipschitz :
    50 * (10 + 7) / (100 + (10 + 7)) ≤ 50 * 10 / (100 + 10) + 7 := by
  native_decide

/-- Necessity of the price bound: on the imbalanced pool (1, 1000) the
    outputs at inputs 0 and 1 are 0 and 500 — a one-unit input difference
    moves the output by 500, so the Lipschitz hop bound fails when `y > x`. -/
theorem witness_hop_not_lipschitz :
    ¬ (1000 * (0 + 1) / (1 + (0 + 1)) ≤ 1000 * 0 / (1 + 0) + 1) := by
  native_decide

end RoundingErrorBound
end Proofs
