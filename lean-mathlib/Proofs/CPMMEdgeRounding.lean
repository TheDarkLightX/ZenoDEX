import Proofs.AntiFragmentation
import Proofs.CrossSliceComposition
import Mathlib.Tactic

/-!
# CPMM Per-Edge Rounding Error Bound

Bridges the gap between:
- `AntiFragmentation.lean`: CPMM floor division algebra (swapOut = ⌊y*a/(x+a)⌋)
- `CrossSliceComposition.lean`: Arbitrage certificate margin absorption

## Key Result

For any CPMM swap, floor division introduces **at most 1 unit** of rounding
error per edge. This per-edge bound is **independent of path length** in
the arbitrage graph, so a certificate with margin ≥ 1 absorbs CPMM
rounding on any cycle.

## Proof Chain

1. `AntiFragmentation.lean`: `swapOut`, `single_hop_gap`, `swap_euclidean`
2. This file: `ceilDiv`, gap ∈ {0, 1}, per-edge ε = 1
3. `CrossSliceComposition.lean`: `perturbed_no_arbitrage` with ε = 1
4. This file: `cpmm_certificate_rounding_safe` (abstract composition)

## Results

| # | Name | Statement |
|---|------|-----------|
| 1 | `ceilDiv` | Definition: ⌈n/d⌉ = (n + d - 1) / d |
| 2 | `floor_le_ceil` | ⌊n/d⌋ ≤ ⌈n/d⌉ |
| 3 | `ceil_le_floor_succ` | ⌈n/d⌉ ≤ ⌊n/d⌋ + 1 |
| 4 | `cpmm_edge_gap_le_one` | ceilSwapOut - swapOut ≤ 1 |
| 5 | `cpmm_floor_le_ceil` | swapOut ≤ ceilSwapOut |
| 6 | `cpmm_edge_perturbation` | ↑swapOut ≥ ↑ceilSwapOut - 1 (ℤ form) |
| 7 | `cpmm_certificate_rounding_safe` | **Main**: margin ≥ 1 ⇒ abstract rounding-safe certificate |
| W | 5 witnesses | Non-vacuity via native_decide |
-/

namespace Proofs
namespace CPMMEdgeRounding

open AntiFragmentation (swapOut swapOut_le_reserve)
open Proofs.ArbitrageCertificate (pathWeight)

/-! ## Part 1: Ceiling Division -/

/-- Ceiling division: ⌈n/d⌉ = (n + d - 1) / d for d > 0, 0 for d = 0.
    Standard formula: add (d-1) to make floor division round up. -/
def ceilDiv (n d : ℕ) : ℕ := (n + d - 1) / d

/-- Ceiling swap output: the most favorable (for trader) integer output.
    ⌈y*a/(x+a)⌉ — what the trader would get if rounding went in their favor. -/
def ceilSwapOut (x y a : ℕ) : ℕ := ceilDiv (y * a) (x + a)

/-! ## Part 2: Floor-Ceiling Gap Characterization -/

/-- FLOOR ≤ CEIL: floor division never exceeds ceiling division.
    Proof: numerator increases by d-1, denominator unchanged. -/
theorem floor_le_ceil (n d : ℕ) (hd : 0 < d) : n / d ≤ ceilDiv n d := by
  unfold ceilDiv
  exact Nat.div_le_div_right (by omega)

/-- CEIL ≤ FLOOR + 1: ceiling exceeds floor by at most 1.

    Proof strategy: show (n+d-1)/d < n/d + 2, then conclude ≤ n/d + 1.
    The key step uses Nat.div_lt_iff_lt_mul to convert to:
      n+d-1 < (n/d+2)*d
    which follows from n = d*(n/d) + n%d with n%d < d. -/
theorem ceil_le_floor_succ (n d : ℕ) (hd : 0 < d) : ceilDiv n d ≤ n / d + 1 := by
  unfold ceilDiv
  suffices h : (n + d - 1) / d < n / d + 2 by omega
  rw [Nat.div_lt_iff_lt_mul hd]
  have hmod := Nat.mod_lt n hd
  have heuclid := (Nat.div_add_mod n d).symm
  have : (n / d + 2) * d = d * (n / d) + 2 * d := by ring
  omega

/-- GAP TIGHT AT 0: when d divides n, ceiling equals floor. -/
theorem ceil_eq_floor_of_dvd (n d : ℕ) (hd : 0 < d) (hdvd : d ∣ n) :
    ceilDiv n d = n / d := by
  obtain ⟨k, rfl⟩ := hdvd
  simp only [ceilDiv, Nat.mul_div_cancel_left k hd]
  -- Goal: (d * k + d - 1) / d = k
  have hrw : d * k + d - 1 = (d - 1) + d * k := by omega
  rw [hrw, Nat.add_mul_div_left (d - 1) k hd, Nat.div_eq_of_lt (by omega : d - 1 < d)]
  omega

/-- GAP TIGHT AT 1: when d does not divide n, ceiling exceeds floor by exactly 1. -/
theorem ceil_eq_floor_succ_of_not_dvd (n d : ℕ) (hd : 0 < d) (hndvd : ¬ d ∣ n) :
    ceilDiv n d = n / d + 1 := by
  have hle := floor_le_ceil n d hd
  have hle2 := ceil_le_floor_succ n d hd
  -- Suffices to show ceilDiv ≠ n/d
  by_contra h
  push_neg at h
  -- h : ceilDiv n d ≠ n / d + 1, so ceilDiv n d = n / d (from hle, hle2)
  have heq : ceilDiv n d = n / d := by omega
  -- Show d ∣ n from heq
  unfold ceilDiv at heq
  have hmod := Nat.mod_lt n hd
  have heuclid := (Nat.div_add_mod n d).symm
  -- From (n + d - 1) / d = n / d:
  -- n/d * d ≤ n + d - 1 < (n/d + 1) * d
  -- But also n/d * d ≤ n (from div_mul_le_self)
  -- If n%d > 0: n ≥ n/d * d + 1, so n + d - 1 ≥ n/d * d + d = (n/d + 1) * d
  -- But (n + d - 1) / d = n/d means n + d - 1 < (n/d + 1) * d, contradiction
  have hmod_zero : n % d = 0 := by
    by_contra hmod_pos
    push_neg at hmod_pos
    have hmod_ge : 1 ≤ n % d := Nat.pos_of_ne_zero hmod_pos
    have hge : (n / d + 1) * d ≤ n + d - 1 := by
      have : (n / d + 1) * d = d * (n / d) + d := by ring
      omega
    have hbound : n + d - 1 < (n / d + 1) * d := by
      have : (n + d - 1) / d < n / d + 1 := by omega
      rwa [Nat.div_lt_iff_lt_mul hd] at this
    omega
  exact hndvd (Nat.dvd_of_mod_eq_zero hmod_zero)

/-! ## Part 3: CPMM Per-Edge Gap -/

/-- CPMM EDGE GAP ≤ 1: ceiling and floor swap outputs differ by at most 1.
    This is the per-edge rounding error for any CPMM pool.

    Derived from ceil_le_floor_succ applied to the CPMM numerator/denominator. -/
theorem cpmm_edge_gap_le_one (x y a : ℕ) :
    ceilSwapOut x y a ≤ swapOut x y a + 1 := by
  unfold ceilSwapOut swapOut
  by_cases h : 0 < x + a
  · exact ceil_le_floor_succ (y * a) (x + a) h
  · have hxa : x + a = 0 := by omega
    have hx : x = 0 := by omega
    have ha : a = 0 := by omega
    subst hx; subst ha
    simp [ceilDiv]

/-- CPMM EDGE GAP ≥ 0: floor output never exceeds ceiling output. -/
theorem cpmm_floor_le_ceil (x y a : ℕ) :
    swapOut x y a ≤ ceilSwapOut x y a := by
  unfold ceilSwapOut swapOut
  by_cases h : 0 < x + a
  · exact floor_le_ceil (y * a) (x + a) h
  · have hxa : x + a = 0 := by omega
    have hx : x = 0 := by omega
    have ha : a = 0 := by omega
    subst hx; subst ha
    simp [ceilDiv]

/-- PER-EDGE PERTURBATION (ℤ form): the actual (floor) output is at least
    the ideal (ceiling) output minus 1. This is the exact form needed by
    CrossSliceComposition's margin absorption theorem.

    ↑(swapOut x y a) ≥ ↑(ceilSwapOut x y a) - 1

    Proof: immediate from cpmm_edge_gap_le_one cast to ℤ. -/
theorem cpmm_edge_perturbation (x y a : ℕ) :
    (↑(swapOut x y a) : ℤ) ≥ ↑(ceilSwapOut x y a) - 1 := by
  have := cpmm_edge_gap_le_one x y a
  omega

/-! ## Part 4: Composition with Arbitrage Certificates

Main theorem: an arbitrage certificate with margin ≥ 1 on ceiling
(ideal) edge weights remains valid on floor (actual) edge weights.

This composes cpmm_edge_perturbation with CrossSliceComposition's
perturbed_no_arbitrage to close the known gap in rounding_arb_composition. -/

/-- **MAIN THEOREM**: abstract certificates with margin ≥ 1 are rounding-safe
    under the CPMM per-edge floor/ceiling gap bound.

    Given:
    - `w_ceil`: ceiling-division CPMM edge weights (ideal, favorable to trader)
    - `w_floor`: floor-division CPMM edge weights (actual)
    - `π`: potential certificate with margin ≥ 1 on ideal weights
    - `h_gap`: each edge satisfies the CPMM per-edge gap bound

    Then: no cycle has negative path weight on actual (floor) weights.

    This is THE cross-slice composition that connects CPMM floor division
    to the abstract arbitrage certificate system. -/
theorem cpmm_certificate_rounding_safe
    (w_ceil w_floor : ℕ → ℕ → ℤ) (π : ℕ → ℤ)
    (h_margin : ∀ u v, w_ceil u v + π u - π v ≥ 1)
    (h_gap : ∀ u v, w_floor u v ≥ w_ceil u v - 1)
    (s : ℕ) (mid : List ℕ) :
    pathWeight w_floor (s :: (mid ++ [s])) ≥ 0 :=
  Proofs.CrossSliceComposition.perturbed_no_arbitrage
    w_ceil w_floor π 1 (by omega) h_margin h_gap s mid

/-- CPMM GAP INSTANTIATION: for any pool graph where edges are CPMM swaps,
    the actual (floor) weights satisfy the perturbation bound w.r.t.
    ceiling weights.

    This provides the h_gap hypothesis for cpmm_certificate_rounding_safe. -/
theorem cpmm_gap_instantiation (pools : ℕ → ℕ → ℕ × ℕ × ℕ)
    (w_ceil w_floor : ℕ → ℕ → ℤ)
    (h_ceil : ∀ u v, w_ceil u v =
      ↑(ceilSwapOut (pools u v).1 (pools u v).2.1 (pools u v).2.2))
    (h_floor : ∀ u v, w_floor u v =
      ↑(swapOut (pools u v).1 (pools u v).2.1 (pools u v).2.2)) :
    ∀ u v, w_floor u v ≥ w_ceil u v - 1 := by
  intro u v
  rw [h_ceil, h_floor]
  exact cpmm_edge_perturbation (pools u v).1 (pools u v).2.1 (pools u v).2.2

/-! ## Part 5: Non-Vacuity Witnesses -/

/-- Ceiling division computation witness: floor vs ceil for various inputs. -/
theorem witness_ceil_div :
    10 / 3 = 3 ∧ ceilDiv 10 3 = 4 ∧
    9 / 3 = 3 ∧ ceilDiv 9 3 = 3 ∧
    1 / 3 = 0 ∧ ceilDiv 1 3 = 1 := by
  native_decide

/-- CPMM rounding gap = 1 witness: pool (1000, 1000), swap 100.
    floor output = 90, ceil output = 91, gap = 1.
    1000*100 = 100000, 100000/1100 = 90 (floor), ⌈100000/1100⌉ = 91 (ceil). -/
theorem witness_cpmm_gap_one :
    swapOut 1000 1000 100 = 90 ∧
    ceilSwapOut 1000 1000 100 = 91 ∧
    ceilSwapOut 1000 1000 100 - swapOut 1000 1000 100 = 1 := by
  native_decide

/-- CPMM rounding gap = 0 witness: pool (1000, 1100), swap 100.
    1100*100 = 110000, 110000/1100 = 100 exactly. Gap = 0. -/
theorem witness_cpmm_gap_zero :
    swapOut 1000 1100 100 = 100 ∧
    ceilSwapOut 1000 1100 100 = 100 ∧
    ceilSwapOut 1000 1100 100 - swapOut 1000 1100 100 = 0 := by
  native_decide

/-- Per-edge perturbation witness in ℤ: actual ≥ ideal - 1.
    Demonstrates the bound holds for gap=1, gap=0, and small-pool cases. -/
theorem witness_perturbation_z :
    -- Gap = 1 case: 90 ≥ 91 - 1 = 90 ✓
    (↑(swapOut 1000 1000 100) : ℤ) ≥ ↑(ceilSwapOut 1000 1000 100) - 1 ∧
    -- Gap = 0 case: 100 ≥ 100 - 1 = 99 ✓
    (↑(swapOut 1000 1100 100) : ℤ) ≥ ↑(ceilSwapOut 1000 1100 100) - 1 ∧
    -- Small pool: swapOut(1,1,1) = 0, ceilSwapOut(1,1,1) = 1, 0 ≥ 0 ✓
    swapOut 1 1 1 = 0 ∧ ceilSwapOut 1 1 1 = 1 ∧
    (↑(swapOut 1 1 1) : ℤ) ≥ ↑(ceilSwapOut 1 1 1) - 1 := by
  native_decide

/-- Arbitrage certificate witness: triangle with margin 1, CPMM rounding.
    Ideal weights [3, 3, -1] with potentials [0, 2, 4].
    Reduced costs: 3+0-2=1, 3+2-4=1, -1+4-0=3. Min margin = 1 ≥ 1.
    Perturbed weights [2, 2, -2] (each reduced by 1).
    Reduced costs: 2+0-2=0, 2+2-4=0, -2+4-0=2. All ≥ 0. Certificate survives! -/
theorem witness_certificate :
    let w_ceil : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 3
      else if a = 1 ∧ b = 2 then 3
      else if a = 2 ∧ b = 0 then -1
      else 0
    let w_floor : ℕ → ℕ → ℤ := fun a b =>
      if a = 0 ∧ b = 1 then 2
      else if a = 1 ∧ b = 2 then 2
      else if a = 2 ∧ b = 0 then -2
      else 0
    let π : ℕ → ℤ := fun x =>
      if x = 0 then 0 else if x = 1 then 2 else if x = 2 then 4 else 0
    -- Margin ≥ 1 on ideal weights
    w_ceil 0 1 + π 0 - π 1 = 1 ∧
    w_ceil 1 2 + π 1 - π 2 = 1 ∧
    w_ceil 2 0 + π 2 - π 0 = 3 ∧
    -- Gap ≤ 1 per edge
    w_floor 0 1 ≥ w_ceil 0 1 - 1 ∧
    w_floor 1 2 ≥ w_ceil 1 2 - 1 ∧
    w_floor 2 0 ≥ w_ceil 2 0 - 1 ∧
    -- Certificate still valid on rounded weights
    w_floor 0 1 + π 0 - π 1 ≥ 0 ∧
    w_floor 1 2 + π 1 - π 2 ≥ 0 ∧
    w_floor 2 0 + π 2 - π 0 ≥ 0 := by
  simp (config := { decide := true })

/-- **END-TO-END WITNESS**: pathWeight ≥ 0 on the rounded triangle 0→1→2→0.
    Weights [2, 2, -2] (the floor-rounded version of [3, 3, -1]).
    Cycle weight = 2 + 2 + (-2) = 2 ≥ 0.

    This directly witnesses the conclusion of cpmm_certificate_rounding_safe:
    the composition theorem's output is a non-negative pathWeight on actual edges. -/
theorem witness_end_to_end_pathWeight :
    pathWeight (fun a b =>
      if a = 0 ∧ b = 1 then (2 : ℤ)
      else if a = 1 ∧ b = 2 then 2
      else if a = 2 ∧ b = 0 then -2
      else 0)
    [0, 1, 2, 0] ≥ 0 := by
  simp [pathWeight]

end CPMMEdgeRounding
end Proofs
