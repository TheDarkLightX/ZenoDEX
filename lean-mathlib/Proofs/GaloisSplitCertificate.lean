import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Graded Discrete Concavity and Optimality Certificates for Split Routing

A unified theory of discrete concavity **with defect grading**, powering O(1)
optimality certificates for integer-valued objectives on finite domains.

`NearlyDiscreteConcave k f D` means all second differences of `f` on
`{0,...,D}` are bounded by `k`. Grade `k = 0` is exact discrete concavity
(`DiscreteConcave`). Floor-divided AMM outputs are grade 1; two-pool split
objectives are grade 2 (see `CPMMConcavity.lean`).

The theory is organized around two engine lemmas:

* `nearly_delta_le` — **slope drift**: first differences grow by at most `k`
  per step, `Δf(i+n) ≤ Δf(i) + n·k`;
* `nearly_chord_le` — **chord bound**: telescoping the slope drift,
  `2·(f(i+n) − f(i)) ≤ 2·n·Δf(i) + k·n·(n−1)`.

Everything else is a corollary. In particular the **approximate certificate**
`nearly_certificate_approx_global_max`: if `f` is grade-`k` and the two
neighbor checks pass at `a`, then for every `j ≤ D`

    2·(f(j) − f(a)) ≤ k·|j − a|·(|j − a| − 1).

At `k = 0` this *is* the exact certificate `certificate_implies_global_max`:
two local comparisons imply a global maximum. For `k > 0` it gives global
approximate optimality from the same two comparisons — no per-instance
concavity verification required.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 0 | `nearly_zero_iff_concave` | Bridge | Grade 0 ↔ `DiscreteConcave` |
| 1 | `nearly_delta_le` | Engine | Slope drift: Δf(i+n) ≤ Δf(i) + n·k |
| 2 | `nearly_chord_le` / `nearly_chord_le_rev` | Engine | chord bound |
| 3 | `nearly_sum` / `nearly_reverse` / `nearly_mono_grade` | Algebra | grade algebra |
| 4 | `nearly_right_delta_drift`, `nearly_right_quadratic_bound` | Derived | right-side drift |
| 5 | `nearly_left_delta_drift`, `nearly_left_quadratic_bound` | Derived | left-side mirror |
| 6 | `nearly_certificate_approx_global_max` | **Main** | error ≤ k·d·(d−1)/2 |
| 7 | exact chain lemmas | k = 0 | exact propagation |
| 8 | `certificate_implies_global_max` | k = 0 | 2-check global maximum |
| 9 | `necessity_right` / `necessity_left` | Converse | Failed neighbor check → not a global max |
| 10 | `strict_concave_maximizers_adjacent` | Structure | adjacent maximizers |
| 11 | `maximizer_interval` | Structure | Maximizer set is a contiguous interval |
-/

namespace Proofs
namespace GaloisSplitCertificate

/-- Discrete concavity on {0,...,D}: first differences are non-increasing. -/
def DiscreteConcave (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D →
    f (i + 2) - f (i + 1) ≤ f (i + 1) - f i

/-- Graded discrete concavity with defect `k`: second differences on
    `{0,...,D}` are bounded by `k`. Generalizes `DiscreteConcave` (the
    `k = 0` case) to capture floor-division rounding defects.

    The grade behaves like a (graded) monoid under pointwise addition:
    - sum of grade-k₁ and grade-k₂ has grade k₁+k₂ (`nearly_sum`)
    - index reversal preserves the grade (`nearly_reverse`)
    - grades are upward-closed (`nearly_mono_grade`) -/
def NearlyDiscreteConcave (k : ℤ) (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D → f (i + 2) - f (i + 1) ≤ f (i + 1) - f i + k

/-! ## Grade algebra -/

/-- **GRADE-0 BRIDGE**: `NearlyDiscreteConcave 0` is exactly `DiscreteConcave`.
    Every theorem below about grade-k functions specializes to the exact
    theory at k = 0, and the exact certificate is recovered this way. -/
theorem nearly_zero_iff_concave (f : ℕ → ℤ) (D : ℕ) :
    NearlyDiscreteConcave 0 f D ↔ DiscreteConcave f D := by
  simp only [NearlyDiscreteConcave, DiscreteConcave]
  constructor <;> intro h i hi <;> linarith [h i hi]

/-- **GRADE MONOTONICITY**: a tighter defect bound implies a looser one. -/
theorem nearly_mono_grade {k₁ k₂ : ℤ} (hle : k₁ ≤ k₂) {f : ℕ → ℤ} {D : ℕ}
    (h : NearlyDiscreteConcave k₁ f D) : NearlyDiscreteConcave k₂ f D :=
  fun i hi => by linarith [h i hi]

/-- **ADDITIVE COMPOSITION**: concavity defect is additive under function sum.
    Each summand contributes its own defect independently. This is the
    algebraic core of multi-pool split-routing analysis. -/
theorem nearly_sum (k₁ k₂ : ℤ) (f g : ℕ → ℤ) (D : ℕ)
    (hf : NearlyDiscreteConcave k₁ f D)
    (hg : NearlyDiscreteConcave k₂ g D) :
    NearlyDiscreteConcave (k₁ + k₂) (fun i => f i + g i) D := by
  intro i hi
  have := hf i hi; have := hg i hi
  show f (i + 2) + g (i + 2) - (f (i + 1) + g (i + 1)) ≤
       f (i + 1) + g (i + 1) - (f i + g i) + (k₁ + k₂)
  linarith

/-- **REVERSAL INVARIANCE**: index reversal `a ↦ f (D − a)` preserves the
    concavity defect. The second-difference condition is symmetric under
    `i ↦ D − i − 2`. Combined with `nearly_sum`, this is why a split
    objective `f(a) + g(D−a)` has defect `grade(f) + grade(g)`. -/
theorem nearly_reverse (k : ℤ) (f : ℕ → ℤ) (D : ℕ)
    (h : NearlyDiscreteConcave k f D) :
    NearlyDiscreteConcave k (fun a => f (D - a)) D := by
  intro i hi
  show f (D - (i + 2)) - f (D - (i + 1)) ≤ f (D - (i + 1)) - f (D - i) + k
  have eq1 : D - i = (D - (i + 2)) + 2 := by omega
  have eq2 : D - (i + 1) = (D - (i + 2)) + 1 := by omega
  rw [eq1, eq2]
  linarith [h (D - (i + 2)) (by omega : D - (i + 2) + 2 ≤ D)]

/-! ## The drift engine

Two lemmas carry the whole theory. Write `Δf(i) = f(i+1) − f(i)` for the
first difference (the "slope" at `i`).

* Slope drift: under grade-k concavity, slopes grow by at most `k` per
  step — `Δf(i+n) ≤ Δf(i) + n·k`. At `k = 0` this says slopes are
  non-increasing, the defining property of concavity.
* Chord bound: telescoping the slope drift bounds the function itself —
  `2·(f(i+n) − f(i)) ≤ 2·n·Δf(i) + k·n·(n−1)`. At `k = 0` this is the
  discrete chord-below-tangent inequality `f(i+n) ≤ f(i) + n·Δf(i)`. -/

/-- **SLOPE DRIFT (engine)**: under grade-k concavity, the first difference
    `n` steps to the right of `i` exceeds the one at `i` by at most `n·k`:

      f(i+n+1) − f(i+n) ≤ (f(i+1) − f(i)) + n·k.

    At k = 0 this is antitonicity of first differences. -/
theorem nearly_delta_le (k : ℤ) (f : ℕ → ℤ) (D : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (i n : ℕ) (hn : i + n + 1 ≤ D) :
    f (i + n + 1) - f (i + n) ≤ (f (i + 1) - f i) + n * k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have ihm := ih (by omega)
    have hc := hconc (i + m) (by omega)
    have e1 : i + (m + 1) + 1 = (i + m) + 2 := by omega
    have e2 : i + (m + 1) = (i + m) + 1 := by omega
    rw [e1, e2]
    push_cast
    linarith

/-- **CHORD BOUND (engine)**: telescoping the slope drift,

      2·(f(i+n) − f(i)) ≤ 2·n·(f(i+1) − f(i)) + k·n·(n−1).

    Stated with the factor 2 to avoid integer division by 2 on the
    drift term `k·n·(n−1)/2`. At k = 0 this is the discrete
    chord-below-tangent inequality. The bound is tight: equality holds
    for `f(i) = k·i·(i−1)/2` (see `witness_nearly_certificate_tight`). -/
theorem nearly_chord_le (k : ℤ) (f : ℕ → ℤ) (D : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (i n : ℕ) (hn : i + n ≤ D) :
    2 * (f (i + n) - f i) ≤ 2 * n * (f (i + 1) - f i) + k * n * (n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have ihm := ih (by omega)
    have hd := nearly_delta_le k f D hconc i m (by omega)
    have e : i + (m + 1) = (i + m) + 1 := by omega
    rw [e]
    push_cast at ihm hd ⊢
    nlinarith [ihm, hd]

/-- **CHORD BOUND (right-anchored)**: the mirror of `nearly_chord_le`,
    anchored at the right endpoint of the chord:

      2·(f(i) − f(i+n)) ≤ 2·n·(f(i+n−1) − f(i+n)) + k·n·(n−1).

    Derived from `nearly_chord_le` via `nearly_reverse` — no second
    induction. At k = 0: walking left from i+n, the function gains at most
    n times the (leftward) slope at the right endpoint. -/
theorem nearly_chord_le_rev (k : ℤ) (f : ℕ → ℤ) (D : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (i n : ℕ) (hin : i + n ≤ D) :
    2 * (f i - f (i + n)) ≤ 2 * n * (f (i + n - 1) - f (i + n)) + k * n * (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  have hg := nearly_reverse k f D hconc
  have h := nearly_chord_le k (fun a => f (D - a)) D hg (D - (i + n)) n (by omega)
  simp only at h
  rwa [show D - (D - (i + n) + n) = i by omega,
       show D - (D - (i + n)) = i + n by omega,
       show D - (D - (i + n) + 1) = i + n - 1 by omega] at h

/-! ## Right-side drift under a non-positive initial slope -/

/-- **DELTA DRIFT (right)**: under grade-k concavity, if the first difference
    at `a` is non-positive, then the first difference `n` steps later is at
    most `n·k`. For k = 0 deltas stay non-positive forever, recovering
    `right_delta_chain`. -/
theorem nearly_right_delta_drift (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n + 1 ≤ D) :
    f (a + n + 1) - f (a + n) ≤ ↑n * k := by
  have h := nearly_delta_le k f D hconc a n hn
  linarith

/-- **QUADRATIC DRIFT BOUND (right)**: under grade-k concavity with a
    non-positive initial delta, the cumulative drift over n steps satisfies

      2·(f(a+n) − f(a)) ≤ n·(n−1)·k.

    For k = 0: f(a+n) ≤ f(a) (exact right monotonicity).
    For k = 1: f(a+n) ≤ f(a) + n·(n−1)/2 (quadratic error). -/
theorem nearly_right_quadratic_bound (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n ≤ D) :
    2 * (f (a + n) - f a) ≤ ↑n * (↑n - 1) * k := by
  have h := nearly_chord_le k f D hconc a n hn
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  nlinarith [h, mul_nonneg hn0 (by linarith : (0:ℤ) ≤ f a - f (a + 1))]

/-! ## Left-side mirror (via reversal)

The left-side statements are *derived* from the right-side ones by the
reversal symmetry `a ↦ f (D − a)` — no second induction is needed. -/

/-- **DELTA DRIFT (left)**: mirror of `nearly_right_delta_drift`. If the
    first difference into `a` is non-negative (`f(a−1) ≤ f(a)`), then `n`
    steps to the left it has decreased by at most `n·k`:

      f(a−n−1) − f(a−n) ≤ n·k. -/
theorem nearly_left_delta_drift (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D) (haD : a ≤ D)
    (h_base : f (a - 1) ≤ f a)
    (n : ℕ) (hn : n + 1 ≤ a) :
    f (a - n - 1) - f (a - n) ≤ ↑n * k := by
  have hg := nearly_reverse k f D hconc
  have hbase' : f (D - (D - a + 1)) ≤ f (D - (D - a)) := by
    rw [show D - (D - a + 1) = a - 1 by omega, show D - (D - a) = a by omega]
    exact h_base
  have h := nearly_right_delta_drift k (fun i => f (D - i)) D (D - a) hg hbase' n (by omega)
  simp only at h
  rwa [show D - (D - a + n + 1) = a - n - 1 by omega,
       show D - (D - a + n) = a - n by omega] at h

/-- **QUADRATIC DRIFT BOUND (left)**: mirror of
    `nearly_right_quadratic_bound`, derived via reversal:

      2·(f(a−n) − f(a)) ≤ n·(n−1)·k. -/
theorem nearly_left_quadratic_bound (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D) (haD : a ≤ D)
    (h_base : f (a - 1) ≤ f a)
    (n : ℕ) (hn : n ≤ a) :
    2 * (f (a - n) - f a) ≤ ↑n * (↑n - 1) * k := by
  have hg := nearly_reverse k f D hconc
  have hbase' : f (D - (D - a + 1)) ≤ f (D - (D - a)) := by
    rw [show D - (D - a + 1) = a - 1 by omega, show D - (D - a) = a by omega]
    exact h_base
  have h := nearly_right_quadratic_bound k (fun i => f (D - i)) D (D - a) hg hbase' n (by omega)
  simp only at h
  rwa [show D - (D - a + n) = a - n by omega,
       show D - (D - a) = a by omega] at h

/-! ## The approximate certificate (main theorem) -/

/-- **APPROXIMATE CERTIFICATE**: for a grade-k nearly-concave function, the
    same two neighbor comparisons that certify a global maximum in the exact
    theory certify *global approximate optimality*: for every `j ≤ D`,

      2·(f(j) − f(a)) ≤ k·d·(d−1),   where d = |j − a|.

    Only 2 comparisons are needed, for any domain size D. At k = 0 the
    right-hand side vanishes and this is exactly
    `certificate_implies_global_max`. For floor-divided AMM objectives
    (k = 1 per pool, k = 2 for a two-pool split) this gives an
    unconditional O(1)-verifiable optimality envelope — no per-instance
    concavity check required.

    The bound is tight: `f(i) = k·i·(i−1)/2` achieves equality at every
    point (see `witness_nearly_certificate_tight`). -/
theorem nearly_certificate_approx_global_max (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hconc : NearlyDiscreteConcave k f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1))
    (j : ℕ) (hj : j ≤ D) :
    2 * (f j - f a) ≤ k * |(j : ℤ) - a| * (|(j : ℤ) - a| - 1) := by
  by_cases hja : j ≤ a
  · -- Left side: j ≤ a, distance d = a − j.
    have habs : |(j : ℤ) - a| = ((a - j : ℕ) : ℤ) := by
      rw [abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ (a : ℤ) - j)]
      omega
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · -- a = 0 forces j = 0: both sides are 0.
      have hj0 : j = 0 := by omega
      subst hj0
      simp
    · have h := nearly_left_quadratic_bound k f D a hconc ha (h_prev hapos)
        (a - j) (by omega)
      rw [show a - (a - j) = j by omega] at h
      rw [habs]
      calc 2 * (f j - f a)
          ≤ ((a - j : ℕ) : ℤ) * (((a - j : ℕ) : ℤ) - 1) * k := h
        _ = k * ((a - j : ℕ) : ℤ) * (((a - j : ℕ) : ℤ) - 1) := by ring
  · -- Right side: a < j ≤ D, distance d = j − a.
    have haj : a < j := by omega
    have habs : |(j : ℤ) - a| = ((j - a : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (j : ℤ) - a)]
      omega
    have h := nearly_right_quadratic_bound k f D a hconc (h_next (by omega))
      (j - a) (by omega)
    rw [show a + (j - a) = j by omega] at h
    rw [habs]
    calc 2 * (f j - f a)
        ≤ ((j - a : ℕ) : ℤ) * (((j - a : ℕ) : ℤ) - 1) * k := h
      _ = k * ((j - a : ℕ) : ℤ) * (((j - a : ℕ) : ℤ) - 1) := by ring

/-! ## Exact theory (k = 0)

All exact-concavity propagation lemmas and the exact certificate are
corollaries of the graded theory at grade 0. -/

/-- Under concavity, non-positive deltas propagate rightward.
    (Grade-0 corollary of `nearly_right_delta_drift`.) -/
theorem right_delta_chain (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n + 1 ≤ D) :
    f (a + n + 1) ≤ f (a + n) := by
  have h := nearly_right_delta_drift 0 f D a
    ((nearly_zero_iff_concave f D).mpr hconc) h_base n hn
  simp only [mul_zero] at h
  linarith

/-- f(a) ≥ f(a+n) for all n, from a non-positive delta at a.
    (Grade-0 corollary of `nearly_right_quadratic_bound`.) -/
theorem right_mono (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n ≤ D) :
    f a ≥ f (a + n) := by
  have h := nearly_right_quadratic_bound 0 f D a
    ((nearly_zero_iff_concave f D).mpr hconc) h_base n hn
  simp only [mul_zero] at h
  linarith

/-- Under concavity, non-negative deltas propagate leftward, expressed
    with the distance d from a. (Grade-0 corollary of `nearly_left_delta_drift`.) -/
theorem left_delta_chain (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D) (haD : a ≤ D)
    (h_base : f a ≥ f (a - 1))
    (d : ℕ) (hd : d < a) :
    f (a - d) ≥ f (a - d - 1) := by
  have h := nearly_left_delta_drift 0 f D a
    ((nearly_zero_iff_concave f D).mpr hconc) haD h_base d (by omega)
  simp only [mul_zero] at h
  linarith

/-- f(a) ≥ f(j) for all j ≤ a (left monotonicity from concavity).
    (Grade-0 corollary of `nearly_left_quadratic_bound`.) -/
theorem left_mono (f : ℕ → ℤ) (D a : ℕ)
    (hconc : DiscreteConcave f D) (haD : a ≤ D)
    (h_base : f a ≥ f (a - 1))
    (j : ℕ) (hj : j ≤ a) :
    f a ≥ f j := by
  have h := nearly_left_quadratic_bound 0 f D a
    ((nearly_zero_iff_concave f D).mpr hconc) haD h_base (a - j) (by omega)
  rw [show a - (a - j) = j by omega] at h
  simp only [mul_zero] at h
  linarith

/-- **Certificate Soundness**: If f is discretely concave on {0,...,D}
    and the 2-comparison certificate holds at a, then a is a global maximum.

    Certificate = 2 comparisons only:
    - f(a) ≥ f(a-1)   (left neighbor, vacuous when a=0)
    - f(a) ≥ f(a+1)   (right neighbor, vacuous when a=D)

    Boundary comparisons (f(a) ≥ f(0), f(a) ≥ f(D)) are NOT needed —
    they follow from concavity + neighbor checks.

    This is the grade-0 instance of `nearly_certificate_approx_global_max`:
    at k = 0 the approximation error k·d·(d−1)/2 vanishes identically. -/
theorem certificate_implies_global_max (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hconc : DiscreteConcave f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1))
    (j : ℕ) (hj : j ≤ D) :
    f a ≥ f j := by
  have h := nearly_certificate_approx_global_max 0 f D a ha
    ((nearly_zero_iff_concave f D).mpr hconc) h_prev h_next j hj
  simp only [zero_mul] at h
  linarith

/-! ## Certificate necessity -/

/-- **Necessity (right)**: if f(a) < f(a+1) then a is NOT the global max on {0,...,D}. -/
theorem necessity_right (f : ℕ → ℤ) (D a : ℕ)
    (ha : a < D)
    (h_fail : f a < f (a + 1)) :
    ∃ j, j ≤ D ∧ f j > f a :=
  ⟨a + 1, by omega, h_fail⟩

/-- **Necessity (left)**: if f(a) < f(a-1) then a is NOT the global max on {0,...,D}.
    Uses the natural number convention: a - 1 = 0 when a = 0 (vacuous). -/
theorem necessity_left (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D) (hapos : 0 < a)
    (h_fail : f a < f (a - 1)) :
    ∃ j, j ≤ D ∧ f j > f a :=
  ⟨a - 1, by omega, h_fail⟩

/-! ## Strict concavity and uniqueness -/

/-- Strict discrete concavity: first differences are strictly decreasing. -/
def StrictDiscreteConcave (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D →
    f (i + 2) - f (i + 1) < f (i + 1) - f i

/-- Strict concavity implies (non-strict) concavity. -/
theorem strict_concave_is_concave (f : ℕ → ℤ) (D : ℕ)
    (h : StrictDiscreteConcave f D) : DiscreteConcave f D :=
  fun i hi => le_of_lt (h i hi)

/-- **Maximizers adjacent**: Under strict discrete concavity, if a ≤ b are both
    global maxima on {0,...,D} then b ≤ a + 1. The set of maximizers has at most
    2 elements (and they must be consecutive).

    Proof: If b ≥ a+2, strict concavity forces f(a+k+2) < f(a) for all valid k
    (strict propagation of negative deltas), contradicting f(b) = f(a). -/
theorem strict_concave_maximizers_adjacent (f : ℕ → ℤ) (D a b : ℕ)
    (hconc : StrictDiscreteConcave f D)
    (ha : a ≤ D) (hb : b ≤ D)
    (hmax_a : ∀ j, j ≤ D → f a ≥ f j)
    (hmax_b : ∀ j, j ≤ D → f b ≥ f j)
    (_hab : a ≤ b) :
    b ≤ a + 1 := by
  by_contra hge
  push_neg at hge
  -- b ≥ a + 2
  have heq : f a = f b := le_antisymm (hmax_b a ha) (hmax_a b hb)
  have h_base : f (a + 1) ≤ f a := hmax_a (a + 1) (by omega)
  have hconc_weak := strict_concave_is_concave f D hconc
  -- Key: f(a + k + 2) < f(a) for all valid k, by induction
  suffices key : ∀ k, a + k + 2 ≤ D → f (a + k + 2) < f a by
    have hk := key (b - a - 2) (by omega)
    have he : a + (b - a - 2) + 2 = b := by omega
    rw [he] at hk
    linarith
  intro k
  induction k with
  | zero =>
    -- Base: strict concavity at a gives f(a+2) - f(a+1) < f(a+1) - f(a) ≤ 0
    intro hbd
    have hsc := hconc a (by omega)
    linarith
  | succ m ih =>
    intro hbd
    have ihm := ih (by omega)
    -- f(a+(m+1)+1) ≤ f(a+(m+1)) from non-strict right_delta_chain
    have hdrop := right_delta_chain f D a hconc_weak h_base (m + 1) (by omega)
    -- Strict concavity at position a+m+1
    have hsc := hconc (a + m + 1) (by omega)
    -- Normalize Nat arithmetic for linarith
    have e1 : a + (m + 1) + 1 = a + m + 2 := by omega
    have e2 : a + (m + 1) = a + m + 1 := by omega
    have e3 : (a + m + 1) + 2 = a + m + 3 := by omega
    have e4 : (a + m + 1) + 1 = a + m + 2 := by omega
    have e5 : a + (m + 1) + 2 = a + m + 3 := by omega
    rw [e1, e2] at hdrop
    rw [e3, e4] at hsc
    -- hdrop: f(a+m+2) ≤ f(a+m+1), so delta ≤ 0
    -- hsc: f(a+m+3) - f(a+m+2) < f(a+m+2) - f(a+m+1) ≤ 0
    -- ihm: f(a+m+2) < f(a)
    -- Therefore f(a+m+3) < f(a+m+2) < f(a)
    show f (a + (m + 1) + 2) < f a
    rw [e5]
    linarith

/-! ## Maximizer set structure -/

/-- **MAXIMIZER INTERVAL**: Under discrete concavity, if `a` and `b` are both
    global maxima on {0,...,D} with `a ≤ c ≤ b`, then `c` is also a global maximum.
    The set of maximizers is a contiguous interval {a, a+1, ..., b}.

    Proof: `right_delta_chain` propagates non-positive deltas from `a` through to `c`,
    giving `f(c+1) ≤ f(c)`. Then `right_mono` from `c` yields `f(c) ≥ f(b)`.
    Since `b` is a global max, `f(c) ≥ f(b) ≥ f(a) ≥ f(j)` for all `j`. -/
theorem maximizer_interval (f : ℕ → ℤ) (D a c b : ℕ)
    (hconc : DiscreteConcave f D)
    (ha : a ≤ D) (hb : b ≤ D) (hac : a ≤ c) (hcb : c ≤ b)
    (hmax_a : ∀ j, j ≤ D → f a ≥ f j)
    (hmax_b : ∀ j, j ≤ D → f b ≥ f j) :
    ∀ j, j ≤ D → f c ≥ f j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le hac with rfl | hac'
  · exact hmax_a j hj
  rcases Nat.eq_or_lt_of_le hcb with rfl | hcb'
  · exact hmax_b j hj
  -- Interior: a < c < b
  have ha1 : f (a + 1) ≤ f a := hmax_a (a + 1) (by omega)
  -- Propagate non-positive deltas from a to c
  have hc1 : f (c + 1) ≤ f c := by
    have h := right_delta_chain f D a hconc ha1 (c - a) (by omega)
    rwa [show a + (c - a) + 1 = c + 1 from by omega,
         show a + (c - a) = c from by omega] at h
  -- f(c) ≥ f(b) via right_mono from c
  have hcb_ge : f c ≥ f b := by
    have h := right_mono f D c hconc hc1 (b - c) (by omega)
    rwa [show c + (b - c) = b from by omega] at h
  -- Chain: f(c) ≥ f(b) ≥ f(a) ≥ f(j)
  linarith [hmax_b a ha, hmax_a j hj]

/-! ## Non-vacuity witnesses -/

/-- f(x) = -(x-5)² + 25 is discretely concave on {0,...,10}.
    The second difference is constantly -2. -/
theorem witness_concave :
    DiscreteConcave (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 := by
  intro i hi
  have hi' : i ≤ 8 := by omega
  interval_cases i <;> norm_num

/-- f(x) = -(x-5)² + 25 is STRICTLY discretely concave on {0,...,10}. -/
theorem witness_strict_concave :
    StrictDiscreteConcave (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 := by
  intro i hi
  have hi' : i ≤ 8 := by omega
  interval_cases i <;> norm_num

/-- End-to-end witness: a=5 is the global max of -(x-5)² + 25 on {0,...,10},
    proved via `certificate_implies_global_max` (not reproving independently). -/
theorem witness_global_max :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∀ j : ℕ, j ≤ 10 → f 5 ≥ f j :=
  certificate_implies_global_max
    (fun x : ℕ => -((x : ℤ) - 5) ^ 2 + 25) 10 5
    (by omega)
    witness_concave
    (by intro; norm_num)
    (by intro; norm_num)

/-- Necessity witness: f(4) < f(5), so a=4 is NOT the global max. -/
theorem witness_necessity_right :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∃ j, j ≤ 10 ∧ f j > f 4 := by
  exact necessity_right _ 10 4 (by omega) (by norm_num)

/-- Adjacency witness: any two global maxima of -(x-5)² + 25 on {0,...,10} are
    within distance 1 of each other. -/
theorem witness_adjacency :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 5) ^ 2 + 25
    ∀ a b : ℕ, a ≤ 10 → b ≤ 10 → a ≤ b →
    (∀ j, j ≤ 10 → f a ≥ f j) → (∀ j, j ≤ 10 → f b ≥ f j) → b ≤ a + 1 :=
  fun a b ha hb hab hma hmb =>
    strict_concave_maximizers_adjacent _ 10 a b witness_strict_concave ha hb hma hmb hab

/-- Maximizer interval witness: f(x) = min(x, 3) on {0,...,6} has
    maximizers {3, 4, 5, 6} — a contiguous interval, as predicted. -/
theorem witness_maximizer_interval :
    let f : ℕ → ℤ := fun x => min (x : ℤ) 3
    f 3 = 3 ∧ f 4 = 3 ∧ f 5 = 3 ∧ f 6 = 3 ∧ f 0 = 0 := by
  decide

/-- **TIGHTNESS of the approximate certificate**: `f(i) = i·(i−1)` has grade
    exactly 2 (constant second difference 2), passes both neighbor checks at
    `a = 0`, and the bound `2·(f(j) − f(0)) ≤ 2·j·(j−1)` holds with EQUALITY
    at every point j. No smaller envelope is valid for grade-2 functions. -/
theorem witness_nearly_certificate_tight :
    let f : ℕ → ℤ := fun i => (i : ℤ) * ((i : ℤ) - 1)
    NearlyDiscreteConcave 2 f 5 ∧
    (f 1 ≤ f 0) ∧
    (∀ j : ℕ, j ≤ 5 → 2 * (f j - f 0) = 2 * (j : ℤ) * ((j : ℤ) - 1)) := by
  refine ⟨fun i _ => by push_cast; ring_nf; omega, by norm_num, fun j hj => by push_cast; ring⟩

/-- Approximate-certificate witness on a non-trivial grade-1 function:
    f(x) = -(x-3)² + x·(x−1)/2-style mix would be overkill — instead check the
    end-to-end inequality numerically for f(x) = -(x-3)² + 9 perturbed by a
    grade-1 defect at one point: f = [0, 5, 8, 9, 9, 8] on {0,...,5}.
    Second differences: -2, -2, -1, +1 ≤ 1 (grade 1); neighbor checks pass at
    a = 3 (f(2)=8 ≤ 9, f(4)=9 ≤ 9); and every j satisfies the grade-1 envelope
    2·(f(j) − f(3)) ≤ |j−3|·(|j−3|−1). -/
theorem witness_nearly_certificate_grade_one :
    let f : ℕ → ℤ := fun i => [0, 5, 8, 9, 9, 8].getD i 0
    NearlyDiscreteConcave 1 f 5 ∧
    (f 2 ≤ f 3 ∧ f 4 ≤ f 3) ∧
    (∀ j : ℕ, j ≤ 5 →
      2 * (f j - f 3) ≤ |(j : ℤ) - 3| * (|(j : ℤ) - 3| - 1)) := by
  constructor
  · intro i hi
    have hi' : i ≤ 3 := by omega
    interval_cases i <;> decide
  constructor
  · norm_num
  · intro j hj
    interval_cases j <;> decide

end GaloisSplitCertificate
end Proofs
