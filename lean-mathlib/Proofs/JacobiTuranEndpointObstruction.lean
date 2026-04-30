import Mathlib.Tactic

/-!
# Jacobi Turan Endpoint Obstruction Skeleton

This packet promotes the algebraic core of
`experiments/math_object_innovation_v189`.

It does **not** prove Gasper's full Jacobi Turan theorem. Instead, it proves the
small exact identity that explains why the wrong endpoint normalization is
mathematically false at the endpoint.
-/

namespace Proofs
namespace JacobiTuranEndpointObstruction

/-- Local Turan determinant for three adjacent endpoint values. -/
def turanEndpoint (prev cur next : Rat) : Rat :=
  cur ^ 2 - prev * next

/-- Right-normalized endpoint obstruction.

In plain English: if adjacent endpoint ratios satisfy the Jacobi binomial-ratio
recurrences, then the endpoint Turan determinant has sign controlled by
`beta - alpha`, up to positive factors.
-/
theorem right_endpoint_obstruction_formula
    (r alpha beta n : Rat)
    (hDen0 : n + beta ≠ 0)
    (hDen1 : n + alpha + 1 ≠ 0) :
    turanEndpoint
        (r * ((n + alpha) / (n + beta)))
        r
        (r * ((n + beta + 1) / (n + alpha + 1))) =
      r ^ 2 * (beta - alpha) / ((n + alpha + 1) * (n + beta)) := by
  unfold turanEndpoint
  have hProd : (n + alpha + 1) * (n + beta) ≠ 0 := by
    exact mul_ne_zero hDen1 hDen0
  field_simp [hDen0, hDen1, hProd]
  ring_nf

/-- Left-normalized endpoint obstruction, obtained by the mirrored parameter
orientation.

In plain English: the left endpoint has the same formula with `alpha` and
`beta` swapped, so the wrong strict cone gives a negative endpoint value before
any interval certificate is attempted.
-/
theorem left_endpoint_obstruction_formula
    (r alpha beta n : Rat)
    (hDen0 : n + alpha ≠ 0)
    (hDen1 : n + beta + 1 ≠ 0) :
    turanEndpoint
        (r * ((n + beta) / (n + alpha)))
        r
        (r * ((n + alpha + 1) / (n + beta + 1))) =
      r ^ 2 * (alpha - beta) / ((n + beta + 1) * (n + alpha)) := by
  unfold turanEndpoint
  have hProd : (n + beta + 1) * (n + alpha) ≠ 0 := by
    exact mul_ne_zero hDen1 hDen0
  field_simp [hDen0, hDen1, hProd]
  ring_nf

/-! ## Sign consequences for recognizer prefilters -/

/-- Right endpoint is nonnegative in the `beta >= alpha` cone.

In plain English: once the positive denominator side conditions hold, the
right-normalized endpoint obstruction cannot be negative inside the right cone.
-/
theorem right_endpoint_obstruction_nonneg_of_alpha_le_beta
    (r alpha beta n : Rat)
    (hDen0 : 0 < n + beta)
    (hDen1 : 0 < n + alpha + 1)
    (hCone : alpha <= beta) :
    0 <=
      turanEndpoint
        (r * ((n + alpha) / (n + beta)))
        r
        (r * ((n + beta + 1) / (n + alpha + 1))) := by
  rw [right_endpoint_obstruction_formula r alpha beta n
    (ne_of_gt hDen0) (ne_of_gt hDen1)]
  have hDiff : 0 <= beta - alpha := sub_nonneg.mpr hCone
  have hDen : 0 < (n + alpha + 1) * (n + beta) :=
    mul_pos hDen1 hDen0
  exact div_nonneg (mul_nonneg (sq_nonneg r) hDiff) (le_of_lt hDen)

/-- Right endpoint is strictly negative outside the `beta >= alpha` cone.

In plain English: if `beta < alpha`, a right-normalized Jacobi Turan claim is
already false at the opposite endpoint, provided the endpoint ratio is nonzero.
-/
theorem right_endpoint_obstruction_negative_of_beta_lt_alpha
    (r alpha beta n : Rat)
    (hr : r ≠ 0)
    (hDen0 : 0 < n + beta)
    (hDen1 : 0 < n + alpha + 1)
    (hWrongCone : beta < alpha) :
    turanEndpoint
        (r * ((n + alpha) / (n + beta)))
        r
        (r * ((n + beta + 1) / (n + alpha + 1))) < 0 := by
  rw [right_endpoint_obstruction_formula r alpha beta n
    (ne_of_gt hDen0) (ne_of_gt hDen1)]
  have hSq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hDiff : beta - alpha < 0 := sub_neg.mpr hWrongCone
  have hDen : 0 < (n + alpha + 1) * (n + beta) :=
    mul_pos hDen1 hDen0
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hSq hDiff) hDen

/-- Left endpoint is nonnegative in the mirrored `alpha >= beta` cone. -/
theorem left_endpoint_obstruction_nonneg_of_beta_le_alpha
    (r alpha beta n : Rat)
    (hDen0 : 0 < n + alpha)
    (hDen1 : 0 < n + beta + 1)
    (hCone : beta <= alpha) :
    0 <=
      turanEndpoint
        (r * ((n + beta) / (n + alpha)))
        r
        (r * ((n + alpha + 1) / (n + beta + 1))) := by
  rw [left_endpoint_obstruction_formula r alpha beta n
    (ne_of_gt hDen0) (ne_of_gt hDen1)]
  have hDiff : 0 <= alpha - beta := sub_nonneg.mpr hCone
  have hDen : 0 < (n + beta + 1) * (n + alpha) :=
    mul_pos hDen1 hDen0
  exact div_nonneg (mul_nonneg (sq_nonneg r) hDiff) (le_of_lt hDen)

/-- Left endpoint is strictly negative outside the mirrored `alpha >= beta` cone. -/
theorem left_endpoint_obstruction_negative_of_alpha_lt_beta
    (r alpha beta n : Rat)
    (hr : r ≠ 0)
    (hDen0 : 0 < n + alpha)
    (hDen1 : 0 < n + beta + 1)
    (hWrongCone : alpha < beta) :
    turanEndpoint
        (r * ((n + beta) / (n + alpha)))
        r
        (r * ((n + alpha + 1) / (n + beta + 1))) < 0 := by
  rw [left_endpoint_obstruction_formula r alpha beta n
    (ne_of_gt hDen0) (ne_of_gt hDen1)]
  have hSq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hDiff : alpha - beta < 0 := sub_neg.mpr hWrongCone
  have hDen : 0 < (n + beta + 1) * (n + alpha) :=
    mul_pos hDen1 hDen0
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hSq hDiff) hDen

/-- Non-vacuity check for the right endpoint formula. -/
example :
    turanEndpoint
        ((3 : Rat) * (((5 : Rat) + 1) / ((5 : Rat) + 2)))
        (3 : Rat)
        ((3 : Rat) * (((5 : Rat) + 2 + 1) / ((5 : Rat) + 1 + 1))) =
      (3 : Rat) ^ 2 * (2 - 1) / (((5 : Rat) + 1 + 1) * ((5 : Rat) + 2)) := by
  exact right_endpoint_obstruction_formula 3 1 2 5 (by norm_num) (by norm_num)

end JacobiTuranEndpointObstruction
end Proofs
