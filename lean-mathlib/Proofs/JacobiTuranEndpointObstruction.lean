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
