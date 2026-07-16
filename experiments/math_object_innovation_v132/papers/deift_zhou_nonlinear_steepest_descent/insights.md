# Deift-Zhou Nonlinear Steepest Descent

## Pass 1

- Deift and Zhou convert the inverse-scattering problem into a matrix
  Riemann-Hilbert factorization, factor the jump matrix, and deform the contour
  so jumps away from stationary points rapidly approach the identity.
- The remaining problem localizes to crosses around the stationary points.
  Their interactions vanish to higher order, so the leading contribution is a
  sum of independently solved local problems after a stationary-point scaling.
- The fixed local cross is solved with parabolic-cylinder functions. Undoing
  the deformation yields matched asymptotic descriptions across six regions,
  including a Painleve-II transition regime and a rapidly decaying outer
  regime.
- The reusable object is the proof architecture:
  `global factorization -> decay-oriented deformation -> local universal
  models -> interaction bound -> matched reconstruction`.

## Deepest current insights

- ZenoDEX should import the architecture as a certificate compiler, not the
  mKdV theorem. The immediate seam is the current orthogonal-polynomial
  certificate menu, where equal subdivisions work well in some families and
  poorly in oscillatory or transition regions.
- The decisive promotion boundary is finite error control. A leading
  asymptotic formula without an explicit, verifier-checkable remainder cannot
  authorize a Tau/FIRE or runtime claim.
- The first honest experiment was a region dispatcher over the existing exact
  Jacobi/Gegenbauer corpus. Pass 3 records the measured survivor and the
  falsified critical-point heuristic.

## Pass 2: executable gluing spine

- `ApproximationDefectCertificates.local_target_nonneg` now proves the exact
  local gluing law over real-valued targets and models.
- `ApproximationDefectCertificates.finiteCover_target_nonneg` lifts valid local
  certificates to any declared domain covered by a finite region list.
- `overlap_model_mismatch_bound` proves that two models tied to the same target
  differ by at most the sum of their local absolute-error bounds.
- This closed the abstract proof spine before the Pass 3 dispatcher comparison.

## Pass 3: region-dispatch falsification and survivor

- The exact comparison covers `772` positive Gegenbauer/Jacobi obligations and
  seven negative controls. Equal, midpoint-adaptive, and derivative-landmark
  methods all accept every positive and no negative.
- Refining only failing leaves is the consequential idea. Midpoint refinement
  lowers the cover from `3592` to `2928` pieces, lowers canonical certificate
  bytes by `1412852`, and reduces the maximum from `16` to `8` pieces.
- Critical-point selection itself does not survive. A bounded `1/64`
  derivative-landmark policy emits `15` more pieces and `1607182` more bytes
  than midpoint refinement. Exact coefficient interpolation was worse because
  it caused coefficient-height-dependent denominator growth.
- The paper transfer therefore narrows to adaptive regionalization plus typed
  residual accounting. Specialized local models need their own corpus before
  critical-point dispatch can earn a place in the certificate menu.
- Lean now proves arbitrary-degree nonnegative Bernstein combinations and the
  adaptive-cover lift. The exact Julia compiler has 12 power-basis parity
  checks; its general de Casteljau binding is not yet formalized.
