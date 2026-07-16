# Wang-Ma Dbar Steepest Descent

## Candidate transfers

- `approximation_defect_receipt_v1`: replace an unavailable analytic extension
  with an explicit interpolation plus a defect object. The receipt carries a
  certified reference model, a defect norm, a decay integral bound, and the
  final reconstruction margin.
- `weak_regular_data_certificate_v1`: investigate whether sampled or
  coefficient-based analytic obligations can be certified under Sobolev-style
  regularity assumptions instead of requiring exact special-function
  recognition.
- `separated_local_contribution_receipt_v1`: certify each stationary-point
  contribution independently, then add an explicit interaction-error bound
  before composing the global result.
- Use this only as an offchain certificate generator. The verifier must check a
  rational residual bound and may return `UNKNOWN`; it must never trust a
  floating-point dbar solve.

## Proof targets

- A Lean approximation-margin theorem:
  `lowerBound(model, region) >= epsilon` and
  `forall x in region, |target x - model x| <= epsilon` imply
  `target >= 0` on the region.
- A compositional error-budget theorem for local model error, interaction
  error, and reconstruction error.
- A norm-budget theorem stating that every accepted global error is bounded by
  the sum of its typed component budgets.

## Non-transfers

- Weighted Sobolev initial data for the mKdV hierarchy is unrelated to oracle
  decentralization or market-data validity.
- The asymptotic error rates `t^-3/4`, `t^-1`, and the Painleve-region rate are
  paper-specific and must not be reused as DEX error rates.
- A nonanalytic interpolation is useful only if its dbar defect is bounded by a
  deterministic checker; numerical smoothness is insufficient.
