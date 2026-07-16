# Deift-Zhou Nonlinear Steepest Descent

## Candidate transfers

- `region_adaptive_analytic_certificate_v1`: partition a difficult analytic
  obligation into bulk/oscillatory, stationary-point, transition, and outer
  regions; attach a simple reference model and explicit remainder budget to
  each region; accept only when every local margin dominates its remainder.
- `stationary_point_parametrix_dispatch_v1`: recognize stationary-point type
  before choosing a certificate family. Use ordinary Bernstein subdivision in
  regular regions and a specialized local model only near a certified critical
  point or endpoint.
- `local_model_plus_residual_receipt_v1`: carry the tuple
  `(region, model_id, model_certificate, residual_bound, overlap_bound)` so a
  verifier checks the local model and the error separately.
- Apply the method first to the existing normalized Jacobi/Gegenbauer envelope
  corpus. Measure certificate piece count, exact-rational checking cost, and
  `UNKNOWN` rate against the current equal-subdivision Bernstein lane.

## Candidate outcome

- `failing_region_midpoint_refinement_v1` survives the bounded comparison:
  it preserves `772/772` positive accepts and `0/7` false accepts while
  reducing total certificate pieces from `3592` to `2928` and canonical bytes
  from `4076028` to `2663176`.
- `derivative_landmark_dispatch_v1` is retained as negative knowledge. It uses
  `2943` pieces but `4270358` bytes, so derivative-root guidance does not beat
  midpoint refinement on this corpus.
- coefficient-interpolated critical splits are dropped because recursive exact
  denominators depend on coefficient height and create an avoidable arithmetic
  work hazard.

## Proof targets

- A Lean gluing theorem: local lower bound `model >= margin`, residual bound
  `|target - model| <= error`, and `error <= margin` imply target
  nonnegativity on the covered region.
- A finite-cover theorem that lifts the local result to a closed interval when
  the certified regions cover it and overlap contracts agree.
- A small-norm perturbation theorem for a bounded operator, kept separate from
  any specific Riemann-Hilbert representation.

## Non-transfers

- The mKdV asymptotic theorem does not establish any AMM, liquidation, oracle,
  or routing property.
- The paper's asymptotic `O(...)` terms are not executable certificates until
  their constants and parameter domains are explicit.
- Parabolic-cylinder and Painleve local models should stay theory-only unless
  a concrete ZenoDEX obligation actually requires them and a rational checker
  can validate the resulting bounds.
