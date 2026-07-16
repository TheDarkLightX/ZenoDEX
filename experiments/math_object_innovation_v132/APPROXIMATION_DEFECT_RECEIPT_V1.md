# Approximation Defect Receipt v1

Status: research-only executable certificate arithmetic. It has no settlement,
Tau, oracle, governance, or runtime authority.

## Accepted claim

For every region in a finite cover, the checker requires

```text
certified_bound(component) <= allocated_bound(component)

allocated_defect
  + allocated_interaction
  + allocated_reconstruction
  <= certified_model_margin
```

It also requires exact domain coverage, canonical region order, one overlap
contract per adjacent pair, exact overlap intervals, matching contract IDs, and
a SHA-256 root over the full receipt body. All rationals are reduced strings.
JSON numbers and floating-point values reject.

The parser also caps input/canonical payloads at 1,000,000 bytes, rational
strings at 128 characters, regions at 256, and multi-receipt inputs at 512.
Limit violations return `RESOURCE_LIMIT_EXCEEDED`.

An accepted receipt cites
`ApproximationDefectCertificates.finiteCover_target_nonneg`. The Lean theorem
proves the local error-budget gluing law and finite-cover lift.

## External assumption

Every `certificate_id` is opaque to this checker. Acceptance assumes each ID
refers to a valid upstream proof of its stated model margin or error bound. The
checker validates arithmetic and binding only. A future promotion must replace
opaque IDs with replayable certificate verifiers or proof receipts.

## Fail-closed witnesses

The built-in replay contains:

- `alice_valid_cover`: accepted two-region cover;
- `mallory_missing_region`: `COVERAGE_GAP`;
- `mallory_underestimated_defect`:
  `ALLOCATED_BOUND_UNDERESTATES_CERTIFIED_BOUND`;
- `mallory_omitted_interaction`: `FIELD_SET_MISMATCH`;
- `mallory_overlap_mismatch`: `OVERLAP_CONTRACT_MISMATCH`.

Replay:

```bash
python3 experiments/math_object_innovation_v132/approximation_defect_receipt.py --demo
python3 -m pytest -q \
  experiments/math_object_innovation_v132/test_approximation_defect_receipt.py
cd lean-mathlib && lake env lean Proofs/ApproximationDefectCertificates.lean
```

Schema:
`experiments/math_object_innovation_v132/approximation_defect_receipt_v1.schema.json`.

## Non-claims

- The checker does not prove a Jacobi, Gegenbauer, Riemann-Hilbert, mKdV, AMM,
  oracle, liquidation, or routing theorem.
- It does not turn asymptotic `O(...)` notation into a finite bound.
- It does not verify a numerical dbar or special-function solve.
- `UNKNOWN` is not a counterexample to the target inequality.
