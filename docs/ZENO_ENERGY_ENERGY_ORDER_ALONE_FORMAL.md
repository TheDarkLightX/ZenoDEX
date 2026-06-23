# ZenoEnergy Energy-Order-Alone Formal Boundary

Artifact:
`data/upba_energy/zenoenergy_energy_order_alone_formal_receipt.json`

Lean target:
`lean-mathlib/Proofs/ZenoEnergyAdvisoryBoundary.lean`

## Claim

Advisory energy ordering alone is not a verifier-facing optimality certificate.
The Lean boundary now includes two checked counterexample theorems:

```text
energy_order_alone_does_not_imply_true_weakly_best
energy_order_alone_does_not_imply_true_weakly_max
```

The first theorem covers minimization-style true verifier cost. The second
covers maximization-style verifier score, such as UPBA objective encodings.

## Consequence

The model may reorder candidates to reduce search cost. It cannot authorize a
settlement from low energy, even if the low-energy candidate is first.

The authority path remains:

```text
ranked candidate order
  -> deterministic verifier checks
  -> full fallback or suffix-bound checked-stop certificate
  -> accepted candidate
```

## Verification

```bash
cd lean-mathlib && lake env lean Proofs/ZenoEnergyAdvisoryBoundary.lean
pytest -q tests/formal/test_lean_aristotle_boundary_packets.py
```

Both commands are recorded as passing in the receipt.

## Limits

This is formal negative knowledge over an abstract finite candidate model. It
does not prove model calibration, production readiness, real replay coverage, or
UPBA v2 bounded-grid completeness.
