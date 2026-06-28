# ZenoDEX AB Zero-Min Economic Compression Certificate - 2026-06-28

## Executive Result

A counterexample-salvage certificate supports one-record min-reserve-out compression only for the zero-min same-direction exact-in economic AB key, while preserving explicit witnesses against canonical-tie, nonzero-min, and aggregate-input overclaims.

Tau admits a research certificate only. It does not compute swaps, run DP, select AB orders, or authorize settlement.

## Evidence Summary

- Zero-min economic parity cases: `50`
- Economic mismatches: `0`
- Canonical tie mismatches: `1`
- Nonzero-min counterexample found: `True`
- Rounding path-dependence witness found: `True`

First canonical-tie mismatch:

```json
{
  "brute_economic_key": [
    260,
    296
  ],
  "brute_order": [
    "2f44",
    "2f46",
    "2f47",
    "2f49",
    "2f4b",
    "2f4a",
    "2f45",
    "2f48"
  ],
  "compressed_economic_key": [
    260,
    296
  ],
  "compressed_order": [
    "2f44",
    "2f47",
    "2f49",
    "2f46",
    "2f4b",
    "2f4a",
    "2f45",
    "2f48"
  ],
  "full_economic_key": [
    260,
    296
  ],
  "n": 8,
  "ok": true,
  "same_canonical_order": false,
  "variant": 21
}
```

Nonzero-min boundary witness:

```json
{
  "brute_economic_key": [
    39,
    1
  ],
  "brute_order": [
    "283d",
    "283c"
  ],
  "compressed_economic_key": [
    -1,
    -1
  ],
  "compressed_order": [],
  "counterexample_found": true,
  "n": 2,
  "pattern": "cliff",
  "reason": "Nonzero minimum-output cliffs can make the min-reserve-out representative infeasible while another order still executes value.",
  "variant": 3
}
```

The supported surface is economic-key only: `(executed_input, surplus)`. Canonical tie order remains outside the compressed DP.

## Tau Specification

- Spec: `src/tau_specs/recommended/ab_zero_min_economic_compression_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Certificate ok: `True`

## Certificate Flags

| flag | value |
| --- | ---: |
| `brute_or_full_parity_ok` | `1` |
| `canonical_tie_nonclaim_witness_ok` | `1` |
| `deterministic_replay_ok` | `1` |
| `economic_parity_ok` | `1` |
| `no_authority_effect` | `1` |
| `nonzero_min_boundary_witness_ok` | `1` |
| `resource_budget_ok` | `1` |
| `rounding_path_dependence_witness_ok` | `1` |
| `same_direction_exact_in_scope_ok` | `1` |
| `zero_min_scope_ok` | `1` |

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `zero_min_pass` | `True` | All scoped economic-compression evidence and boundary witnesses hold. |
| `missing_zero_min_reject` | `True` | Missing zero-min scope fails closed. |
| `missing_economic_parity_reject` | `True` | Missing economic-key parity fails closed. |
| `missing_tie_nonclaim_reject` | `True` | Missing canonical-tie nonclaim witness fails closed. |
| `missing_nonzero_boundary_reject` | `True` | Missing nonzero-min boundary witness fails closed. |
| `missing_rounding_boundary_reject` | `True` | Missing rounding path-dependence witness fails closed. |
| `authority_reject` | `True` | Authority-bearing certificates are rejected. |
| `inactive_safe` | `True` | Inactive certificates do not admit while the no-authority rail remains true. |

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_zero_min_reject` | `False` | Missing zero-min scope fails closed. |
| `missing_economic_parity_reject` | `False` | Missing economic-key parity fails closed. |
| `missing_tie_nonclaim_reject` | `False` | Missing canonical-tie nonclaim witness fails closed. |
| `missing_nonzero_boundary_reject` | `False` | Missing nonzero-min boundary witness fails closed. |
| `missing_rounding_boundary_reject` | `False` | Missing rounding path-dependence witness fails closed. |
| `authority_reject` | `False` | Authority-bearing certificates are rejected. |

## Non-Claims

- This is a research certificate, not a production ordering change.
- The compressed DP preserves the economic AB key only on the tested zero-min exact-in scope.
- The compressed DP does not preserve canonical tie order; a separate tie resolver is required.
- Nonzero min_amount_out batches are outside this compression surface.
- Tau does not compute swaps, run DP, select orders, or authorize settlement.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_zero_min_economic_compression_certificate.py
```
