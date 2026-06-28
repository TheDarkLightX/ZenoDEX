# ZenoDEX Tau Bitvector Frontier Probe - 2026-06-28

## Executive Result

`receipt_sequence_bv16_guard_v1.tau` and `receipt_sequence_projected_guard_v1.tau` define a paired direct-vs-projected Tau probe for bounded receipt sequence checks.
The replay checked `6` Tau binaries with `0` invalid accepts and `6` behavior-equivalent direct/projected runs.

Small local bv16 sequence arithmetic is viable on current and bitblasting Tau builds, but performance is binary-sensitive; host projection remains the robust pattern for broad receipt machinery.

Authority boundary: these specs are evidence gates for receipt sequence facts. They do not authorize receipt commits, settlement, oracle updates, or governance.

## Specifications

- `src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau`: direct `bv[16]` monotonicity, max-gap, and replay-floor arithmetic.
- `src/tau_specs/recommended/receipt_sequence_projected_guard_v1.tau`: host-projected monotonicity, max-gap, and replay-floor facts.

## Tau Binary Matrix

| binary | version | direct | projected | equivalent |
| --- | --- | --- | --- | --- |
| `workspace_latest` | `Tau Language Framework version 0.7.0-alpha (401d756b)` | `fast` | `fast` | `True` |
| `workspace_runtime` | `Tau Language Framework version 0.7.0-alpha (1d4bd3a6)` | `fast` | `fast` | `True` |
| `upstream_main` | `Tau Language Framework version 0.7.0-alpha (cb9d364)` | `slow` | `slow` | `True` |
| `bitblasting` | `Tau Language Framework version 0.7.0-alpha (d0e5bd6e)` | `fast` | `fast` | `True` |
| `bitblasting_opt` | `Tau Language Framework version 0.7.0-alpha (d0e5bd6e)` | `fast` | `fast` | `True` |
| `bitblasting_cegqi_bv_default` | `Tau Language Framework version 0.7.0-alpha (d0e5bd6e)` | `fast` | `fast` | `True` |

Latency classes are buckets: `fast` <=2s, `moderate` <=10s, `slow` <=30s. Raw timings live in the generated replay JSON.

## Frontier Reading

1. Direct `bv[16]` arithmetic is now a viable Tau island for this small sequence-check family on the current and bitblasting binaries.
2. The upstream-main binary remains materially slower in this local probe, so direct arithmetic should stay profile-gated.
3. Host-projected facts remain the safer default for large receipt machinery: hashes, signatures, membership, historical windows, and receipt-chain binding.

## Non-Claims

- This does not validate arbitrary direct Tau bitvector arithmetic.
- This does not replace host receipt verification.
- This does not claim production activation for either spec.

## Replay

```bash
python3 tools/zenodex_tau_bitvector_frontier_probe_20260628.py
```
