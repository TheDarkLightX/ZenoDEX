# ZenoDEX AB/CoW Algorithm Breakthrough - 2026-06-27

## Executive Result

The core contains bounded exact AB full-state subset DP, exact Hungarian CoW assignment for the uncoupled volume/surplus objective, and bounded exact DP for small grouped-capacity CoW batches; `ab_cow_exact_solver_envelope_v1.tau` gates the proof surface and rejects overbroad capacity claims.

The Tau spec admits certificates only. It has no settlement-authorizing output.

## Tau Specification

- Spec: `src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Trace replay ok: `True`

The spec has separate modes for AB ordering and CoW matching. It requires objective binding, state/capacity scope, parity, deterministic ties, balance/slippage checks, resource budget, fallback bounds, and a no-authority rail.

## Work Item 1: AB Ordering

Core status: bounded exact full-state subset DP is active for same-direction batches above the small brute-force threshold and at or below the public fallback limit.

- Brute-force threshold: `8`
- Subset-DP public surface: `9..12 same-direction bounded batches`
- Fallback after: `12`
- Measured n=8 brute force: `4.231782s`
- Measured n=8 subset DP: `0.023111s`
- Measured n=8 speedup: `183.11x`

At n=12, the compressed Held-Karp proxy is `589824` state transitions versus `479001600` permutations, a `812.11x` reduction proxy.
The live implementation carries reserves and per-sender balances in state, so this report treats that number as a target/proxy rather than a universal runtime claim.

## Work Item 2: CoW Matching

Core status: exact Hungarian assignment is active for the uncoupled sender-balance economic objective and now encodes the brute-force lexicographic pair-id tie as a mixed-radix score layer; small grouped-capacity batches use bounded exact DP, while larger grouped-capacity batches remain outside the pure matching claim.

- Assignment surface: `uncoupled sender balances`
- Fallback surface: `capacity-coupled grouped senders use bounded exact DP up to the coupled cap, then greedy/fail-closed path`
- Tie scope: `The assignment path is exact for volume and surplus and matches the tiny brute-force lexicographic pair-id tie on the bounded oracle cases.`
- Measured 6x6 brute force: `0.013997s`
- Measured 6x6 Hungarian assignment: `0.000335s`
- Measured 6x6 speedup: `41.81x`
- Canonical tie fuzzer: `25` cases, `0` mismatches
- Measured 20x20 assignment: `0.012214s`

At balanced n=20, perfect matching enumeration has `2432902008176640000` assignments versus an `n^3` proxy of `8000`, a `3.04e+14x` proxy reduction for the uncoupled surface.

## Replay

```bash
python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py
```
