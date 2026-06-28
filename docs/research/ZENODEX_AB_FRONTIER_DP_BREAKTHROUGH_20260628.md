# ZenoDEX AB Frontier-DP Boundary - 2026-06-28

## Executive Result

A dominance-pruned full-state frontier DP preserves brute-force AB ordering on bounded exact-in same-direction CPMM cases, but the bounded replay shows no final state-count reduction versus the existing full-state DP. Tau admits only the replayed research certificate facts.

No production ordering path changes; host/kernel verifiers remain authoritative for clearing and settlement.

## Tau Specification

- Spec: `src/tau_specs/recommended/ab_frontier_dp_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau cases: `6`
- Invalid accepts: `0`

The Tau spec requires scope, brute-force parity, full-state parity, dominance no-loss evidence, observed dominance pruning, deterministic ties, negative replay, resource budget, fallback, advisory-only status, and no-authority facts.

## Bounded Oracle Results

- Cases: `5`
- Full-state DP states: `4307`
- Frontier DP states: `4307`
- State reduction: `0`
- Dominated prunes: `7927`

The safe dominance rule rejected dominated candidates, but the existing full-state DP already converged to the same final state count on these bounded fixtures. That makes the rule a research boundary rather than a production optimization candidate.

| n | variant | ok | full states | frontier states | reduction | brute time | frontier time |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `5` | `0` | `True` | `58` | `58` | `0` | `0.012060s` | `0.004088s` |
| `6` | `1` | `True` | `249` | `249` | `0` | `0.089931s` | `0.022617s` |
| `7` | `4` | `True` | `790` | `790` | `0` | `0.569601s` | `0.104957s` |
| `8` | `3` | `True` | `1800` | `1800` | `0` | `4.325578s` | `0.170248s` |
| `8` | `7` | `True` | `1410` | `1410` | `0` | `4.126682s` | `0.129423s` |

## Negative Replay

A one-record-per-subset Held-Karp DP is not sound for the current AB objective under integer CPMM semantics.
The replayed counterexample loses `32` units of primary AB amount under unsafe one-record compression.

## Non-Claims

- This is an exact-in same-direction CPMM certificate experiment, not a proof for mixed directions or exact-out batches.
- This does not replace the production AB ordering path.
- This does not revive one-record-per-subset Held-Karp compression; the negative replay remains required evidence.
- Observed dominance pruning did not reduce final DP state count on these fixtures, so this is negative knowledge for production optimization.

## Replay

```bash
python3 tools/zenodex_ab_frontier_dp_breakthrough_20260628.py
```
