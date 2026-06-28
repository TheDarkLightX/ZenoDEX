# ZenoDEX Tau Route Split Window Breakthrough - 2026-06-28

## Executive Result

A Tau host-projected certificate can guard exact-out two-pool split routing by requiring derivative-window replay, local-window coverage, bounded full-oracle parity, integer rounding scope, resource budget, fallback, and no-authority facts.

Tau admits a split-routing certificate lane only. It does not quote pools, choose routes, or authorize settlement.

## Breakthrough Specification

- Spec: `src/tau_specs/recommended/route_split_window_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Split cases: `4`
- Quote-call reduction range: `3.41x` to `16.57x`
- Naive discrete-convex failures: `4`

The spec requires derivative-window replay, local window coverage, bounded full-oracle parity, quote replay, integer rounding scope, resource budget, fallback, exact-out scope, and no settlement authority.

## Split Evidence

| case | feasible splits | full quotes | window quotes | reduction | selected q0 | amount in | first-diff monotone |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `endpoint_best_amount2000` | `2001` | `4000` | `1172` | `3.41x` | `2000` | `3010` | `False` |
| `interior_plateau_amount5000` | `4985` | `10000` | `1300` | `7.69x` | `928` | `5464` | `False` |
| `large_endpoint_amount9000` | `8960` | `17961` | `1084` | `16.57x` | `9000` | `5151` | `False` |
| `interior_rounding_gap_amount4000` | `3980` | `7979` | `1286` | `6.20x` | `3719` | `5272` | `False` |

The failed first-difference checks are recorded as negative knowledge. The certificate accepts only because bounded full-oracle parity and quote replay pass.

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `route_split_window_pass` | `True` | All host-computed proof-surface facts admit the split-window certificate lane. |
| `parity_reject` | `True` | A missing bounded full-oracle parity fact fails closed. |
| `local_window_reject` | `True` | A missing local window certificate cannot admit. |
| `authority_reject` | `True` | A certificate with settlement authority effects is rejected. |
| `inactive_safe` | `True` | Inactive requests do not admit while the no-authority rail remains true. |

## Work Items 1 And 2

The earlier AB and CoW tracks remain in scope through `ab_cow_exact_solver_envelope_v1.tau`.

1. AB ordering: bounded full-state subset DP/brute-force proof-surface rail. Replay: `python3 tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py`.
2. CoW matching: uncoupled Hungarian assignment plus bounded coupled-capacity DP proof-surface rail. Grouped-capacity polynomial matching is not claimed.

## New Specification Frontier

- `src/tau_specs/recommended/route_split_window_certificate_v1.tau`: Gates exact-out two-pool split-window certificates and records when bounded full-oracle parity is required.
- `src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau`: Compresses route, AB, and CoW optimizer proof surfaces into domain-hash-bound certificates.
- `src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau`: Covers work items 1 and 2: AB subset-DP/brute-force and CoW exact matching proof-surface facts.

## Mutation Checks

| mutation | accepted | failed flags |
| --- | --- | --- |
| `bad_domain_hash` | `False` | `window_search_replayed` |
| `bad_selected_q0` | `False` | `window_search_replayed`, `full_oracle_parity_ok` |
| `bad_search_point_count` | `False` | `local_window_certificate_ok` |

## Non-Claims

- This artifact does not prove a universal continuous or discrete convexity theorem for integer CPMM exact-out split costs.
- The bounded full-oracle parity check is evidence for these fixtures; production verifiers still own route correctness.
- Tau does not compute quotes, hashes, derivatives, windows, or route winners.
- The AB/CoW entries are existing supported rails included to keep work items 1 and 2 in scope.

## Replay

```bash
python3 tools/zenodex_tau_route_split_window_breakthrough_20260628.py
```
