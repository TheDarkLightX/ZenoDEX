# ZenoDEX Route Split Window Adversarial Corpus - 2026-06-28

## Executive Result

The route_split_window_certificate_v1 Tau rail can admit host-projected exact-out two-pool split-window certificates across this deterministic adversarial corpus when bounded full-oracle parity, quote replay, local window coverage, resource bounds, fallback, exact-out scope, and no-authority facts all hold.

- Cases: `24`
- Full/window mismatches: `0`
- Winner kinds: `interior, left_endpoint, right_endpoint`
- First-difference monotonicity failures: `24`
- Quote-call reduction range: `3.41x` to `16.93x`
- Total quote calls: full sweep `255007`, windowed `27553`
- Tau replay ok: `True`

## Why This Matters

The earlier route-split report showed four showcase fixtures. This corpus broadens the evidence across endpoint, interior, fee-skewed, shallow/deep, zero-endpoint, and near-tie regimes. Every fixture is checked against a bounded full-sweep oracle before Tau admits the certificate lane.

The first-difference failures are retained as negative knowledge: integer CPMM rounding is not a safe basis for a pure discrete-convex shortcut here. The supported pattern is host-computed replay facts plus a Tau no-authority certificate gate.

## Case Table

| case | winner | feasible splits | full quotes | window quotes | reduction | q0 | amount in | first-diff monotone |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `endpoint_low_fee_v0` | `right_endpoint` | `2001` | `4000` | `1172` | `3.41x` | `2000` | `3010` | `False` |
| `endpoint_low_fee_v1` | `right_endpoint` | `2046` | `4090` | `1103` | `3.71x` | `2045` | `2977` | `False` |
| `endpoint_low_fee_v2` | `right_endpoint` | `2167` | `4335` | `1101` | `3.94x` | `2169` | `2921` | `False` |
| `interior_plateau_v0` | `interior` | `4985` | `10000` | `1300` | `7.69x` | `928` | `5464` | `False` |
| `interior_plateau_v1` | `interior` | `5031` | `10090` | `1300` | `7.76x` | `1067` | `5650` | `False` |
| `interior_plateau_v2` | `interior` | `5159` | `10338` | `1300` | `7.95x` | `1405` | `6110` | `False` |
| `large_endpoint_v0` | `right_endpoint` | `8960` | `17961` | `1084` | `16.57x` | `9000` | `5151` | `False` |
| `large_endpoint_v1` | `right_endpoint` | `9006` | `18051` | `1084` | `16.65x` | `9045` | `5180` | `False` |
| `large_endpoint_v2` | `right_endpoint` | `9131` | `18299` | `1084` | `16.88x` | `9169` | `5258` | `False` |
| `rounding_gap_v0` | `interior` | `3980` | `7979` | `1286` | `6.20x` | `3719` | `5272` | `False` |
| `rounding_gap_v1` | `interior` | `4025` | `8069` | `1286` | `6.27x` | `3836` | `5166` | `False` |
| `rounding_gap_v2` | `right_endpoint` | `4149` | `8317` | `1089` | `7.64x` | `4169` | `4899` | `False` |
| `fee_skew_v0` | `interior` | `3493` | `6992` | `1295` | `5.40x` | `3240` | `4181` | `False` |
| `fee_skew_v1` | `interior` | `3537` | `7081` | `1294` | `5.47x` | `3352` | `4183` | `False` |
| `fee_skew_v2` | `right_endpoint` | `3660` | `7328` | `1097` | `6.68x` | `3669` | `4182` | `False` |
| `deep_shallow_v0` | `right_endpoint` | `6432` | `12931` | `1079` | `11.98x` | `6500` | `2627` | `False` |
| `deep_shallow_v1` | `right_endpoint` | `6477` | `13021` | `1079` | `12.07x` | `6545` | `2669` | `False` |
| `deep_shallow_v2` | `right_endpoint` | `6603` | `13271` | `1080` | `12.29x` | `6669` | `2781` | `False` |
| `zero_endpoint_v0` | `left_endpoint` | `6979` | `14000` | `847` | `16.53x` | `0` | `5650` | `False` |
| `zero_endpoint_v1` | `left_endpoint` | `7025` | `14090` | `847` | `16.64x` | `0` | `5846` | `False` |
| `zero_endpoint_v2` | `left_endpoint` | `7151` | `14338` | `847` | `16.93x` | `0` | `6379` | `False` |
| `balanced_tie_pressure_v0` | `interior` | `5001` | `10000` | `1300` | `7.69x` | `2523` | `6655` | `False` |
| `balanced_tie_pressure_v1` | `interior` | `5046` | `10090` | `1300` | `7.76x` | `2634` | `6730` | `False` |
| `balanced_tie_pressure_v2` | `interior` | `5168` | `10336` | `1299` | `7.96x` | `2963` | `6909` | `False` |

## Mutation Checks

| mutation | accepted | failed flags |
| --- | --- | --- |
| `bad_domain_hash` | `False` | `window_search_replayed` |
| `bad_selected_q0` | `False` | `window_search_replayed`, `full_oracle_parity_ok` |
| `bad_amount_in_total` | `False` | `window_search_replayed`, `full_oracle_parity_ok` |
| `bad_search_point_count` | `False` | `local_window_certificate_ok` |

## Tau Specification Boundary

`src/tau_specs/recommended/route_split_window_certificate_v1.tau` remains a host-projected proof-surface gate. The host computes quotes, hashes, full-sweep parity, local-window coverage, and resource facts. Tau combines those facts and preserves the no-settlement-authority rail.

## Non-Claims

- This replay does not prove universal discrete convexity or pure ternary-search correctness.
- The bounded full-sweep oracle is a research certificate surface for these fixtures.
- Tau combines host-projected boolean facts only; it does not compute quotes, derivatives, hashes, or settlements.

## Replay

```bash
python3 tools/check_route_split_window_adversarial.py
```
