---
title: UPBA V1 Grid Economic Profiles
type: note
permalink: autonomous-tau-dex-review/docs/upba-v1-grid-economic-profiles
---

# UPBA V1 Grid Economic Profiles

This note records the replayable economic-resolution gate for UPBA v1 price
grids. It complements the bounded-grid optimality theorem by checking whether a
chosen rational grid is fine enough for an explicit price band and maximum
per-fill input size.

The checker is `tools/upba_v1_grid_economic_profile.py`.

## Bound

For a target rational price `p` and grid denominator `D`, nearest-numerator
rounding gives:

```text
grid_step = 1 / D
epsilon_price = 1 / (2D)
abs_error(p, D) <= epsilon_price
```

For a supported price band with `p >= p_min`, the relative error bound is:

```text
relative_error_bps <= ceil(10_000 / (2D * p_min))
```

For a per-fill gross input cap `X`, the output-unit slack bound is:

```text
output_error_units <= ceil(X / (2D)) + 1
```

The `+ 1` term is the integer floor-output slack already present in the UPBA v1
certificate arithmetic.

The checker also emits exact nearest-grid witnesses for the minimum, midpoint,
and maximum rational prices in each profile. Each witness records the target
price, selected grid numerator, grid price, and exact absolute error. A profile
accepts only when those representative rational prices are within
`epsilon_price` and the minimum supported price is not below the positive grid
floor.

The machine-readable report now includes
`universal_rational_price_bound`, an explicit interval-cover certificate for
the whole declared rational price band:

```text
p_min <= p <= p_max
∧ p_min * D >= 1
∧ ceil(p_max * D) <= N
  -> exists n in [1, N], abs(p - n / D) <= 1 / (2D)
```

Plain-English reading: every rational price in the declared band has a bounded
grid numerator within the stated nearest-grid epsilon. The certificate records
the exact assumptions separately from the representative endpoint/midpoint
witnesses.

## Profiles

The built-in profiles are:

| Profile | Price Band | Grid Denominator | Max Fill Input | Relative Threshold | Output-Unit Threshold |
|---|---:|---:|---:|---:|---:|
| `production_deep_v1` | `[0.001, 10]` | `10,000,000` | `1,000,000` | `1 bps` | `2 units` |
| `production_wide_v1` | `[0.00001, 10]` | `100,000,000` | `10,000,000` | `5 bps` | `2 units` |

Both profiles also check that the required numerator at the maximum supported
price stays inside the runtime `UNIFORM_BATCH_PRICE_RATIO_MAX` domain and that
the supported price band is ordered. When the minimum supported price has a
positive grid candidate and the maximum supported price stays inside the bounded
grid numerator domain, every rational price in the declared band has a nearest
bounded-grid witness within `epsilon_price`. The representative witnesses are
kept as replayable examples for the lower bound, midpoint, and upper bound.
The report also records nonnegative margins between each profile's configured
negligibility threshold and the computed relative-error and output-unit bounds.

## Replay

```bash
python3 tools/upba_v1_grid_economic_profile.py --json
pytest -q tests/tools/test_upba_v1_grid_economic_profile.py
```

## Boundary

An accepted profile means the configured price band, denominator, and per-fill
input cap meet the profile's explicit price-epsilon, relative-error, and
output-unit thresholds.

It does not prove fair admission, rational-price search completeness outside
the declared band, market-depth sufficiency, oracle safety, or a universal
economic optimality theorem. A deployment must bind one accepted profile to its
batch-builder configuration and enforce the same price band and per-fill input
cap at runtime.
