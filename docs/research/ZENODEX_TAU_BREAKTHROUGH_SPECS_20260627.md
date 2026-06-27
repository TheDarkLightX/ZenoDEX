# ZenoDEX Tau Breakthrough Specifications - 2026-06-27

## Executive Result

The breakthrough is `frontier_certificate_menu_v1`: Shared one-hot certificate menu for route, oracle, and AB/CoW optimizer envelopes.
It turns frontier optimizers into a shared Tau-facing certificate menu: the host proves search, interval, rounding, replay, and capacity facts; Tau checks one-hot mode selection, non-vacuity, coverage, budget, fallback, and no-authority rails.

Authority boundary: these specs guard proof surfaces and research candidates. They do not authorize settlement, oracle updates, or governance by themselves.

## Tau Builds

- `latest`: `/home/trevormoc/Downloads/Autonomous Tau DEX/external/tau-lang/build-Release/tau`
  - `Tau Language Framework version 0.7.0-alpha (401d756b)`
- `runtime`: `/home/trevormoc/Downloads/Autonomous Tau DEX/external/tau-lang-bitblasting-prev-eea8fb1f/build-Release/tau`
  - `Tau Language Framework version 0.7.0-alpha (1d4bd3a6)`

## New Specifications

| spec | track | latest | runtime | elapsed latest | energy | bytes |
| --- | --- | --- | --- | ---: | ---: | ---: |
| `frontier_certificate_menu_v1` | `shared_tau_frontier` | `True` | `True` | `1.383867s` | `-106.3340` | `2208` |
| `route_dominance_frontier_envelope_v1` | `ZB-20260627-02` | `True` | `True` | `0.994831s` | `-103.6760` | `2287` |
| `oracle_polytope_frontier_envelope_v1` | `ZB-20260627-03` | `True` | `True` | `0.913455s` | `-95.3980` | `2351` |
| `ab_cow_exact_solver_envelope_v1` | `algorithm_items_1_and_2` | `True` | `True` | `2.145966s` | `-82.4760` | `3062` |

## What Tau Language Can Do Here

1. Encode compact optimizer certificate menus with one-hot mode selection and fail-closed admission.
2. Combine 9 to 10 host-projected proof facts per step without embedding route search, interval arithmetic, hashes, or matching inside Tau.
3. Expose mode-specific diagnostic outputs, so a failed candidate tells reviewers whether the gap is coverage, replay, authority, capacity, or external assumptions.
4. Keep high-complexity algorithms out of Tau while still requiring every accepted optimizer to carry a small, replayable proof-surface packet.

## Breakthrough Specification

`frontier_certificate_menu_v1` ranked first under `tau_spec_ebrm_v1`.

```text
host verifier facts + one-hot optimizer mode + no-authority rail -> Tau certificate admit
```

The practical consequence is a reusable certificate layer: route dominance, oracle parameter intervals, AB ordering, and CoW matching can share the same Tau admission shape while preserving their own host/kernel verifiers.

## Work Items 1 And 2

### 1. AB Ordering

`ab_cow_exact_solver_envelope_v1` adds a Tau rail for the existing AB full-state subset DP/brute-force path. It requires objective binding, full-state or bounded-search facts, parity, deterministic tie handling, balance/slippage checks, budget checks, fallback bounds, and no settlement authority.

### 2. CoW Matching

The same spec covers the exact CoW assignment subcase. It admits only the uncoupled-capacity surface and rejects grouped sender-capacity cases unless the host treats them as a separate bounded search or fail-closed fallback.

## Track-Specific Notes

### `frontier_certificate_menu_v1`

Shared one-hot certificate menu for route, oracle, and AB/CoW optimizer envelopes.

Formal obligations:
- Each mode flag maps to exactly one host verifier surface.
- Coverage and replay facts are produced by deterministic host/kernel checks.
- No accepted menu output has authority to mutate settlement state by itself.

Non-claims:
- Does not prove the underlying optimizer is globally correct.
- Does not replace route, oracle, AB, or CoW host verifiers.

### `route_dominance_frontier_envelope_v1`

Tau envelope for the #1 route-dominance track: pruned-label cover plus full-domain projection-cover binding.

Formal obligations:
- Dominance relation is sound under integer CPMM fee and rounding semantics.
- Every pruned label has a kept dominating witness.
- Projection cover links the selected domain back to the full bounded route domain.
- Argmin stream certificate selects the canonical winner among kept labels.

Non-claims:
- Does not compute route dominance in Tau.
- Does not certify unbounded route domains.

### `oracle_polytope_frontier_envelope_v1`

Tau envelope for the #2 oracle-polytope track: interval feasibility, point-verifier parity, boundary walls, and disclosed assumptions.

Formal obligations:
- Honest challenge profitability holds over the declared interval.
- Frivolous dispute deterrence holds over the declared interval.
- Slash coverage exceeds cheat gain plus declared margin over the interval.
- Every accepted interval is pointwise-parity checked against the existing verifier.

Non-claims:
- Does not estimate MEV or challenge probability inside Tau.
- Does not authorize oracle updates.

### `ab_cow_exact_solver_envelope_v1`

Tau envelope for work items 1 and 2: AB full-state subset DP and CoW uncoupled exact assignment.

Formal obligations:
- AB full-state DP state includes processed set, reserves, and sender balances.
- CoW assignment is only claimed for uncoupled sender capacities.
- Capacity-coupled CoW batches remain on bounded exact search or fail-closed fallback.
- Objective and deterministic tie key are host-bound.

Non-claims:
- Does not make grouped-capacity CoW polynomial.
- Does not remove the fallback path when state caps are exceeded.

## EBRM Ranking

| method | order |
| --- | --- |
| `tau_spec_ebrm_v1` | `frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1, oracle_polytope_frontier_envelope_v1, ab_cow_exact_solver_envelope_v1` |
| `highest_value` | `frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1, oracle_polytope_frontier_envelope_v1, ab_cow_exact_solver_envelope_v1` |
| `most_projected_facts` | `oracle_polytope_frontier_envelope_v1, route_dominance_frontier_envelope_v1, ab_cow_exact_solver_envelope_v1, frontier_certificate_menu_v1` |
| `grammar_minimal` | `frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1, oracle_polytope_frontier_envelope_v1, ab_cow_exact_solver_envelope_v1` |

`tau_spec_ebrm_v1` is deterministic and advisory. It uses hard Tau trace results, profile budget, source size, definition count, value score, novelty score, and projected-fact coverage.

## Refutation Plan

- Route dominance: compare dominance-pruned exact-out winners against the full bounded oracle on <=5 pools, then require every pruned label to have a kept dominating witness under integer rounding.
- Oracle polytope: sample every accepted interval wall and reject if any point passes the interval compiler but fails the existing point verifier.
- AB/CoW: keep brute-force parity for small AB batches and reject pure matching claims whenever grouped sender capacities are present.

## Replay

```bash
python3 tools/zenodex_tau_breakthrough_specs_20260627.py
```

