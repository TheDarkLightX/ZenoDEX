---
title: math_object_innovation_v193
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v193
---

# v193 Evidence-Meet Fee-Cap Lattice

## Structural Target

```text
evidence_meet_fee_cap_lattice_v1
```

This cycle composes the v190, v191, and v192 fee-cap recommendation artifacts.
The structural object is the meet cap:

```text
MeetCap(surface) := min { cap(source, surface) such that cap exists }
```

In plain English: when multiple evidence sources recommend a review cap for the
same surface, the composed cap is the most conservative one.

## Bounded Domain

Sources:

- `v190_fixture`
- `v191_stress`
- `v192_execution`

The union contains `16` named surfaces:

- `6` user-value cap surfaces,
- `2` execution-backed surfaces,
- `4` synthetic-only cap surfaces,
- `10` non-user-cap surfaces after rejected, penalty, or protocol-surplus
  classifications are included.

## Acceptance Rules

```text
MeetNeverLoosens:
  MeetCap(surface) <= cap(source, surface)
```

In plain English: adding another evidence source cannot loosen the composed cap
because the composed cap is the minimum of all available caps.

```text
NoLaunchClaim:
  launch_parameter_claim = false
```

In plain English: the evidence meet remains a review artifact, not a production
fee schedule.

## Claim Tier

```text
tier = symbolic_state_compiler
oracle_dependent = true
```

The meet compiler is exact over the upstream recommendation artifacts, but the
upstream artifacts still depend on measured-value receipts and fixture markets.

## Replay

```bash
python3 experiments/math_object_innovation_v193/run_cycle.py
pytest -q experiments/math_object_innovation_v193/test_v193_cycle.py
cd lean-mathlib && lake env lean Proofs/RevenueSurfaceSafety.lean
```

## Current Result

```text
surface_count = 16
meet_cap_surface_count = 6
execution_backed_meet_count = 2
synthetic_meet_count = 4
single_source_cap_count = 0
no_user_value_cap_count = 10
total_meet_invariant_failures = 0
```

Execution-backed meet caps:

```text
route_surplus_capture = 1800 bps
exact_out_savings_capture = 2000 bps
```

The execution fixtures produce higher review caps for both surfaces than the
stress corpus. The meet keeps the lower stress caps and records this as
execution-stress tension, not as permission to loosen the fee schedule.
