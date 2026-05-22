---
title: math_object_innovation_v194
type: note
permalink: autonomous-tau-dex-review/experiments/math-object-innovation-v194
---

# v194 Evidence-Meet Launch Config Guard

## Structural Target

```text
evidence_meet_launch_config_guard_v1
```

This cycle compiles the v193 evidence-meet fee caps into a bounded launch/config
lint rule:

```text
LaunchFeeOK(surface) :=
  fee_bps(surface) <= MeetCap(surface)
  OR AssumptionChangeOverride(surface)
```

In plain English: a proposed fee surface is accepted by the lint rule only when
it stays under the evidence meet, or when governance explicitly records that it
is changing assumptions and cannot claim the v193 user-net guarantee.

## Bounded Domain

Input cap source:

- `experiments/math_object_innovation_v193/generated/meet_rows.json`

Candidate configs:

- `10` named launch/config candidates,
- `18` surface-level fee checks,
- capped surfaces, over-cap surfaces, unknown surfaces, malformed overrides,
  redundant overrides, and mixed safe/override configs.

## Acceptance Rules

```text
EvidenceCompliant(config) :=
  every checked surface has fee_bps <= MeetCap(surface)
```

In plain English: a config can claim evidence-compliant fee safety only when
every fee line is below its evidence-meet cap.

```text
OverCapAccepted(surface) -> AssumptionChangeOverride(surface)
```

In plain English: if an over-cap or uncapped fee line is accepted at all, it
must carry a governance-approved assumption-change record and must acknowledge
that the v193 user-net claim no longer applies.

## Claim Tier

```text
tier = symbolic_state_compiler
oracle_dependent = true
```

The checker is exact over the bounded config corpus and v193 cap artifact. It
does not prove that the v193 cap inputs are economically complete.

## Replay

```bash
python3 experiments/math_object_innovation_v194/run_cycle.py
pytest -q experiments/math_object_innovation_v194/test_v194_cycle.py
cd lean-mathlib && lake env lean Proofs/RevenueSurfaceSafety.lean
```

## Current Result

```text
config_count = 10
surface_check_count = 18
accepted_without_override_count = 2
accepted_with_override_count = 3
rejected_count = 5
evidence_compliant_config_count = 2
governance_assumption_change_count = 3
total_config_invariant_failures = 0
```

The practical result is a sharper boundary between two very different states:

- under-meet configs can claim the current evidence-backed user-net cap;
- over-meet or uncapped configs can only proceed as explicit assumption-change
  reviews, not as proof-backed safe fee schedules.
