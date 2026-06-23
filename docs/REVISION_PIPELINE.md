# Revision Pipeline (Pointwise Revision)

This document describes the **safe upgrade path** for parameter changes using pointwise revision. The goal is to allow market‑driven tuning without changing core safety logic.

## Components

1) `src/tau_specs/governance_timelock_v1.tau`
- Validates proposals are delayed by a minimum timelock before execution.

2) `src/tau_specs/revision_policy_v1.tau`
- Enforces bounds + step limits on updatable parameters.
- Requires governance approval + timelock when `exec_req=1`.

3) `src/tau_specs/parameter_registry_v1.tau`
- Applies approved parameter updates; otherwise keeps current values.

## Data Flow (Minimal)

```
proposal -> governance vote -> timelock -> revision_policy -> parameter_registry -> settlement
```

## Update Rules
- **Immutable invariants** are not modified by revision.
- Only **parameters** (rates, caps, floors, thresholds, weights) are changed.
- Each update must satisfy:
  - min/max bounds
  - step‑size limits (bounded drift)
  - timelock delay
  - governance approval

## Recommended Governance Policy
- Timelock: 24–72 hours minimum
- Supermajority for large changes (e.g., >1% fee shift)
- Emergency pause only with strict sunset conditions

## Integration Notes
- Feed `revision_policy_v1.tau` with **current** and **proposed** values.
- Use `parameter_registry_v1.tau` outputs as the *only* parameter source for:
  - fee rate
  - buyback share
  - rebate rate
  - supply floor
  - unit scale
  - lock tiers + weights

## Safety Guarantee
As long as the settlement spec consumes parameters **only from the registry**, updates cannot bypass the revision policy.
