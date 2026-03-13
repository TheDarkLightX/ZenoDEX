---
title: README
type: note
permalink: autonomous-tau-dex-review/formal/tla/readme
---

# TLA+ / TLC models (ZenoDEX)

This folder contains small, bounded TLA+ models for two different jobs:

- **liveness-level** protocol obligations (“eventually settles”, “no deadlocks”),
- **independent shadow semantics** for selected Tau guard specs, used to reduce semantic drift risk.

These models complement the repo’s safety invariants and mechanized math proofs.

## Perp epoch scheduler

Files:

- `formal/tla/PerpEpochScheduler.tla`
- `formal/tla/PerpEpochScheduler.cfg`

What it models:

- an epoch-based workflow that must **publish a clearing price** and then **settle** it,
- a v1.1-style **breaker** flag that enforces **reduce-only** position updates while active,
- a small liveness property: `clearingSeen => eventually ~clearingSeen` under weak fairness of settlement.

### Run with TLC

Install the TLA+ tools (TLC), then from the repo root:

```bash
bash tools/install_tla_tools.sh
python3 tools/run_tla_models.py
```

Notes:

- The repo does not commit the TLC jar, but `tools/install_tla_tools.sh` downloads it
  to `external/tla-tools/tla2tools.jar`.
- The release gate now runs `tools/run_tla_models.py` fail-closed, so TLC is part of
  the semantic-assurance lane.
- Bounds are intentionally tiny (`EPOCH_MAX=3`) to keep exploration fast.

## Tau shadow semantics

Files:

- `formal/tla/AutoTraderNonceGuardShadow.tla`
- `formal/tla/AutoTraderNonceGuardShadow.cfg`
- `formal/tla/AutoTraderTxEnvelopeShadow.tla`
- `formal/tla/AutoTraderTxEnvelopeShadow.cfg`
- `formal/tla/OracleFreshnessBoundedShadow.tla`
- `formal/tla/OracleFreshnessBoundedShadow.cfg`
- `formal/tla/OrderIntentCancelExpiryShadow.tla`
- `formal/tla/OrderIntentCancelExpiryShadow.cfg`
- `formal/tla/PerpSubmissionAuthScopeShadow.tla`
- `formal/tla/PerpSubmissionAuthScopeShadow.cfg`
- `formal/tla/PerpIngressSchemaShadow.tla`
- `formal/tla/PerpIngressSchemaShadow.cfg`

What they model:

- the intended meaning of selected Tau guards,
- the modeled perps submission-auth admission semantics,
- a bounded oracle freshness predicate used by modeled guard lanes,
- the cancel/expiry order lifecycle admission semantics used by the modeled
  order-intent lane,
- independently of Tau syntax and evaluation semantics,
- with small invariant sets that are pinned by `tools/check_tau_shadow_assurance.py`.

Run the fail-closed scaffolding check from the repo root:

```bash
python3 tools/check_tau_shadow_assurance.py
```

The release gate treats unresolved semantic deltas on release-blocking properties as a blocker.
