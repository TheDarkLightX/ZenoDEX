# TLA+ / TLC models (ZenoDEX)

This folder contains small, bounded TLA+ models for **liveness-level** protocol obligations
(“eventually settles”, “no deadlocks”), complementing the repo’s safety invariants and mechanized
math proofs.

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
tlc -config formal/tla/PerpEpochScheduler.cfg formal/tla/PerpEpochScheduler.tla
```

Notes:

- This repo does not vendor TLC; the check is optional unless you install the toolchain.
- Bounds are intentionally tiny (`EPOCH_MAX=3`) to keep exploration fast.

