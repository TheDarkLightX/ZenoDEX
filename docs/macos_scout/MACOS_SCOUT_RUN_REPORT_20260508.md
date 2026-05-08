# MacOS Scout Run Report - 2026-05-08

## Scope

This pass continued the disaster-state minimization work after rebasing onto
`a96e633` (`Add Mac agent operating loop`). It used the local M3 Max Mac for
Julia scout runs, promoted one evidence-integrity hardening, and promoted one
runtime perps invariant with a Lean proof target.

This is bounded evidence. It is not a production safety proof and no derivative
formula is promoted.

## Machine Profile

Source: `internal/macos_scout_runs/20260508_181555_smoke/host_info.txt`.

```text
julia = julia version 1.12.6
hw.ncpu = 16
hw.memsize = 137438953472
chip = Apple M3 Max
cpu = 12 performance cores + 4 efficiency cores
gpu = 40 cores, Metal 3
memory = 128 GB
Julia threads used by scout = 12
OPENBLAS_NUM_THREADS = 1
VECLIB_MAXIMUM_THREADS = 1
OMP_NUM_THREADS = 1
```

Metal smoke was attempted:

```bash
julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl
```

Result: `Metal.jl` was not installed in this Julia environment. The CPU scout
remained the authoritative evidence path.

## Commands

Environment and syntax checks:

```bash
julia --version
bash -n tools/macos_scout/run_macos_scout.sh
python3 -m py_compile \
  tools/macos_scout/summarize_scout_outputs.py \
  tools/macos_scout/check_scout_regression_gate.py \
  tools/macos_scout/build_witness_space_receipt.py
```

Scout runs:

```bash
JULIA_NUM_THREADS=auto bash tools/macos_scout/run_macos_scout.sh smoke

JULIA_NUM_THREADS=auto \
MACOS_SCOUT_OUTDIR=internal/macos_scout_runs/20260508_181623_scout_seed20260508_fixed \
bash tools/macos_scout/run_macos_scout.sh scout

JULIA_NUM_THREADS=auto SEED=20260509 \
MACOS_SCOUT_OUTDIR=internal/macos_scout_runs/20260508_181623_scout_seed20260509_fixed \
bash tools/macos_scout/run_macos_scout.sh scout

JULIA_NUM_THREADS=auto SEED=20260512 \
MACOS_SCOUT_OUTDIR=internal/macos_scout_runs/20260508_181623_deep_seed20260512_fixed \
bash tools/macos_scout/run_macos_scout.sh deep
```

One same-second parallel launch accidentally targeted
`internal/macos_scout_runs/20260508_181623_scout` twice. That run is excluded
from this report's evidence. The runner now allocates output directories
atomically and supports explicit `MACOS_SCOUT_OUTDIR` for replay.

## Results

| Run | Seed | Candidates | Paths | Steps | Counterexamples | Zero-disaster legal shapes | Gate | Witness receipt |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `internal/macos_scout_runs/20260508_181623_scout_seed20260508_fixed` | 20260508 | 50000 | 64 | 96 | 0 | 50000 | accepted | `sha256:3cf55a9dc31294e707c0e219d335ebf258ad42d77670ef67862052a85f5e8d5a` |
| `internal/macos_scout_runs/20260508_181623_scout_seed20260509_fixed` | 20260509 | 50000 | 64 | 96 | 0 | 50000 | accepted | `sha256:3cf55a9dc31294e707c0e219d335ebf258ad42d77670ef67862052a85f5e8d5a` |
| `internal/macos_scout_runs/20260508_181623_deep_seed20260512_fixed` | 20260512 | 250000 | 96 | 128 | 0 | 250000 | accepted | `sha256:3cf55a9dc31294e707c0e219d335ebf258ad42d77670ef67862052a85f5e8d5a` |

All three fixed runs opened the witness-space receipt:

```text
gate = OPEN_FOR_BOUNDED_RESEARCH
materialized_witness_count = 65
reachable_witness_count = 0
compressed_frontier_total = 9
```

No formula passed the strict promotion gate in the fixed scout/deep runs. The
top reranked candidates still rely on nontrivial guard/clamp rates, so they
remain search evidence only.

## Promoted Hardening

### Evidence integrity

Disaster state found while using parallel compute:

```text
same-second scout launches share one timestamped output directory
  -> run artifacts can overwrite each other
  -> regression and witness receipts can bind mixed seeds
```

Reduction:

- `tools/macos_scout/run_macos_scout.sh` now allocates output directories with
  atomic `mkdir`.
- `MACOS_SCOUT_OUTDIR` allows explicit replay directories.
- `MACOS_SCOUT_ALLOCATE_ONLY=1` exposes the allocator for regression tests.

### Runtime clearinghouse invariant

The Julia scout hardening depends on oracle movement, oracle freshness, payout
caps, and liquidity guards remaining monotone while risk is live. The runtime
clearinghouse path now enforces the analogous invariant for open positions:

```text
OpenClearinghousePosition
  -> no increase to max_oracle_move_bps
  -> no increase to max_oracle_staleness_epochs
  -> no decrease to initial_margin_bps
  -> no decrease to maintenance_margin_bps
  -> no increase to max_position_abs
  -> no increase to liquidation_penalty_bps
```

This closes the live-governance loosening disaster class. Flat markets may
still update parameters after the operator and settled-epoch gates pass.

## Lean Target

Added `lean-mathlib/Proofs/PerpLiveRiskParamMonotonicity.lean`.

Formal target:

```text
LiveRiskNotLoosened(old, new)
  -> any move/staleness/position admissible under new was already admissible
     under old
  -> any initial/maintenance margin floor satisfied under old remains
     satisfied under new
  -> increasing max_oracle_move_bps contradicts the live guard
```

The target typechecks with plain Lean, without requiring the missing local
`external/mathlib4` checkout.

## Verification

Focused verification completed:

```bash
python3.11 -m pytest \
  tests/test_macos_scout_run_allocator.py \
  tests/core/test_perp_clearinghouse_market_params_guard.py \
  tests/formal/test_lean_perp_live_risk_param_monotonicity.py \
  -q
```

Result: `5 passed`.

```bash
python3.11 -m pytest \
  tests/integration/test_perp_engine_clearinghouse_2p.py \
  tests/integration/test_perp_engine_clearinghouse_3p_transfer.py \
  -q
```

Result: `26 passed`.

Additional direct Lean check:

```bash
lean lean-mathlib/Proofs/PerpLiveRiskParamMonotonicity.lean
```

Result: passed.

## Next Targets

- Lower guard-block and payout-clamp rates before promoting any formula.
- Run a second deep seed or soak after the allocator hardening is committed.
- Lift `LiveRiskNotLoosened` from the Lean target into a broader perps
  settlement theorem once the local mathlib checkout is available.
