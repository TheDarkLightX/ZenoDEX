# Tools

## Zeno Burn Demo (HTML)

Open in a browser:
```
open tools/zeno_burn_demo.html
```

This visualizes the Zeno-style burn: each step burns a fixed percentage of remaining supply.

## Tau Spec Runner (GUI)

Run:
```
python3 tools/tau_spec_runner_gui.py
```

- Choose a Tau binary (auto-detected if built in `external/tau-lang/build-Release/tau`).
- Choose a `.tau` spec.
- Paste input values line-by-line and run.

Note: Specs with long runs may take time; the GUI uses a 30s timeout.

## Tau Lang Update / Bitblasting (Internal)

Update/build Tau (default `main` into `external/tau-lang/build-Release/tau`):
```bash
tools/update_tau_lang.sh
```

Build an alternate Tau checkout into a separate build dir (useful for A/B benchmarking):
```bash
tools/update_tau_lang.sh --ref feature/bitblasting --build-dir build-Release-bitblasting
```

Recommended: keep separate clones for baseline vs experimental branches to avoid checkout conflicts:
```bash
tools/update_tau_lang.sh --ref main --tau-dir external/tau-lang --build-dir build-Release
tools/update_tau_lang.sh --ref feature/bitblasting --tau-dir external/tau-lang-bitblasting --build-dir build-Release-bitblasting
```

Current status note (as of `tau-lang` `origin/feature/bitblasting` @ `d0e5bd6e`):
- Upstream is WIP. This repo applies small local patches at build time
  (`tools/patches/tau-lang/feature-bitblasting-*.patch`) so it can execute our bv-heavy
  `.tau` specs deterministically for A/B experiments (io-var preservation + correct
  two's complement handling).
- The actual `bv_bitblasting_*` implementation on that branch is still a stub, so any
  performance deltas you observe today are primarily from simplification/rewriting, not a
  real SAT bitblaster.

Most Tau tooling in this repo supports an explicit binary override via `TAU_BIN`:
```bash
TAU_BIN=external/tau-lang-bitblasting/build-Release-bitblasting/tau bash tests/tau/test_specs_syntax.sh
```

BV microbench / regression probe (internal):
```bash
python3 tools/tau_bv_solve_bench.py \
  --a-tau-bin external/tau-lang/build-Release/tau \
  --b-tau-bin external/tau-lang-bitblasting/build-Release-bitblasting/tau \
  --steps 32 --timeout-s 10 --verify-witness
```

## Tau Frontier Explorer (Structured Frontier Search)

Searches a regret-focused Tau policy space, emits candidate `.tau` specs, and
computes a Pareto frontier over safety/regret/fill/speed/simplicity.

Run:
```bash
python3 tools/tau_frontier_explorer.py \
  --out-dir runs/tau_frontier_explorer/latest \
  --scenario-size 256 \
  --max-candidates 48
```

Optional deep Tau probe on top frontier candidates (slow/inconclusive-friendly):
```bash
python3 tools/tau_frontier_explorer.py \
  --out-dir runs/tau_frontier_explorer/probe \
  --tau-probe-top-k 3 \
  --tau-probe-steps 1 \
  --tau-probe-timeout-s 45
```

Artifacts:
- `.../candidates/*.tau` generated candidate specs
- `.../tau_frontier_report.json` full results + frontier
- `.../tau_frontier_frontier.json` frontier-only rows

## Boundary Value Analysis (BVA) Helpers (Internal)

Static BVA suggestions + optional dynamic "boundary mining":
```bash
python3 tools/bva/mine_bva.py --scenario tools/bva/scenarios/slippage_advisor_status.py --print-bva
python3 tools/bva/mine_bva.py --scenario tools/bva/scenarios/slippage_advisor_status.py --mine-boundaries
```

Global, cross-field boundary mining via pair-density MCMC:
```bash
python3 tools/bva/mine_bva.py --scenario tools/bva/scenarios/slippage_advisor_status.py --mine-mcmc
```

## GPU-Assisted Certificates (Internal)

These helpers compute winners off-chain (optionally on GPU via Torch/CuPy) and emit
Tau steps for cheap, deterministic certificate checks.

GPU backend note:
- Linux/NVIDIA uses Torch CUDA or CuPy CUDA (when installed) and `--prefer-gpu` is set.
- macOS uses Torch MPS when available.
- All results are *untrusted* until verified by deterministic replay / Tau steps.

Quick check:
```bash
python3 tools/gpu_env_check.py
```

- Argmin (key asc, index asc):
```bash
python3 tools/gpu_argmin_certificate.py --input /tmp/cands.json --output /tmp/argmin_steps.json --prefer-gpu
```
- Argmax (key desc, index asc):
```bash
python3 tools/gpu_argmax_certificate.py --input /tmp/cands.json --output /tmp/argmax_steps.json --prefer-gpu
```

## GPU Useful-Work Prototype: Route Improvement Witness (Internal)

Prototype "expensive search, cheap verification" for routing:
- Search is optionally GPU-accelerated (approx ranking with Torch/CuPy float64).
- Binding is always via deterministic integer replay in the functional core.
- Verification is a pure replay check (no trust in off-chain compute).

Generate a route-improvement witness (2-hop CPMM search):
```bash
python3 tools/gpu_jobs/route_2hop_search_cpmm.py --input /tmp/job.json --output /tmp/witness.json --prefer-gpu
```

Verify the witness deterministically:
```bash
python3 tools/proof_verifiers/route_improvement_v1.py --input /tmp/witness.json
```

Smoke test (search + verifier):
```bash
python3 tools/gpu_jobs/route_2hop_smoke.py
```

Run an improvement bounty round (select best verified submission; optional Tau argmax cert):
```bash
python3 tools/gpu_jobs/improvement_bounty_round_route_v1.py \\
  --submission alice=/tmp/witness1.json \\
  --submission bob=/tmp/witness2.json \\
  --output /tmp/round.json \\
  --emit-argmax-steps /tmp/argmax_cert.json \\
  --require-positive-improvement
```

## Perps GPU Liftoff Runner

Runs a full high-resource loop:
- GPU hazard mining (funding + pnl)
- GPU CE mining for perps kernel
- ML-driven boundary-value test generation
- mechanical-scientist campaign (M3 Max profile by default, high-resource profile optional)
- strict replay + summary metrics

Run:
```
bash tools/run_perps_gpu_liftoff.sh
```

Defaults:
- CE model: `src/kernels/dex/perp_epoch_isolated_v3.yaml`
- hazard batch: `262144`
- CE batch: `262144`
- ML-BVA max candidates/action: `400`
- ML-BVA max states: `128`
- ML-BVA UCB alpha: `1.25`

The high-resource profile used during internal evaluation is not published in
this repo. Provide a local profile path through `PERPS_LIFTOFF_CONFIG` when you
use this runner.

Override any default with env vars, for example:
```
GPU_BATCH_CE=1048576 GPU_STEPS_CE=1000 bash tools/run_perps_gpu_liftoff.sh
```
or:
```
PERPS_LIFTOFF_CONFIG=/path/to/local-perps-liftoff-profile.yaml \
ML_BVA_CASES_PER_ACTION=16 ML_BVA_ITERS_PER_ACTION=320 \
ML_BVA_MAX_CANDIDATES=600 ML_BVA_MAX_STATES=192 \
GPU_STEPS_CE=6000 bash tools/run_perps_gpu_liftoff.sh
```

## ML-Driven Boundary Test Generation

Generates replayable boundary-value tests using an adaptive UCB policy over boundary candidates
(machine-learning-driven BVA).

Portability:
- Generated test artifacts are replayable on CPU-only machines.
- `model_path` is emitted in a repo-relative form when possible, so artifacts are not tied to one developer's absolute filesystem path.

Run:
```
python3.11 tools/ml_boundary_bva.py \
  --model src/kernels/dex/perp_epoch_isolated_v3.yaml \
  --out-json tests/kernels/data/perp_epoch_isolated_v3_ml_bva_cases.json \
  --cases-per-action 12 \
  --iterations-per-action 220 \
  --max-candidates-per-action 400 \
  --max-states 128 \
  --alpha 1.25 \
  --pretty
```

Replay test:
```
python3.11 -m pytest -q tests/kernels/test_perp_epoch_isolated_v3_ml_bva_cases.py
```
