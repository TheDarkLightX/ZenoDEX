---
title: README
type: note
permalink: autonomous-tau-dex-review/tools/readme
---

# Tools

## Zeno Oracle Pre-MVP CLI

Local-only reporter/validator wrapper:
```bash
tools/zenodex-oracle --json version
tools/zenodex-oracle init --home /tmp/zenodex-oracle
tools/zenodex-oracle identity create --home /tmp/zenodex-oracle
tools/zenodex-oracle query register \
  --home /tmp/zenodex-oracle \
  --base-asset AGRS \
  --quote-asset ZDEX \
  --asset-class crypto \
  --evidence-floor O3 \
  --reward-budget-e8 100000000
tools/zenodex-oracle query fund \
  --home /tmp/zenodex-oracle \
  --query-id sha256:... \
  --amount-e8 100000000
tools/zenodex-oracle query status \
  --home /tmp/zenodex-oracle \
  --query-id sha256:...
tools/zenodex-oracle query status --home /tmp/zenodex-oracle --all
tools/zenodex-oracle reporter register \
  --home /tmp/zenodex-oracle \
  --query-id sha256:... \
  --required-bond-e8 100000000
tools/zenodex-oracle reporter bond \
  --home /tmp/zenodex-oracle \
  --amount-e8 100000000
tools/zenodex-oracle reporter list --home /tmp/zenodex-oracle --active-only
tools/zenodex-oracle reporter deactivate \
  --home /tmp/zenodex-oracle \
  --reporter-id sha256:...
tools/zenodex-oracle source register \
  --home /tmp/zenodex-oracle \
  --source-id source:cex-a \
  --source-kind cex \
  --control-group-id control:cex-a \
  --venue-id venue:cex-a \
  --data-family-id price:cex-last-trade \
  --transport-id api:https:cex-a \
  --asset-class crypto \
  --query-id sha256:... \
  --assurance-class S3
tools/zenodex-oracle source list --home /tmp/zenodex-oracle --active-only
tools/zenodex-oracle report dry-run \
  --query-id sha256:... \
  --price-e8 123456789 \
  --source-observed-epoch 1000 \
  --reporter-id reporter:alice \
  --source-id source:manual
tools/zenodex-oracle report submit \
  --home /tmp/zenodex-oracle \
  --query-id sha256:... \
  --price-e8 123456789 \
  --source-observed-epoch 1000 \
  --source-id source:manual
tools/zenodex-oracle aggregate build \
  --home /tmp/zenodex-oracle \
  --query-id sha256:...
tools/zenodex-oracle read accept \
  --home /tmp/zenodex-oracle \
  --aggregate-id sha256:... \
  --consumer-module zenodex.zusd \
  --profile-id critical-zusd-v1
tools/zenodex-oracle authorization build \
  --home /tmp/zenodex-oracle \
  --read-id sha256:... \
  --action-kind mint \
  --action-id sha256:... \
  --action-facts-hash sha256:... \
  --pre-state-hash sha256:... \
  --min-evidence-class O3
tools/zenodex-oracle rewards inspect --home /tmp/zenodex-oracle
tools/zenodex-oracle rewards pay --home /tmp/zenodex-oracle --amount-e8 10000
tools/zenodex-oracle dispute open \
  --home /tmp/zenodex-oracle \
  --report-id sha256:... \
  --reporter-id sha256:... \
  --bond-e8 10000000 \
  --reason bad-source
tools/zenodex-oracle dispute resolve \
  --home /tmp/zenodex-oracle \
  --dispute-id sha256:... \
  --outcome upheld \
  --slash-e8 100000000
tools/zenodex-oracle verify local-state --home /tmp/zenodex-oracle
tools/zenodex-oracle verify receipt /tmp/receipt.json
tools/zenodex-oracle verify authorization authorization_payload.json
tools/zenodex-oracle verify evidence --skip-lean
tools/zenodex-oracle validator replay --home /tmp/zenodex-oracle
tools/zenodex-oracle validator receipt /tmp/receipt.json
tools/zenodex-oracle validator authorization authorization_payload.json
tools/zenodex-oracle dashboard snapshot --home /tmp/zenodex-oracle
tools/zenodex-oracle serve --home /tmp/zenodex-oracle --host 127.0.0.1 --port 8787
tools/zenodex-oracle serve --home /tmp/zenodex-oracle --allow-writes
```

Build a local reporter/validator release bundle with the official ZenoOracle
icons and a hash-pinned manifest:

```bash
python3 tools/build_zenodex_oracle_release.py --out-dir dist --zip
```

The default bundle is `python-local-bundle`: it ships the CLI, launcher script,
official ZenoOracle assets, and manifest, but it still depends on a local
Python runtime. The manifest records `native_binary` under `not_claimed`.

To build an easier-to-install native reporter/validator binary, run the builder
from an environment with PyInstaller:

```bash
python3 -m venv .venv-oracle-build
.venv-oracle-build/bin/python -m pip install 'pyinstaller>=6,<7'
.venv-oracle-build/bin/python tools/build_zenodex_oracle_release.py \
  --out-dir dist \
  --zip \
  --native-binary
```

Native bundles use `bin/zenodex-oracle` as the entrypoint and the binary reports
`build_target: native-binary` from `zenodex-oracle --json version`. On Linux,
PyInstaller ignores the icon metadata for the executable itself, but the
official ZenoOracle icon and favicon are still bundled and hash-pinned in the
manifest. The native bundle remains pre-MVP and non-authoritative; it does not
claim a production Oracle network.

Check public canonicalization vectors for cross-language Oracle ports:

```bash
python3 tools/check_zeno_oracle_canonicalization_vectors.py --json
```

This is not a production Oracle node. It is a deterministic pre-MVP entrypoint
for local identity setup, reporter registration, local bond/reward accounting,
source registration, query inspection and funding, report dry-runs/submission,
aggregate/read receipts, terminal `OracleAuthorization` bundles with receipt
graph roots, local disputes and slashes, typed `OracleAuthorization` checks, and
internal evidence replay.

Submitted reports bind their attached reporter/source snapshots with
`reporter_state_hash` and `source_state_hash`. Replay recomputes those
commitments before accepting the log, so mutating a reporter control group,
source venue, data family, transport, or source-control group after report
submission is rejected even if the signed price fields are unchanged.

The local dashboard API is read-only and non-authoritative. It serves JSON for
the UI under paths such as `/api/oracle/dashboard`, `/api/oracle/feeds`,
`/api/oracle/reporters`, `/api/oracle/sources`, `/api/oracle/disputes`,
`/api/oracle/rewards`, `/api/oracle/aggregates`,
`/api/oracle/accepted-reads`, `/api/oracle/authorizations`, and
`/api/oracle/replay`. The read-only route
`/api/oracle/verify-receipt?id=sha256:...` resolves a stored receipt and runs
the same standalone receipt verifier used by the CLI. Each response includes
`production_authority: false`; the API is a local operator console, not a
production oracle node.

Reward accounting and upheld slashes also emit replayable receipts. `rewards
inspect` and `rewards pay` write
`zeno_oracle.reward_ledger_entry.v1` receipts under `receipts/rewards`, while
`dispute resolve --outcome upheld` writes a
`zeno_oracle.slash_settlement.v1` receipt under `receipts/slashes`. Those
receipts are covered by the standalone verifier, the local
`/api/oracle/verify-receipt` lookup, and the public canonicalization vector
ratchet. Dashboard snapshots expose these as `recent_reward_receipts` and
`recent_slash_receipts` so the UI can surface the exact replayable artifacts
behind payouts and penalties.

`verify local-state` also scans stored receipt files under `receipts/` and
fails if any report, aggregate, read, authorization, reward, or slash receipt is
tampered or saved under a filename that does not match its semantic ID. Report,
aggregate, read, and authorization receipts must also appear in their event
logs; slash receipts must match an upheld dispute resolution; reward receipts
must reference a reporter present in the reward ledger.

Local operator writes are disabled unless `serve` is started with
`--allow-writes`. With that flag, the local API accepts POSTs for
`/api/oracle/identity/create`, `/api/oracle/reporter/register`,
`/api/oracle/reporter/bond`, `/api/oracle/query/register`,
`/api/oracle/query/fund`, `/api/oracle/source/register`,
`/api/oracle/rewards/pay`, `/api/oracle/dispute/open`,
`/api/oracle/dispute/resolve`, `/api/oracle/aggregate/build`,
`/api/oracle/read/accept`, `/api/oracle/authorization/build`, and
`/api/oracle/report/submit`.
The report endpoint is for reporter onboarding demos after identity, reporter,
bond, query, and source setup are complete. These endpoints are deliberately
scoped to local operator setup and reuse the same deterministic CLI admission
and accounting paths. Aggregate, read, and authorization builders emit the same
receipt artifacts as their CLI equivalents and remain non-authoritative local
operator helpers.

Feed registration already carries future-market metadata: `asset_class`,
`query_type`, `jurisdiction`, `market_hours_policy_id`, and
`valuation_policy_id`. Crypto and stablecoin feeds can use `always-open-v1`;
equity, RWA, real-estate, FX, and commodity feeds can be registered as devnet
or policy-draft feeds until their source and valuation policies are production
ready.

Feeds can stay on the lightweight `source-policy:declared-diverse-v1` lane for
devnet work, where diversity means distinct declared source IDs and reporter
control groups. A stronger `source-policy:registered-diverse-v1` lane requires
each report to carry an active source-registry snapshot. Aggregation then checks
that every snapshot matches the report's source ID, has non-empty registered
source dimensions, and that source IDs, source control groups, venues, data
families, and transports are all distinct before an O3 aggregate can be built.
This still does not prove hidden beneficial ownership is absent; it proves the
accepted reports satisfy the registered source-control policy the Oracle can
actually verify.

For feeds that need stricter separation, `source-policy:registered-independent-v1`
adds one more check: reporter control groups and source control groups must not
overlap inside the aggregate. This is useful for high-assurance feeds where a
reporter should not be reporting from a source it also controls.

Critical profiles fail before authorization if their aggregate evidence is below
`O3`. The CLI treats `critical` as a profile-token, so both
`critical-zusd-v1` and `profile:zusd-critical-o3-v1` are critical. Lower-evidence
reads can still be created for explicitly non-critical devnet/advisory profiles,
but `authorization build` defaults to `--min-evidence-class O3`.

Open or upheld disputes quarantine their report inputs. A read cannot be
accepted from an aggregate that includes a quarantined report, an authorization
cannot be built from an old read backed by that aggregate, and
`verify local-state` replays old accepted reads/authorizations against the
current dispute state. Receipt graphs bind `dispute_state_root`,
`disputed_report_ids`, and report-leaf commitments so a graph that omits the
dispute lane is rejected by `verify receipt`.

Aggregates also bind the active feed and query-policy roots at build time.
Changing policy fields such as freshness window, evidence floor, source policy,
reporter count, deviation limit, report reward, dispute bond, or slash amount
quarantines older aggregates until they are rebuilt under the active policy.
Mutable budget accounting such as `reward_spent_e8` is excluded from the policy
root so normal reporter payouts do not invalidate older receipts by themselves.

`verify receipt` treats terminal `zeno_oracle.oracle_authorization_bundle.v1`
objects as graph-bearing receipts. The authorization roots, oracle value,
evidence class, freshness window, and receipt graph root must match the embedded
`zeno_oracle.receipt_graph.v1` object; a bundle that swaps in a different graph
is rejected even if the opaque action identifiers still match. The receipt graph
verifier also checks that report-leaf commitments are sorted, exactly match the
included report/source lists, and preserve the reporter/source snapshot hashes.

The zUSD demo API can require typed oracle authorizations for oracle
bootstrap/report/commit by setting:
```bash
ZUSD_ORACLE_AUTHORIZATION_REQUIRED=1
```

When enabled, the API compares the authorization against the actual zUSD runtime
price, action facts, pre-state hash, query, action kind, and current epoch. An
invalid value for this flag fails closed.

## FIRE Assurance Gate

Run the public FIRE compiler/verifier assurance gate:
```bash
bash tools/run_fire_assurance_gate.sh
```

This does not claim the compiler or verifier are bug-free. It checks that
formal-verification claims require checked proof receipts, package acceptance
receipts do not authorize settlement, and `FIREVReceiptOK` remains the
settlement-authority binding rule.

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

## Tau Frontier Explorer (ZAG-style, Internal)

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
- profile config: `docs/derivatives/mechanical_scientist_perps_config_m3max.yaml`
- CE model: `src/kernels/dex/perp_epoch_isolated_v3.yaml`
- hazard batch: `262144`
- CE batch: `262144`
- ML-BVA max candidates/action: `400`
- ML-BVA max states: `128`
- ML-BVA UCB alpha: `1.25`

Override any default with env vars, for example:
```
GPU_BATCH_CE=1048576 GPU_STEPS_CE=1000 bash tools/run_perps_gpu_liftoff.sh
```
or:
```
PERPS_LIFTOFF_CONFIG=docs/derivatives/mechanical_scientist_perps_config_m3max_hires.yaml \
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
