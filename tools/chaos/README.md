---
title: README
type: note
permalink: autonomous-tau-dex-review/tools/chaos/readme
---

# Chaos Engineering Toolkit

Hypothesis-driven chaos engineering for imperative shell boundaries.

## Overview

This toolkit provides chaos experiments targeting the imperative shell layer:
- `tau_runner.py` — child process faults (SIGKILL, stdout flood)
- `proof_verifier.py` — external verifier stalls and bounded-IO failures
- `tau_net_client.py` — TCP network faults (truncated replies, reset_peer)
- `api_server.py` — HTTP boundary faults (oversized body, malformed JSON)

**Design**: Experiments produce standalone JSON evidence artifacts that can be consumed by external hypothesis ledgers. The functional core (`src/core/`, `src/state/`) is NOT targeted—keep proofs, ESSO, and differential tests there.

## Quick Start

```bash
# List available experiments
python -m tools.chaos.run_chaos_experiments --list

# Run a single experiment
python -m tools.chaos.run_chaos_experiments -e tau_runner_sigkill -v

# Run all experiments
python -m tools.chaos.run_chaos_experiments --all --json

# Select the next experiment by regret-aware priority
python -m tools.chaos.run_chaos_experiments --select-next

# Rebuild campaign/regret artifacts from prior journals
python -m tools.chaos.update_campaign_state --json

# Run the repo's local-only shell campaign
python -m tools.chaos.run_repo_campaign --campaign safe_local_v1 --json

# Run the main shell-boundary campaign (skips Tau RPC faults unless Toxiproxy is up)
python -m tools.chaos.run_repo_campaign --campaign shell_boundaries_v1 --json

# Run pytest chaos tests
pytest tests/chaos/ -v
```

## Requirements

### Core (always available)
- Python 3.11+
- No external dependencies for process/HTTP chaos

### Network Chaos (optional)
For TCP fault injection experiments (`tau_net_truncated_tcp`, `tau_net_reset_peer`):

```bash
# Start Toxiproxy
docker run -d --name toxiproxy -p 8474:8474 -p 8475-8500:8475-8500 ghcr.io/shopify/toxiproxy

# Or use docker-compose
docker-compose -f docker-compose.chaos.yml up -d
```

## Experiments

| Experiment | Target | Perturbation | Risk |
|------------|--------|--------------|------|
| `tau_runner_sigkill` | tau_runner.py | SIGKILL mid-execution | Medium |
| `tau_runner_stdout_flood` | tau_runner.py | 10MB stdout flood | Medium |
| `proof_verifier_timeout` | proof_verifier.py | stalled verifier child | Medium |
| `tau_net_truncated_tcp` | tau_net_client.py | Toxiproxy limit_data | **High** |
| `tau_net_reset_peer` | tau_net_client.py | Toxiproxy reset_peer | Medium |
| `api_server_oversized_body` | api_server.py | 10MB Content-Length | Medium |

## Evidence Artifacts

Each experiment produces three JSON artifacts in `runs/chaos/{experiment}/`:

### Hypothesis (`hypothesis.json`)
```json
{
  "schema": "chaos/hypothesis/v1",
  "id": "a1b2c3d4e5f6...",
  "claim": "TauNetTcpClient fails closed under truncated TCP replies",
  "test": "Use Toxiproxy limit_data to truncate responses",
  "refutation_criteria": [
    {"criterion": "partial_parse_accepted", "description": "..."},
    {"criterion": "hang", "description": "..."}
  ],
  "status": "pending"
}
```

### Recipe (`recipe.json`)
```json
{
  "schema": "chaos/recipe/v1",
  "id": "...",
  "hypothesis_id": "a1b2c3d4e5f6...",
  "name": "tau_net_truncated_tcp",
  "perturbation": {
    "type": "toxiproxy",
    "action": "limit_data",
    "params": {"bytes": 50}
  }
}
```

### Journal (`journal.json`)
```json
{
  "schema": "chaos/journal/v1",
  "outcome": "corroborated",
  "steady_state_before": {"passed": true, "probes": [...]},
  "perturbation_applied": {"applied": true},
  "refutation_checks": [
    {"criterion": "partial_parse_accepted", "triggered": false}
  ]
}
```

## Popper Method

Each experiment follows the Popper method for falsifiable claims:

1. **Hypothesis**: A falsifiable resilience claim
2. **Steady State**: Baseline that must hold before/after
3. **Perturbation**: Chaos injection (signal, network, HTTP)
4. **Refutation Criteria**: Conditions that falsify the hypothesis
5. **Evidence**: JSON artifacts capturing the outcome
6. **Promotion Rule**: "Supported" after N corroborations, never "proven"

## Regret Management

This toolkit now distinguishes two kinds of regret:

1. **Operational regret**
   - An experiment leaves the system dirty or causes unnecessary blast radius.
   - Mitigation: explicit `rollback` metadata, rollback execution tracking, and post-rollback steady-state checks.

2. **Epistemic regret**
   - You keep spending budget on low-information experiments.
   - Mitigation: campaign state and regret snapshots rank experiments by:
     - severity
     - novelty in the current context
     - falsification likelihood
     - harness error rate
     - blast radius
     - run cost / duration

Artifacts:

- `runs/chaos/campaign_state.json`
- `runs/chaos/regret_snapshot.json`

Selection:

```bash
python -m tools.chaos.run_chaos_experiments --select-next --json
python -m tools.chaos.run_chaos_experiments --select-next --max-blast-radius 0.25
```

The scheduler is deliberately Popper-first:
- repeated corroborations cool an experiment down
- already-falsified experiments in the same context are deprioritized
- high-severity, low-blast, novel experiments rise to the top
- harness failures count against the harness, not as proof of resilience

## Repo Campaigns

The repo ships a small set of named campaigns in `tools/chaos/campaigns/`:

- `safe_local_v1`
  - local-only process and HTTP faults
  - no external fault injector required
- `tau_rpc_v1`
  - Tau RPC transport faults
  - requires `toxiproxy`
- `shell_boundaries_v1`
  - primary shell campaign
  - always runs local faults, and adds Tau RPC faults when `toxiproxy` is available

This keeps the toolkit aligned with explicit boundary areas instead of ad hoc experiment lists.

## Experiment Catalog DSL

Experiment YAMLs in `tools/chaos/experiments/` now carry enough metadata to support autonomous falsification under safety budgets:

- `oracle`
  - Declares what contract is being evaluated (`steady_state`, `slo`, `ux`, `recovery`)
  - Records the metrics and stop conditions that define scientific value and hard aborts

- `scenario`
  - Declares the fault family, state axes, composition, and scope
  - Keeps the search space explicit instead of encoding assumptions in the runner

- `safety_budget`
  - Declares blast-radius, duration, burn-rate, and production-slice limits
  - Fails closed if rollback is required but no rollback actions are declared

These fields are parsed and validated by `regret_scheduler.py` and surfaced in `campaign_state.json`.

### Refutation Criteria

Experiments are **falsified** if:
- Client/server hangs without clean error
- Partial/malformed data accepted as valid
- Wrong exception class raised
- Retry storm (>3 retries in 1s)
- Resource leak (memory/connections)

## File Structure

```
tools/chaos/
├── __init__.py
├── README.md                    # This file
├── schemas/
│   ├── chaos_hypothesis_v1.schema.json
│   ├── chaos_campaign_state_v1.schema.json
│   ├── chaos_regret_snapshot_v1.schema.json
│   ├── chaos_recipe_v1.schema.json
│   └── chaos_journal_v1.schema.json
├── toxiproxy_harness.py         # Toxiproxy wrapper
├── chaos_toolkit_runner.py      # Experiment runner
├── run_chaos_experiments.py     # CLI entrypoint
└── experiments/
    ├── tau_runner_sigkill.yaml
    ├── tau_runner_stdout_flood.yaml
    ├── tau_net_truncated_tcp.yaml
    ├── tau_net_reset_peer.yaml
    └── api_server_oversized_body.yaml

tests/chaos/
├── __init__.py
├── conftest.py                  # Fixtures
├── test_tau_runner_chaos.py
├── test_tau_net_client_chaos.py
└── test_api_server_chaos.py

runs/chaos/                      # gitignored experiment journals
```

## Toxiproxy Usage

The `ToxiproxyHarness` provides a Python wrapper for TCP fault injection:

```python
from tools.chaos.toxiproxy_harness import ToxiproxyHarness

# Truncate responses after 50 bytes
with ToxiproxyHarness(upstream_port=65432) as harness:
    harness.limit_data(50)
    # Connect to harness.listen_port instead of 65432
    client = MyClient(port=harness.listen_port)
    client.call()

# Reset connection immediately
with ToxiproxyHarness(upstream_port=65432) as harness:
    harness.reset_peer(timeout_ms=0)
    # Connection will receive TCP RST

# Add latency
with ToxiproxyHarness(upstream_port=65432) as harness:
    harness.latency(latency_ms=500, jitter_ms=100)
```

### Available Toxics

| Toxic | Description | Params |
|-------|-------------|--------|
| `limit_data` | Truncate after N bytes | `bytes` |
| `reset_peer` | Send TCP RST | `timeout` (ms before reset) |
| `latency` | Add latency | `latency`, `jitter` (ms) |
| `timeout` | Delay then close | `timeout` (ms) |
| `slow_close` | Delay connection close | `delay` (ms) |
| `bandwidth` | Limit bandwidth | `rate` (KB/s) |
| `slicer` | Slice data into chunks | `average_size`, `delay` |

## Evidence Export

The JSON evidence artifacts can be consumed by an external hypothesis or
evidence ledger. Keep external adapters outside this repository, and bind each
imported record to the emitted journal hash.

## Adding New Experiments

1. Create YAML definition in `tools/chaos/experiments/`
2. Add runner function in `run_chaos_experiments.py`
3. Add to `EXPERIMENTS` dict
4. Create pytest tests in `tests/chaos/`

Template:
```python
def run_my_experiment(output_dir: Path, verbose: bool = False) -> ExperimentResult:
    hypothesis = Hypothesis(
        claim="My component fails closed under X",
        test="Apply X and verify error handling",
        target="src/integration/my_module.py",
        perturbation_type="...",
        refutation_criteria=[...],
    )
    # ... build recipe, run, return result
```

## CI Integration

```bash
# Run chaos tests (non-Toxiproxy)
pytest tests/chaos/ -v -k "not Toxiproxy"

# Run all chaos tests (requires Toxiproxy)
docker-compose -f docker-compose.chaos.yml up -d
pytest tests/chaos/ -v
python -m tools.chaos.run_chaos_experiments --all --json > chaos_report.json
```

## References

- [Principles of Chaos Engineering](https://principlesofchaos.org/)
- [Chaos Toolkit](https://chaostoolkit.org/)
- [Toxiproxy](https://github.com/Shopify/toxiproxy)
