# BVA Tools (Internal)

This folder contains lightweight helpers for **Boundary Value Analysis (BVA)**.

Two modes are supported:
1. **Static BVA**: generate "just-below / at / just-above" values for declared domains
2. **Dynamic boundary mining** (optional): search for inputs where an output label (or execution path)
   flips, then generate BVA triples around those discovered flip points.

These tools are intended to help *author* better tests. They are not part of the
protocol runtime, and they must not be used for consensus-critical decisions.

## Quick Start

1) Create a scenario (see `tools/bva/scenarios/`).

2) Print static BVA suggestions:
```bash
python3 tools/bva/mine_bva.py --scenario tools/bva/scenarios/slippage_advisor_status.py --print-bva
```

3) Mine dynamic boundaries (writes JSON under `internal/` by default):
```bash
python3 tools/bva/mine_bva.py \
  --scenario tools/bva/scenarios/slippage_advisor_status.py \
  --mine-boundaries \
  --out internal/bva/slippage_advisor_status_boundaries.json
```

3b) Mine global boundaries using **pair-density MCMC** (useful for cross-field interactions):
```bash
python3 tools/bva/mine_bva.py \
  --scenario tools/bva/scenarios/slippage_advisor_status.py \
  --mine-mcmc \
  --mcmc-chains 8 \
  --mcmc-steps 512 \
  --out internal/bva/slippage_advisor_status_mcmc.json
```

Example multi-parameter scenario:
```bash
python3 tools/bva/mine_bva.py \
  --scenario tools/bva/scenarios/pokayoke_guardrails_action.py \
  --mine-mcmc \
  --out internal/bva/pokayoke_guardrails_action_mcmc.json
```

4) Generate pytest snippet from mined boundaries:
```bash
python3 tools/bva/gen_pytest_cases.py \
  --scenario tools/bva/scenarios/slippage_advisor_status.py \
  --boundaries internal/bva/slippage_advisor_status_boundaries.json \
  --only-param confidence_bps \
  --limit 12
```

To generate cases from MCMC-mined axis boundaries:
```bash
python3 tools/bva/gen_pytest_cases.py \
  --scenario tools/bva/scenarios/slippage_advisor_status.py \
  --boundaries internal/bva/slippage_advisor_status_mcmc.json \
  --source mcmc \
  --limit 12
```

To include raw opposite-label pair endpoints (useful for interaction regressions):
```bash
python3 tools/bva/gen_pytest_cases.py \
  --scenario tools/bva/scenarios/slippage_advisor_status.py \
  --boundaries internal/bva/slippage_advisor_status_mcmc.json \
  --source mcmc \
  --include-mcmc-pairs \
  --limit 12
```

## Notes

- All output under `internal/` is git-ignored by default.
- Exceptions are treated as a distinct label (useful for validation boundaries).
- The miner is budgeted and heuristic. It is a *suggestion engine*, not proof.
