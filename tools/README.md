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

These helpers compute winners off-chain (optionally on GPU via Torch) and emit
Tau steps for cheap, deterministic certificate checks.

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
- Search is optionally GPU-accelerated (approx ranking with Torch float64).
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

Run an improvement bounty round (select best verified submission; optional Tau argmax cert):
```bash
python3 tools/gpu_jobs/improvement_bounty_round_route_v1.py \\
  --submission alice=/tmp/witness1.json \\
  --submission bob=/tmp/witness2.json \\
  --output /tmp/round.json \\
  --emit-argmax-steps /tmp/argmax_cert.json \\
  --require-positive-improvement
```
