# Assurance

This page is the public assurance ledger for the code that ships in this repo. It is modeled after the same general idea as SQLite's testing page: publish the evidence mix, publish the numbers, and be explicit about what those numbers do and do not mean.

The rule in this repo is:
- coverage is a test-reach metric, not a proof
- passing tests are necessary, not sufficient
- consensus-critical claims should be backed by replayable gates, exported refs, formal checks, and fail-closed design

## Published Release-Lane Numbers

Current public release snapshot on `main`:
- release tag: `shape-v1-rc1`
- authoritative release note: `docs/zenodex/SHAPE_V1_RC1.md`
- public assurance lanes ready: `6/6`
- tracked exported refs required by the public lanes: `10/10`
- acceptance TCB gate: `361` tests, `99.4%` branch coverage
- critical quality gate: `735` tests, `99%` overall branch-enabled coverage
- critical mutation gate: `7/7` mutants killed, mutation score `1.0`
- acceptance fuzz gate: `11` tests passed
- snapshot recovery gate: `19` tests passed
- Tau syntax gate: `62/62` specs passed
- Tau trace registry gate: `1/1` passed
- perps evidence lane: `330` tests passed in the release lane, plus ESSO cross-solver verification and Lean proof builds
- spot evidence lane: `214` tests passed in the release lane, `2` skipped, plus ESSO cross-solver verification

Replay commands:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/permissionless_assurance.py replay public
python3 tools/permissionless_assurance.py replay critical
python3 tools/permissionless_assurance.py replay release
```

Operational release checklist:

- `docs/zenodex/SHAPE_V1_RELEASE_CHECKLIST.md`

## Evidence Stack

We use several evidence layers at once:
- direct unit tests and regression tests
- property tests and BVA tests
- fuzzing
- mutation testing
- Tau syntax and trace execution
- ESSO `verify-multi` with fail-closed posture
- Lean proofs for selected arithmetic and accounting claims
- differential tests against exported kernel refs

That combination is materially stronger than a line-coverage target by itself.

## Subsystem Matrix

### Acceptance TCB

This is the most trust-sensitive integration surface for replay, settlement validation, proof verification, replay protection, and state-root style checks.

Current public bar:
- included in the release lane: `yes`
- branch coverage: `100%`
- mutation gate: `7/7` killed
- fuzz gate: `yes`

Verdict:
- strongest published assurance surface in the repo today

### Spot DEX Functional Core

This includes the public spot/settlement path, exported refs, witness adapters, and the batch-auction evidence slice.

Current public bar:
- included in the release lane: `yes`
- critical gate overall: `99%` branch-enabled coverage
- spot evidence lane: `225` tests passed
- batch-auction exported ref tracked: `yes`
- batch-auction kernel verified with ESSO in the public lane: `yes`

Important caveat:
- this is a very strong practical posture, but handwritten batch orchestration still exists, so the strongest claim is "high assurance", not "perfect"

### Perps and Insurance Accounting

This is the best-covered insurance-like surface in the public tree.

Public evidence:
- included in the release lane: `yes`
- clean focused direct suite: `333 passed`
- focused branch coverage on `src/core/perp_v2` + `src/integration/perps_api`: `100%`
- ESSO `verify-multi` in the public lane:
  - `src/kernels/dex/perp_epoch_isolated_v3.yaml`
  - `src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml`
  - `src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml`
  - `src/kernels/dex/perp_game_theory_v2.yaml`
- Lean proofs built in the public lane:
  - `Proofs.PerpEpochSafety`
  - `Proofs.PerpFundingRateSafety`
  - `Proofs.PerpInsuranceSafety`
  - `Proofs.PerpGameTheory`

What this means:
- perps insurance accounting is at a strong published bar
- the repo has explicit formal evidence for insurance conservation and solvency-style claims in the perps lane

### zUSD / Stability Module

`zUSD` exists in the tree and has real tests, but it is not yet at the same published assurance bar as the spot/perps core.

Direct measurement on the current tree:
- direct zUSD slice: `92 passed`, `14 skipped`
- branch coverage:
  - `src/core/zusd.py`: `69%`
  - `src/integration/zusd_api.py`: `75%`
  - `src/integration/zusd_tau_gate.py`: `63%`

Current status:
- included in the public release lane: `no`
- same assurance bar as acceptance TCB / spot / perps: `no`

Why not:
- it does not currently have a dedicated public replay lane
- its branch coverage is materially below the published core bar
- the Tau-gated zUSD surface is not yet enforced by the same fail-closed public release workflow

Verdict:
- tested and partially hardened
- not ready to be advertised as "fully covered" or at the same public assurance level as the published DEX core

### IL Insurance Pools

The repo contains insurance-pool kernels:
- `src/kernels/dex/il_insurance_pool_v1.yaml`
- `src/kernels/dex/il_insurance_pool_v2.yaml`

Current status:
- included in the public release lane: `no`
- dedicated public tests found in the current tree: `no`
- dedicated public gate script: `no`

Verdict:
- experimental / below the published assurance bar
- we should not market these as having the same assurance level as the spot core or perps insurance accounting

## What Is Not Yet at 10/10

The repo is strong, but not finished.

Main remaining gaps:
- handwritten batch orchestration is still richer than a pure kernel-first runtime
- `zUSD` is below the published core bar
- IL insurance pools are below the published core bar
- some experimental or advisory modules are present in the tree without being part of the public release lane

## Practical Reading of the Numbers

Good interpretations:
- `100%` branch coverage on the acceptance TCB means we reached every branch there with tests
- `99%` branch-enabled coverage on the critical slice means the public DEX core is very heavily exercised
- mutation and fuzz gates add evidence against overfitting to static regressions
- ESSO and Lean add formal pressure where pure test coverage is weak

Bad interpretations:
- `99%` coverage does not mean "zero bugs"
- one green replay does not mean all repo modules are equally hardened
- a module existing in `src/` does not mean it is part of the published high-assurance lane

## Short Answers

Is the codebase secure?
- the published DEX core is at a strong practical assurance level
- stronger than typical application code because it combines replayable tests, coverage, fuzzing, mutation, Tau, ESSO, and Lean

Is everything in the repo at that level?
- no

Is `zUSD` fully covered?
- no

Is insurance fully covered?
- perps insurance accounting is strong and formally backed
- IL insurance pool kernels are not yet at the same public bar
