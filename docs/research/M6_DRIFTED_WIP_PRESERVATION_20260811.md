# M6 Drifted WIP Preservation — 2026-08-11

Status: `WIP_DRIFTED_UNMOUNTED`

This branch preserves the broader M6 candidate that remained outside the
replayable FCIS snapshot. It is based on FCIS preservation commit
`827f5cfcacfc3f26fe6bd5fcf4f82f0dd326b6bd`.

The M6 ATDD contract remains frozen to historical base
`12bde5263b8855e0ac76bd49b3de402e3e6f9b76`. The current candidate evolved
after that snapshot. Its fail-closed checker reports the base mismatch and 18
source-hash mismatches. This branch preserves both sides of that discrepancy;
it does not refresh hashes or imply current refinement evidence.

## Included scope

- The 18-workflow, 81-scenario M6 global-economic ATDD/BDD contract and its
  historical source pins.
- The Luna completeness review and the seven exact runtime files it inspected.
- Safe-mount state, transition, authority-evidence, migration, durable-store,
  external-proof, outbox, and commit-port research modules.
- The M6 writer inventory, global economic commit kernel, zUSD liability
  coverage kernel, recursive-STARK M6 core, and focused tests/checkers.

## Why this is a WIP branch

Several historically pinned runtime files contain large later changes shared
with other unfinished work. Preserving the contract and current bytes together
keeps the detected drift reproducible while avoiding any claim that the changes
form a clean review or merge unit.

## Nonclaims

- No M6 profile is mounted and no writer epoch is rotated.
- No migration, settlement, outbox, or value-moving production authority is
  granted.
- The current source-pin and completeness checkers fail closed. No successful
  current refinement or review claim is made.
- The branch is unsuitable for direct merge. Future work must port reviewed
  pieces onto a clean, refreshed base and regenerate all source manifests.
- Real RISC0 proof replay remains deferred to Runpod.

## Preservation observations

- `python3 tools/check_m6_global_economic_core_atdd_v1.py` fails with one base
  mismatch and 18 source-hash mismatches.
- `python3 tools/check_m6_global_economic_core_luna_review_v1.py` fails because
  the reviewed contract hash and current contract/source closure differ.
- The focused nine-file M6 pytest run reached 79% and exposed five failures
  before it was intentionally interrupted (`exit 130`) for workstation thermal
  safety. The interrupted run has no complete pass count and makes no claim
  about the unexecuted remainder.
- Ruff over all 32 staged Python files reports 18 findings: one unsorted import
  block in `confidential_sealed_bid_api.py`, 13 module-import-position findings,
  one non-strict `zip`, and three constant-attribute `getattr` findings in
  `zeno_ledger_run_local.py`.
- staged diff, credential-pattern, and machine-path scans

Any failing check remains a recorded WIP limitation and blocks promotion.
