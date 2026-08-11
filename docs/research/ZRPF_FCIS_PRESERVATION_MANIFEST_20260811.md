# ZRPF FCIS Preservation Manifest — 2026-08-11

Status: `RESEARCH_ONLY_UNMOUNTED`

This manifest records the bounded source snapshot preserved on branch
`codex/zrpf-global-settlement-fcis-20260811` from base commit
`b135030f3b960609f2d6cca805a5a38433d63bf4`. That parent adds the M6 RISC0
semantic-surface checker and is itself based directly on
`12bde5263b8855e0ac76bd49b3de402e3e6f9b76`.

## Included scope

- Test Hygiene Contract V1, its repository skill, CI/critical-gate integration,
  deterministic checkers, and eight source-pinned evidence packets.
- GlobalSettlementABI V1 Python and Rust functional cores for asset transfer,
  managed asset lifecycle, lane coordination, release-aware receipt admission,
  route composition, bounded epoch admission, and checked epoch-effect
  composition.
- The source-pinned ShapeForge world model, scenario corpus, tactic bank,
  negative knowledge, development import bundle, and checker.
- The standalone RISC0 asset leaf, lane coordinator, and bounded epoch research
  crates, including static preflight and receipt-admission tests.

## Authority and nonclaims

- The snapshot grants no production, settlement, migration, publication, or
  writer capability.
- The current epoch-effect composer is host-side and restricted to sequential
  `ASSET_TRANSFER` routes with zero terminal obligations and no external outbox.
- Real RISC0 proof regeneration and release-aware recursive replay remain
  deferred to a higher-capacity Runpod machine.
- Most M6 economic lanes, whole-state reconciliation, atomic ZenoLedger
  publication, migration activation, and legacy-writer retirement remain open.
- The source branch contains thousands of unrelated dirty paths. This
  preservation commit intentionally excludes those paths and all build caches,
  temporary agent outputs, screenshots, browser state, and local machine data.
- The broader source-pinned M6 safe-mount, migration, outbox, writer-inventory,
  and durable-store candidate predates the hygiene contract. It remains intact
  in the working tree and is outside this replayable FCIS commit; preserve it on
  a separately labeled WIP branch rather than weakening this branch's gate.

## Preservation gates

The staged snapshot must pass before commit:

- `git diff --cached --check`
- Test Hygiene Contract V1 static and changed-file gates
- the ShapeForge global epoch admission checker
- Python/Rust golden-vector parity
- focused Python GlobalSettlementABI tests
- standalone Rust GlobalSettlementABI tests, formatting, and Clippy
- the M6 ATDD and completeness-review structural checkers

Real proof generation is outside this preservation gate and remains an explicit
Runpod follow-up.
