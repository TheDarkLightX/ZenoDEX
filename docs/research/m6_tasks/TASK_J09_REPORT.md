# FCIS M6 Task J09 Report

TASK_ID: J09
BASE_SHA: 7a921783a8e0b3e706f4dcaa86bd3a9ad0aa6321
SOURCE_HEAD_SHA: fdbbe7813621f0f4ae8c393f83ee2a99072bf8cc
SOURCE_HEAD_TREE: fe7c15b3c5aca5d25e797d958ee2e47f0460dd64
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_j09_migration_crash_v1.json
- docs/TLA_CLAIM_SUMMARY.md
- docs/claims_registry.yaml
- docs/research/m6_tasks/FCIS_M6_J09_MIGRATION_CRASH_V1.md
- docs/research/m6_tasks/TASK_J09_MIGRATION_CRASH_V1.json
- docs/research/m6_tasks/TASK_J09_PLAN.md
- docs/research/m6_tasks/TASK_J09_REPORT.md
- docs/research/m6_tasks/TASK_J09_EVIDENCE.json
- docs/research/m6_tasks/TASK_J09_SOURCE_MANIFEST.sha256
- experiments/fcis_m6_j09_migration_crash_check.py
- formal/tla/FCISM6J09MigrationCrash.cfg
- formal/tla/FCISM6J09MigrationCrash.tla
- src/core/fcis_m6_j09_migration_crash.py
- tests/core/test_fcis_m6_j09_migration_crash.py
- tests/core/test_fcis_m6_j09_migration_crash_properties.py
- tools/build_fcis_m6_j09_migration_crash.py

IMPLEMENTATION_HEAD_SHA: fdbbe7813621f0f4ae8c393f83ee2a99072bf8cc
IMPLEMENTATION_TREE: fe7c15b3c5aca5d25e797d958ee2e47f0460dd64
IMPLEMENTATION_PARENT: 7a921783a8e0b3e706f4dcaa86bd3a9ad0aa6321

CLAIM_IMPLEMENTED: J09 provides a bounded Python and TLA+ migration/crash
campaign. The Python model reaches every declared migration phase with exact
phase-prefix progression, one writer, fresh authorization after restart,
atomic complete publication, PRE/POST crash behavior, retry identity,
complete history/residual/nullifier/outbox lineage, ordered delivery and
acknowledgment, and evidence-version rebind without V1/V2 mixture. The
independent TLA+ control model checks the corresponding bounded obligations.

COMMANDS_RUN:
- `PYTHONPATH=. python3 experiments/fcis_m6_j09_migration_crash_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_j09_migration_crash.py --check`
- focused J09 tests and deterministic property tests
- the adjacent J01-J08 and F05-F06 migration regression suite
- `python3 -m py_compile` on all J09 Python files
- Ruff check and Ruff format check on all J09 Python files
- strict mypy on all J09 Python files
- JSON parsing for the J09 configuration and vector
- `python3 tools/render_tla_claim_summary.py --check`
- TLA claim inventory and registry tests
- direct TLC 2.19 check of `formal/tla/FCISM6J09MigrationCrash.cfg`
- `git diff --check`

RESULTS:
- The independent Python checker passed with `1694` reachable states and
  `30492` explored transitions.
- The campaign performed `396396` named invariant checks and found zero
  invariant failures.
- All ten permanent Python mutants were killed, including the four task
  blockers: skipped phase, dual writers, missing residual transport, and
  mixed V1/V2 evidence.
- Focused/property tests passed: `9 passed`. The adjacent migration regression
  passed: `74 passed`.
- TLC passed with `6773` distinct states, `21958` generated states, depth `24`,
  and zero errors.
- The generated TLA claim summary and inventory tests passed with 38 discovered
  models and 38 corresponding claim entries.
- Ruff, formatting, strict mypy, Python compilation, JSON, and diff checks
  passed.
- The complete all-model batch command was attempted with a 120-second
  per-model limit. It reached an existing `SettlementWitnessInclusionQueue`
  model and did not complete within that limit. This is recorded as an
  uncompleted broad gate; it is not presented as J09 evidence.

MUTANTS_ADDED: Skipped phase, dual writers, missing residual transport, mixed
V1/V2 evidence, restart without fresh authorization, acknowledgment before
delivery, effect-identity rebound, crash partial observation, old writer after
authority switch, and balance-only rollback.

FORMAL_EVIDENCE: Direct TLC 2.19 model checking of the new J09 TLA+ control
model passed. No new Lean theorem is claimed. The TLA+ model uses bounded
counters and version labels; it does not authenticate real durable state.

REMAINING_NONCLAIMS:
- J09 is research-only and unmounted.
- The Python construction and identity checks are bounded model premises.
- J09 does not prove production datastore atomicity, filesystem durability,
  external destination authenticity/idempotency, runtime writer reachability,
  no-bypass coverage, accounting, backing, or zUSD safety.
- The complete public TLA batch remains incomplete because an existing model
  exceeded the selected per-model timeout; the new J09 model itself passed.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The functional Python source is a large bounded research
hotspot, and the TLA+ model abstracts rows and roots into counters. A
production refinement must bind the same complete publication aggregate to an
authenticated datastore transaction, process recovery protocol, destination
worker, migration authority token, and every mounted value-moving entrypoint.
