# FCIS M6 Task I07 Report

TASK_ID: I07
BASE_SHA: a26110e90c83371316155680c6207e99ebf47804
SOURCE_HEAD_SHA: a47bb984f277a767b260c3c6d0d62343a732bd20
SOURCE_HEAD_TREE: 9da902c3ee5eac854047e01275f290480c135ed1
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- tools/check_fcis_m6_i07_disaster_matrix.py
- tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- docs/research/m6_tasks/TASK_I07_OUTBOX_DISASTER_MATRIX_V1.json
- docs/research/m6_tasks/TASK_I07_PLAN.md

IMPLEMENTATION_HEAD_SHA: a47bb984f277a767b260c3c6d0d62343a732bd20
IMPLEMENTATION_TREE: 9da902c3ee5eac854047e01275f290480c135ed1
IMPLEMENTATION_PARENT: a26110e90c83371316155680c6207e99ebf47804

CLAIM_IMPLEMENTED: I07 adds a fail-closed ten-scenario outbox disaster
matrix. Each required failure family has exact durable fields for reopen,
outbox, acknowledgment, and authority state, exact external fields for
delivery attempts, semantic-effect count, and receipt outcome, named
preconditions, fault boundary, invariants, evidence references, and
research-only nonclaims. The checker rejects missing, duplicate, reordered, or
unknown scenarios, altered nested fields, impossible effect/attempt claims,
missing invariant anchors, and omitted unmounted boundaries.

COMMANDS_RUN:
- python3 tools/check_fcis_m6_i07_disaster_matrix.py docs/research/m6_tasks/TASK_I07_OUTBOX_DISASTER_MATRIX_V1.json
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- python3 -m ruff check tools/check_fcis_m6_i07_disaster_matrix.py tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- python3 -m ruff format --check tools/check_fcis_m6_i07_disaster_matrix.py tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- python3 -m mypy --strict tools/check_fcis_m6_i07_disaster_matrix.py tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- python3 -m py_compile tools/check_fcis_m6_i07_disaster_matrix.py tests/core/test_fcis_m6_i07_outbox_disaster_matrix.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I07
- sha256sum --check --strict docs/research/m6_tasks/TASK_I07_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- The matrix checker accepted exactly ten required scenarios.
- Focused I07 suite passed: 6 passed.
- Negative witnesses rejected a missing scenario, an effect without a
  delivery attempt, a missing unmounted nonclaim, and a missing named
  invariant.
- The matrix covers delivery before commit, orphan rows, same-effect payload
  collision, foreign receipt, acknowledgment before delivery, lost lease,
  worker crash before send, worker crash after send, worker crash after ack
  write, and migration during delivery.
- Every row records exact durable and external expectations and points to the
  relevant I02-I06 evidence or explicit open boundary.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: None. The focused checker suite uses targeted in-memory
mutations as negative witnesses for registry completeness, effect/attempt
consistency, unmounted-claim preservation, and invariant coverage.

FORMAL_EVIDENCE: None. I07 supplies a machine-checked scenario registry; it
adds no machine-checked theorem or production crash test.

REMAINING_NONCLAIMS:
- I07 does not execute a production worker, datastore, network destination,
  migration switch, or local acknowledgment journal.
- I07 does not prove filesystem or power-loss durability, concurrent
  linearizability, runtime reachability, no-bypass coverage, accounting,
  backing, or zUSD safety.
- The scenario rows are obligations for future refinement and do not promote
  I02-I06 research models to mounted runtime behavior.
- No caller, API, worker, destination, migration, or value-moving path is
  mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The matrix encodes expected outcomes as a checked registry, but
its evidence references do not execute a production adapter. The migration
row intentionally remains an authority-boundary obligation until J-wave
implementation proves stale-writer rejection during delivery. The external
semantic-effect count is a model-level invariant and requires destination-side
refinement evidence before any operational claim.
