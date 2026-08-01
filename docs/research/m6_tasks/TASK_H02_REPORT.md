# FCIS M6 Task H02 Report

TASK_ID: H02
BASE_SHA: 00d95e2b09be663e7d07547e4eab020718042d62
SOURCE_HEAD_SHA: 3eea372c4b7b672785ce897625d207358f6b6f36
SOURCE_HEAD_TREE: 23f3e3fe0d96044d974af8c26f9385efae1bf850
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_h02_sqlite_publication.py
- docs/research/m6_tasks/TASK_H02_PLAN.md
- docs/research/m6_tasks/FCIS_M6_H02_SQLITE_PUBLICATION_SCHEMA_V1.md

IMPLEMENTATION_HEAD_SHA: 3eea372c4b7b672785ce897625d207358f6b6f36
IMPLEMENTATION_TREE: 23f3e3fe0d96044d974af8c26f9385efae1bf850
IMPLEMENTATION_PARENT: 00d95e2b09be663e7d07547e4eab020718042d62

CLAIM_IMPLEMENTED: H02 adds an isolated SQLite refinement with one
BEGIN IMMEDIATE publication transaction. It reconstructs the complete PRE
layout, checks expected snapshot/publication/state/authority roots, binds a
verifier-produced D08 ANF witness, derives the complete POST relation,
performs a SQL CAS, inserts the logical publication rows, reopens the
uncommitted rows, compares them with the exact POST state, and commits or
rolls back. The ANF relation is explicit because PublicationAtomV1 does not
contain an ANF root field.

COMMANDS_RUN:
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h02_sqlite_publication.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H02
- sha256sum --check --strict docs/research/m6_tasks/TASK_H02_SOURCE_MANIFEST.sha256

RESULTS:
- Focused tests passed: 8 passed.
- Python compilation passed.
- Ruff check passed.
- Ruff format check passed.
- Strict mypy passed with no issues in 2 source files.
- Complete POST publication and all H02 logical row families passed.
- Stale snapshot, state, and authority CAS cases were no-ops.
- A forced SQLite abort after evidence insertion rolled back every H02 row.
- Foreign verifier acceptance, atom-bearing seed without ANF, and crossed
  atom/witness cases rejected.
- The source and test hashes match the H02 implementation commit.

MUTANTS_ADDED: None. Negative witnesses are covered by focused rejection and
rollback tests.

FORMAL_EVIDENCE: None. H02 supplies executable isolated-adapter evidence and
does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- H02 does not prove filesystem durability, WAL/fsync behavior, or power-loss
  recovery.
- H02 does not provide deterministic process-crash injection at every logical
  boundary; that is H03/H04.
- H02 does not prove concurrent linearization or production isolation settings.
- H02 does not establish authenticated production callers, runtime coverage,
  or no-bypass behavior.
- H02 does not establish destination idempotency or worker acknowledgment
  provenance.
- H02 does not mount migration authority or production value movement.
- H02 does not prove whole-system conservation, backing, liability, or zUSD
  safety.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The adapter is a 1029-line research hotspot and remains an
auditability risk. SQLite schema constraints and in-memory tests do not refine
the production datastore contract. The D08 fixture has no outbox rows, so H02
does not yet exercise a nonempty effect publication; H02 schema and reopen
logic retain the outbox relation for the later H03-H08 sequence.
