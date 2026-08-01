# FCIS M6 Task I02 Report

TASK_ID: I02
BASE_SHA: 014f88efc3e3215bdfb9672dffb519414a740f9e
SOURCE_HEAD_SHA: 059f99d3b53001a7dd98b5f42ba2127e2c575f65
SOURCE_HEAD_TREE: c1c1680948a957750f33c56698b97a5be8eb2bb3
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_i02_committed_outbox.py
- docs/research/m6_tasks/TASK_I02_OUTBOX_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I02_PLAN.md

IMPLEMENTATION_HEAD_SHA: 059f99d3b53001a7dd98b5f42ba2127e2c575f65
IMPLEMENTATION_TREE: c1c1680948a957750f33c56698b97a5be8eb2bb3
IMPLEMENTATION_PARENT: 014f88efc3e3215bdfb9672dffb519414a740f9e

CLAIM_IMPLEMENTED: I02 extends the isolated H02 SQLite research adapter with
a typed operational row for every committed outbox effect. The row preserves
the semantic effect identity while carrying status, lease, attempt, error, and
acknowledgment-root fields. SQL checks and canonical reopen reject invalid,
orphaned, missing, or mismatched operational rows.

COMMANDS_RUN:
- python3 -m ruff format tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i02_committed_outbox.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I02
- sha256sum --check --strict docs/research/m6_tasks/TASK_I02_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused I02 suite passed: 6 passed.
- A nonempty committed effect receives exactly one PENDING operational row
  inside the publication seed transaction.
- Lease mutation changes operational state while preserving the semantic
  effect identity and its canonical preimage.
- Typed LEASED and ACKED rows reject missing required fields.
- SQLite CHECK constraints reject a LEASED row without owner and expiry.
- Canonical reopen rejects an orphan effect row that has no publication atom.
- The combined H02/H03/I02 regression suite passed: 37 passed.
- The post-I03 H02/H03/I02/I03 regression suite passed: 41 passed.
- Current-head Ruff, formatting, strict mypy, and Python compilation passed
  across the shared module and all affected tests.
- Ruff, strict mypy, Python compilation, packet validation, and the source
  manifest pass.

MUTANTS_ADDED: None. The focused suite adds invalid lease, invalid
acknowledgment, SQL constraint, semantic-ID stability, and orphan-row
regressions.

FORMAL_EVIDENCE: None. I02 supplies executable schema and reconstruction
evidence; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I02 does not implement worker lease acquisition, retry scheduling, or
  destination delivery.
- I02 does not prove destination deduplication, acknowledgment provenance,
  lost-ack recovery, or effect application.
- I02 does not provide schema migration for existing production stores.
- I02 does not prove concurrent linearizability, filesystem durability,
  production datastore behavior, runtime reachability, migration, no-bypass
  coverage, accounting, or zUSD safety.
- D08 still has an empty-outbox publication fixture; nonempty production
  publication remains unmounted.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The operational fields are typed and checked only within the
declared SQLite research schema. I03 is a shared-adapter follow-up at the
current source head; the I02 task itself still supplies only the schema and
seed contract. A production adapter must preserve the same effect identity,
perform an explicit schema migration, atomically seed the operational row,
implement safe leasing and retry semantics, and bind every destination
acknowledgment to verifier-produced delivery evidence. The H02 adapter remains
a large research hotspot.
