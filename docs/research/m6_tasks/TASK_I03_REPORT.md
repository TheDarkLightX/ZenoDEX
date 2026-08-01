# FCIS M6 Task I03 Report

TASK_ID: I03
BASE_SHA: 014f88efc3e3215bdfb9672dffb519414a740f9e
SOURCE_HEAD_SHA: 059f99d3b53001a7dd98b5f42ba2127e2c575f65
SOURCE_HEAD_TREE: c1c1680948a957750f33c56698b97a5be8eb2bb3
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_i03_safe_leasing.py
- docs/research/m6_tasks/TASK_I03_LEASING_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_I03_PLAN.md

IMPLEMENTATION_HEAD_SHA: 059f99d3b53001a7dd98b5f42ba2127e2c575f65
IMPLEMENTATION_TREE: c1c1680948a957750f33c56698b97a5be8eb2bb3
IMPLEMENTATION_PARENT: 014f88efc3e3215bdfb9672dffb519414a740f9e

CLAIM_IMPLEMENTED: I03 adds a typed safe-leasing port to the isolated H02
SQLite research adapter. A worker request names an already committed effect,
worker label, and explicit logical time. The adapter derives expiry, rejects
active/nonclaimable rows, reclaims expired leases to PENDING, and atomically
claims the canonical effect with a conditional status/owner/expiry/attempt
update. The returned effect and payload are copied from committed durable
state, so a timeout cannot mint a second semantic identity.

COMMANDS_RUN:
- python3 -m ruff format experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks I03
- sha256sum --check --strict docs/research/m6_tasks/TASK_I03_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused I03 suite passed: 4 passed.
- Active leases reject a second worker without changing durable state.
- Expired leases are reaped to PENDING and can be claimed again with the
  same effect ID, payload root, and incremented attempt count.
- Direct acquisition at the expiry boundary atomically reclaims and re-leases
  the same canonical effect.
- Missing effects, zero/overflowing lease durations, and attempt-count
  exhaustion reject without minting or changing a semantic effect.
- The combined H02/H03/I02/I03 suite passed: 41 passed.
- Independent H08 review passed: 20 passed.
- H04 crash-recovery suite passed: 17 passed.
- Ruff, formatting, strict mypy, Python compilation, packet validation, and the
  source manifest pass at the I03 source head.

MUTANTS_ADDED: None. The focused suite contains negative witnesses for active
lease stealing, non-boundary expiry, missing effect IDs, expiry arithmetic
overflow, attempt-count exhaustion, and semantic identity replacement.

FORMAL_EVIDENCE: None. I03 supplies executable transactional and multi-worker
research evidence; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- I03 does not implement destination delivery, destination deduplication,
  acknowledgment provenance, lost-ack recovery, retry scheduling, or worker
  supervision.
- I03 does not prove SQLite filesystem durability, production concurrent
  linearizability, schema migration, runtime reachability, migration, or
  no-bypass coverage.
- I03 does not establish accounting, backing, liability, or zUSD safety.
- No production datastore, caller, worker, destination, or value-moving path
  is mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The lease port uses explicit logical time and SQLite
`BEGIN IMMEDIATE` in the isolated research schema. A production worker must
preserve the effect/payload binding, implement adapter-specific transaction
and lease durability semantics, define retry/error policy, and connect the
lease to a provenance-checked destination adapter. The H02 adapter remains a
large research hotspot.
