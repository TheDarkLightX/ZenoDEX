# FCIS M6 Task H08 Report

TASK_ID: H08
BASE_SHA: 014f88efc3e3215bdfb9672dffb519414a740f9e
SOURCE_HEAD_SHA: bdb8781861084a775a4c48a70afabc0545396354
SOURCE_HEAD_TREE: e114841afd3a06745c9780865a5af18de802f8a0
BRANCH: codex/task-m6-receipt-rebind-20260802
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_h08_independent_review.py
- docs/research/m6_tasks/TASK_H08_PLAN.md
- docs/research/m6_tasks/TASK_H08_REVIEW_MATRIX_V1.json

IMPLEMENTATION_HEAD_SHA: bdb8781861084a775a4c48a70afabc0545396354
IMPLEMENTATION_TREE: e114841afd3a06745c9780865a5af18de802f8a0
IMPLEMENTATION_PARENT: 10c07c1012c1097834878d3578724ec568816e82

REVIEW_VERDICT: PASS_WITH_NONCLAIMS

CLAIM_IMPLEMENTED: H08 independently attacks the repaired H02/H03 research
adapter with two-connection stale CAS, every ordinary H03 crash boundary,
missing evidence, surplus orphan evidence, and contaminated initialization.
The repair rejects any nonempty durable table before writing snapshot metadata,
performs staged canonical reopen before commit, preserves the former
contaminated-initialization witness as a regression test, and now reconstructs
typed operational outbox rows for every committed effect, and now supports
the I03 safe lease/reclaim port. I02 and I03 record the outbox extensions; the
H08 attack conclusions remain unchanged. The current adapter additionally
re-verifies the replayable D08 instance and returns an exactly typed ANF root.

COMMANDS_RUN:
- python3 -m ruff format experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H08
- sha256sum --check --strict docs/research/m6_tasks/TASK_H08_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- Focused H08 suite passed: 20 passed in 56.50 seconds.
- All 16 ordinary crash points reopened as exact PRE, with the
  post-COMMIT/pre-response point reopening as exact POST.
- A second connection using the same stale request received
  STALE_SNAPSHOT_CAS and left its state unchanged.
- Missing committed evidence and surplus orphan evidence were rejected by
  canonical reopen.
- The former contaminated-initialization witness now rejects before
  snapshot_meta is written; the pre-existing authority row remains the only
  row and the database is not initialized.
- H02/H03 regression suite passed after the repair: 31 passed.
- The shared H02/H03/I02 regression suite passed after the I02 outbox
  extension: 37 passed.
- The shared H02/H03/I02/I03 regression suite passed after the I03 lease
  extension: 41 passed.
- The exact current H02/H03/H08/I02/I03 suite passed: 61 passed.
- Ruff, formatting, strict mypy, Python compilation, packet validation, and
  the source manifest pass at the current source head.

MUTANTS_ADDED: None. The original contaminated-initialization failure is
retained as a named regression scenario; the existing H02-H04 transaction
mutants remain covered by their prior packets.

FORMAL_EVIDENCE: None. H08 adds independent executable attack evidence and a
review verdict; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- H08 does not prove operating-system power-loss recovery, filesystem
  durability, WAL/fsync behavior, or production concurrent linearizability.
- H08 does not cover a full verifier-produced authority-transition atom at the
  four authority-helper-only fault points.
- H08 does not establish production startup binding, destination delivery,
  migration, no-bypass coverage, whole-system accounting, or zUSD safety.
- I02 operational outbox fields do not establish worker leasing, destination
  acknowledgment provenance, or production schema migration.
- I03 lease/reclaim evidence does not establish destination delivery,
  acknowledgment provenance, or production worker behavior.
- No production datastore, caller, or value-moving path is mounted.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The initialization repair, I02 operational-row contract, and
I03 lease/reclaim port are fail-closed for the declared SQLite research schema.
A production datastore still needs an adapter-specific empty-store invariant,
schema migration, transaction semantics, crash recovery evidence, startup
binding, destination delivery, and acknowledgment provenance. The H02 adapter
remains a large research hotspot.
