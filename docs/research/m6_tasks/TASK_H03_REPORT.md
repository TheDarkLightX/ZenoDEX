# FCIS M6 Task H03 Report

TASK_ID: H03
BASE_SHA: 014f88efc3e3215bdfb9672dffb519414a740f9e
SOURCE_HEAD_SHA: bdb8781861084a775a4c48a70afabc0545396354
SOURCE_HEAD_TREE: e114841afd3a06745c9780865a5af18de802f8a0
BRANCH: codex/task-m6-receipt-rebind-20260802
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_h03_crash_points.py
- docs/research/m6_tasks/TASK_H03_PLAN.md
- docs/research/m6_tasks/TASK_H03_CRASH_MANIFEST_V1.json

IMPLEMENTATION_HEAD_SHA: bdb8781861084a775a4c48a70afabc0545396354
IMPLEMENTATION_TREE: e114841afd3a06745c9780865a5af18de802f8a0
IMPLEMENTATION_PARENT: 10c07c1012c1097834878d3578724ec568816e82

FOLLOW_UP_REPAIR: The shared adapter now rejects every nonempty durable table
before initialization writes, compares staged seed state before commit, binds
typed operational outbox fields to each committed effect, and exposes the I03
lease/reclaim port. H08 records the initialization regression and exact repair;
I02 and I03 record the outbox schema and lease contract. The shared adapter
also consumes the replayable D08 acceptance value and exposes its ANF root
through an exact typed boundary without process-global acceptance registration.

CLAIM_IMPLEMENTED: H03 adds a closed deterministic crash-point registry and
one-shot fault hook to the isolated H02 SQLite publication adapter. The hook
surfaces the pre-BEGIN, post-BEGIN, pre-CAS, post-CAS-check, every logical
publication-row boundary, pre-COMMIT, and post-COMMIT/pre-response points. The
optional authority-successor helper also exposes its epoch and allowed-writer
insert boundaries. The injected exception is deliberately outside the normal
typed-rejection catches so a later harness can model process loss.

COMMANDS_RUN:
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h03_crash_points.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m ruff format --check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- python3 -m py_compile experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py tests/core/test_fcis_m6_h08_independent_review.py tests/core/test_fcis_m6_i02_committed_outbox.py tests/core/test_fcis_m6_i03_safe_leasing.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H03
- sha256sum --check --strict docs/research/m6_tasks/TASK_H03_SOURCE_MANIFEST.sha256

RESULTS:
- H02 regression suite passed: 8 passed.
- H03 crash-point suite passed: 23 passed.
- Combined H02/H03 suite passed: 31 passed.
- Current-head combined H02/H03/I02 suite passed after the I02 extension:
  37 passed.
- Current-head combined H02/H03/I02/I03 suite passed after the I03 lease
  extension: 41 passed.
- The exact current H02/H03/H08/I02/I03 suite passed: 61 passed.
- All 20 manifest points are registered and match the JSON manifest.
- 16 ordinary publication points are reachable twice on fresh seeded
  connections and raise the same named surrogate.
- 4 optional authority-insert points are reachable twice through the direct
  authority helper and leave no rows after rollback.
- The post-COMMIT/pre-response point leaves the staged POST root durable in the
  connection; H04 must perform the fresh-process canonical reopen.
- Python compilation, Ruff, formatting, and strict mypy pass at the current
  I03 source head across the shared module and all affected tests.

MUTANTS_ADDED: None. The reachability and repeatability suite is the positive
H03 hook contract; H04 owns PRE/POST recovery mutants.

FORMAL_EVIDENCE: None. H03 supplies executable isolated-adapter evidence and
does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- H03 does not terminate a real operating-system process or establish a real
  crash boundary.
- H03 does not prove SQLite filesystem durability, WAL/fsync behavior,
  power-loss recovery, or deployment configuration.
- H03 alone does not prove that every post-crash layout is exact PRE or exact
  POST. H04 supplies tested recovery-model evidence, while production crash
  refinement remains open.
- H03 does not prove concurrent linearization, runtime caller coverage,
  no-bypass behavior, destination idempotency, migration mounting, or value
  movement.
- Whole-system accounting, backing, liability, and zUSD safety remain open.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The fault hook is an isolated research seam and is not connected
to a production datastore or process supervisor. The authority-successor
points are tested through the private table helper because the current D08
fixture binds its publication atom to the existing authority epoch. The 1,000+
line adapter remains an auditability hotspot. The H08 initialization repair is
not a production startup or filesystem-durability proof.
