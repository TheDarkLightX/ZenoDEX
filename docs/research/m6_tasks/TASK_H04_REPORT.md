# FCIS M6 Task H04 Report

TASK_ID: H04
BASE_SHA: 0846ea9787cc68a9fd40803f2ee93ac674809f78
SOURCE_HEAD_SHA: c6cfcb9b84b4a481e7cfd5e8021c4fc23dade80f
SOURCE_HEAD_TREE: 236886accd35cefd5d4ba92794511463e60c8afc
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h04_crash_recovery.py
- tests/core/test_fcis_m6_h04_crash_recovery.py
- docs/research/m6_tasks/TASK_H04_PLAN.md
- docs/research/m6_tasks/TASK_H04_RECOVERY_MATRIX_V1.json

IMPLEMENTATION_HEAD_SHA: c6cfcb9b84b4a481e7cfd5e8021c4fc23dade80f
IMPLEMENTATION_TREE: 236886accd35cefd5d4ba92794511463e60c8afc
IMPLEMENTATION_PARENT: 0846ea9787cc68a9fd40803f2ee93ac674809f78

CLAIM_IMPLEMENTED: H04 adds a file-backed SQLite process-restart harness. It
prepares independent complete PRE and POST state oracles, launches a fresh
Python worker for each ordinary H03 crash point, requires the dedicated crash
exit code, reopens the seed database through a fresh connection, and compares
the complete SQLiteStateV1 rather than a selected root. The matrix expects PRE
for every pre-COMMIT point and POST for the post-COMMIT/pre-response point.

COMMANDS_RUN:
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py -k 'matrix or AFTER_COMMIT_BEFORE_RESPONSE'
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py -k 'BEFORE_BEGIN or AFTER_BEGIN or BEFORE_CAS or AFTER_CAS_CHECK'
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py -k 'BEFORE_ATOM_INSERT or AFTER_ATOM_INSERT or BEFORE_EVIDENCE_INSERT or AFTER_EVIDENCE_INSERT'
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py -k 'BEFORE_NULLIFIER_INSERT or AFTER_NULLIFIER_INSERT or BEFORE_OUTBOX_INSERT or AFTER_OUTBOX_INSERT'
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h04_crash_recovery.py -k 'BEFORE_ANF_INSERT or AFTER_ANF_INSERT or BEFORE_COMMIT or AFTER_COMMIT_BEFORE_RESPONSE'
- python3 -m py_compile experiments/fcis_m6_h04_crash_recovery.py tests/core/test_fcis_m6_h04_crash_recovery.py
- python3 -m ruff check experiments/fcis_m6_h04_crash_recovery.py tests/core/test_fcis_m6_h04_crash_recovery.py
- python3 -m ruff format --check experiments/fcis_m6_h04_crash_recovery.py tests/core/test_fcis_m6_h04_crash_recovery.py
- python3 -m mypy --strict experiments/fcis_m6_h04_crash_recovery.py tests/core/test_fcis_m6_h04_crash_recovery.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H04
- sha256sum --check --strict docs/research/m6_tasks/TASK_H04_SOURCE_MANIFEST.sha256

RESULTS:
- The recovery matrix and post-commit smoke cases passed: 2 passed.
- All 16 ordinary publication crash points passed across four grouped runs.
- Every pre-COMMIT point reopened as exact PRE.
- The post-COMMIT/pre-response point reopened as exact POST.
- The comparator compared complete SQLiteStateV1 values, including rows and
  derived roots; no third layout was accepted.
- Worker exit code 73 was observed for every injected process fault.
- Python compilation, Ruff, formatting, and strict mypy pass.

MUTANTS_ADDED: None. H04 retains the exact PRE/POST comparator and makes a
third durable layout a rejected classification.

FORMAL_EVIDENCE: None. H04 supplies executable process-harness evidence and
does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- H04 does not prove operating-system power-loss crash consistency, SQLite
  filesystem durability, WAL/fsync deployment settings, or storage hardware
  behavior.
- H04 covers the ordinary D08 publication path. The four H03 authority-helper
  points remain deferred because the current D08 verifier fixture does not
  produce an authority-transition atom.
- H04 does not prove concurrent linearization, destination effects,
  acknowledgment provenance, migration mounting, no-bypass coverage, or value
  movement.
- Whole-system accounting, backing, liability, and zUSD safety remain open.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The child worker is a deterministic Python process harness, not
the production process supervisor or storage engine. The test fixture has an
empty outbox, so the no-external-effect clause is only exercised through the
complete durable-state relation and remains open for H05-H08/I-wave refinement.
