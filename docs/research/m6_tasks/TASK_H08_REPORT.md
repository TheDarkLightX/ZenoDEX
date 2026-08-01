# FCIS M6 Task H08 Report

TASK_ID: H08
BASE_SHA: d257d6f086bf809cb8f56a9028fb3625d8f9fa5d
SOURCE_HEAD_SHA: e52c09e84981f35db83a5aa390c49c9156c4c1ae
SOURCE_HEAD_TREE: 38923f8baa019027d168ad872dc55def76f0b841
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- experiments/fcis_m6_h02_sqlite_publication.py
- tests/core/test_fcis_m6_h08_independent_review.py
- docs/research/m6_tasks/TASK_H08_PLAN.md
- docs/research/m6_tasks/TASK_H08_REVIEW_MATRIX_V1.json

IMPLEMENTATION_HEAD_SHA: e52c09e84981f35db83a5aa390c49c9156c4c1ae
IMPLEMENTATION_TREE: 38923f8baa019027d168ad872dc55def76f0b841
IMPLEMENTATION_PARENT: d257d6f086bf809cb8f56a9028fb3625d8f9fa5d

REVIEW_VERDICT: PASS_WITH_NONCLAIMS

CLAIM_IMPLEMENTED: H08 independently attacks the repaired H02/H03 research
adapter with two-connection stale CAS, every ordinary H03 crash boundary,
missing evidence, surplus orphan evidence, and contaminated initialization.
The repair rejects any nonempty durable table before writing snapshot metadata,
performs staged canonical reopen before commit, and preserves the former
contaminated-initialization witness as a regression test.

COMMANDS_RUN:
- python3 -m ruff format experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m ruff check experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- python3 -m mypy --strict experiments/fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h08_independent_review.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h02_sqlite_publication.py tests/core/test_fcis_m6_h03_crash_points.py
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
- Ruff, strict mypy, packet validation, and the source manifest pass.

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
- No production datastore, caller, or value-moving path is mounted.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The initialization repair is fail-closed for the declared SQLite
research schema. A production datastore still needs an adapter-specific empty
store invariant, transaction semantics, crash recovery evidence, and startup
binding. The H02 adapter remains a large research hotspot.

