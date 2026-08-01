# FCIS M6 Task J04 Report

TASK_ID: J04
BASE_SHA: accbd4fb82d0a70a9d0aff850ec7696f0d447f13
SOURCE_HEAD_SHA: 5fff44d7fd542838b5a69436a614a08889fd0780
SOURCE_HEAD_TREE: d316e3f7e8a7c1e796be1cb32c8060e0fba3d263
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- tools/check_fcis_m6_j04_migration_manifest.py
- tests/core/test_fcis_m6_j04_migration_manifest.py
- docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json
- docs/research/m6_tasks/TASK_J04_PLAN.md

IMPLEMENTATION_HEAD_SHA: 5fff44d7fd542838b5a69436a614a08889fd0780
IMPLEMENTATION_TREE: d316e3f7e8a7c1e796be1cb32c8060e0fba3d263
IMPLEMENTATION_PARENT: accbd4fb82d0a70a9d0aff850ec7696f0d447f13

CLAIM_IMPLEMENTED: J04 adds a canonical root- and sequence-bound migration
manifest. It binds source and target profile, deployment, configuration,
state, and history roots; three transport checker/root pairs; activation
sequence; complete rollback rules; six quiescence markers; complete replay
evidence; and a canonical self-hash. The checker rejects profile/configuration
identity collapse, missing transport checkers, incomplete quiescence, invalid
activation or rollback windows, and stale manifest roots.

COMMANDS_RUN:
- python3 tools/check_fcis_m6_j04_migration_manifest.py docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_j04_migration_manifest.py
- python3 -m ruff check tools/check_fcis_m6_j04_migration_manifest.py tests/core/test_fcis_m6_j04_migration_manifest.py
- python3 -m ruff format --check tools/check_fcis_m6_j04_migration_manifest.py tests/core/test_fcis_m6_j04_migration_manifest.py
- python3 -m mypy --strict tools/check_fcis_m6_j04_migration_manifest.py tests/core/test_fcis_m6_j04_migration_manifest.py
- python3 -m py_compile tools/check_fcis_m6_j04_migration_manifest.py tests/core/test_fcis_m6_j04_migration_manifest.py
- python3 -m json.tool docs/research/m6_tasks/TASK_J04_MIGRATION_MANIFEST_V1.json
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J04
- sha256sum --check --strict docs/research/m6_tasks/TASK_J04_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- The J04 checker accepted the canonical manifest and self-hash.
- Focused J04 suite passed: 6 passed.
- Changing target configuration to the source configuration rejected.
- Missing quiescence evidence rejected.
- A transport row without a checker rejected.
- Zero activation sequence rejected.
- Changing any canonical body field changes the manifest root.
- The schema parsed as valid JSON.
- Ruff, formatting, strict mypy, Python compilation, packet validation, the
  source manifest, and diff whitespace checks pass.

MUTANTS_ADDED: None. The focused suite contains negative witnesses for source/
target configuration collapse, incomplete quiescence, missing transport
checker, and invalid activation sequence.

FORMAL_EVIDENCE: None. J04 supplies executable manifest-binding evidence; it
adds no machine-checked theorem or completed migration transport proof.

REMAINING_NONCLAIMS:
- J04 does not prove any state, fee, receipt, nullifier, history,
  proof-context, configuration, or outbox transport relation.
- J04 does not implement migration, writer exclusion, rollback, datastore
  behavior, runtime reachability, no-bypass coverage, accounting, backing, or
  zUSD safety.
- Transport checker IDs, roots, replay roots, and quiescence markers are
  research obligations and are not completed production receipts.
- No production migration, datastore, caller, worker, destination, or
  value-moving path is mounted. M6 remains research-only and non-promotable.

REVIEW_RISKS: The self-hash proves internal manifest consistency only. It does
not authenticate an external migration authority or prove that the named
transport, replay, rollback, and quiescence evidence exists. J05-J08 must
replace the research obligations with independently verified runtime evidence.
