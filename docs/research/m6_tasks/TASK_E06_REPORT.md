# FCIS M6 Task E06 report: independent-connection concurrency

TASK_ID: E06
BASE_SHA: 7e8fd88bc84d80552c01ec53a331ec5d21aaeb0a
SOURCE_HEAD_SHA: 8d9140bed783032ae3e5ff1591803e74e70b9577
SOURCE_HEAD_TREE: 7aeecc7d05c283233adb125c229f34d3a79d631b
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_e06_concurrency_v1.json
- experiments/fcis_m6_e06_concurrency.py
- experiments/fcis_m6_e06_concurrency_check.py
- tests/core/test_fcis_m6_e06_concurrency.py
- tools/build_fcis_m6_e06_concurrency.py
- docs/research/m6_tasks/FCIS_M6_E06_CONCURRENCY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E06_CONCURRENCY_V1.json
- docs/research/m6_tasks/TASK_E06_PLAN.md
- docs/research/m6_tasks/TASK_E06_REPORT.md
- docs/research/m6_tasks/TASK_E06_EVIDENCE.json
- docs/research/m6_tasks/TASK_E06_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 8d9140bed783032ae3e5ff1591803e74e70b9577
IMPLEMENTATION_TREE: 7aeecc7d05c283233adb125c229f34d3a79d631b
IMPLEMENTATION_PARENT: 7e8fd88bc84d80552c01ec53a331ec5d21aaeb0a

CLAIM_IMPLEMENTED: E06 adds an independent-connection SQLite concurrency
harness for E05. Five required race families use barriers and fresh temporary
databases. Same-command retry, same-sender/nonce commands, and same-commit-ID
different-fingerprint races each produce one committed publication and one
STALE_SNAPSHOT_CAS result. Quiescence and authority-switch races linearize the
head change first and return one STALE_AUTHORITY_CAS publisher rejection with
no publication, nullifier, or effect rows.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e06_concurrency.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py`
- `python3 tools/build_fcis_m6_e06_concurrency.py`
- `python3 tools/build_fcis_m6_e06_concurrency.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e06_concurrency_check.py`
- `python3 -m py_compile experiments/fcis_m6_e06_concurrency.py experiments/fcis_m6_e06_concurrency_check.py tools/build_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e06_concurrency.py`
- `python3 -m ruff check experiments/fcis_m6_e06_concurrency.py experiments/fcis_m6_e06_concurrency_check.py tools/build_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e06_concurrency.py`
- `python3 -m ruff format --check experiments/fcis_m6_e06_concurrency.py experiments/fcis_m6_e06_concurrency_check.py tools/build_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e06_concurrency.py`
- `python3 -m mypy --strict experiments/fcis_m6_e06_concurrency.py experiments/fcis_m6_e06_concurrency_check.py tools/build_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e06_concurrency.py`
- `python3 -m json.tool config/deploy/fcis_m6_e06_concurrency_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E06_CONCURRENCY_V1.json`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E06`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E06_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused E06 suite passed: 2 passed.
- Combined E05/E06 suite passed: 14 passed.
- Independent checker passed: `E06_CONCURRENCY_CHECKS_PASS 5`.
- Source-bound vector regeneration and check passed:
  `E06_CONCURRENCY_VECTOR_MATCH`.
- Same-command retry: one committed, one `stale_snapshot_cas`, final counts
  publication/nullifier/effect = 1/1/1.
- Same-sender/nonce different command: one committed, one
  `stale_snapshot_cas`, final counts = 1/1/1.
- Same commit ID with different fingerprint: one committed, one
  `stale_snapshot_cas`, final counts = 1/1/1.
- Commit racing quiescence: head change plus `stale_authority_cas`, final
  counts = 0/0/0.
- Commit racing authority switch: head change plus `stale_authority_cas`,
  final counts = 0/0/0.
- Two complete campaigns produced byte-identical summaries.
- Ruff, Ruff formatting, strict mypy, Python compilation, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: E06 covers same-command duplicate publication, same-nullifier
different command, same commit ID with changed fingerprint, a publisher
entering while quiescence owns the head lock, a publisher entering while an
authority switch owns the head lock, worker failure, incomplete worker result,
and partial-row count mismatch. The independent connection/barrier harness
keeps each witness deterministic and checks the reopened durable layout.

FORMAL_EVIDENCE: None. E06 supplies executable independent-connection and
barrier evidence plus a repeatable source-bound vector. It does not add a
machine-checked theorem.

REMAINING_NONCLAIMS:
- E06 exercises the isolated SQLite adapter and does not prove production
  isolation, lock behavior, or concurrent linearizability under deployment
  settings.
- The quiescence and authority-switch actors mutate the E05 research head;
  they are not the real M6 migration authority machine.
- E06 does not prove network transport loss, process-crash recovery,
  filesystem durability, authenticated runtime callers, destination
  idempotency, accounting, backing, zUSD safety, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The harness verifies SQLite serialization and no-partial-row
outcomes for the tested adapter. It does not refine production datastore
configuration, connection pooling, retries across process boundaries, or the
real migration authority lifecycle.
