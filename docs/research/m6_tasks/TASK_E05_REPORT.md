# FCIS M6 Task E05 report: expected-root atomic CAS

TASK_ID: E05
BASE_SHA: 48b471ea3ae1b07c876a128ed7f17bc595227001
SOURCE_HEAD_SHA: 96273b95ba8dba68fb1b7544dc4fa9f33eb2bf83
SOURCE_HEAD_TREE: c49338d88f4173318744df2fcc442360b556f336
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_e05_expected_root_cas_v1.json
- experiments/fcis_m6_e05_expected_root_cas.py
- experiments/fcis_m6_e05_expected_root_cas_check.py
- src/core/fcis_m6_e05_expected_root_cas.py
- tests/core/test_fcis_m6_e05_expected_root_cas.py
- tools/build_fcis_m6_e05_expected_root_cas.py
- docs/research/m6_tasks/FCIS_M6_E05_EXPECTED_ROOT_CAS_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E05_EXPECTED_ROOT_CAS_V1.json
- docs/research/m6_tasks/TASK_E05_PLAN.md
- docs/research/m6_tasks/TASK_E05_REPORT.md
- docs/research/m6_tasks/TASK_E05_EVIDENCE.json
- docs/research/m6_tasks/TASK_E05_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 96273b95ba8dba68fb1b7544dc4fa9f33eb2bf83
IMPLEMENTATION_TREE: c49338d88f4173318744df2fcc442360b556f336
IMPLEMENTATION_PARENT: 48b471ea3ae1b07c876a128ed7f17bc595227001

CLAIM_IMPLEMENTED: E05 adds an isolated SQLite transaction port that begins
with BEGIN IMMEDIATE, runs the E04 classifier over a verifier-owned
predecessor and matching reopen receipt, compares the complete predecessor
projection, performs one SQL CAS over state/snapshot/authority/profile/
sequence/publication-set roots, inserts the complete E04 publication,
nullifier, and effect projections, reopens the staged rows, and commits only
when the exact successor layout is recovered. The transaction has no
preflight-read followed by an unguarded write path.

COMMANDS_RUN:
- `python3 -m pytest -q tests/core/test_fcis_m6_e05_expected_root_cas.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_*.py`
- `python3 tools/build_fcis_m6_e05_expected_root_cas.py`
- `python3 tools/build_fcis_m6_e05_expected_root_cas.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e05_expected_root_cas_check.py`
- `python3 -m py_compile src/core/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas_check.py tools/build_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e05_expected_root_cas.py`
- `python3 -m ruff check src/core/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas_check.py tools/build_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e05_expected_root_cas.py`
- `python3 -m ruff format --check src/core/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas_check.py tools/build_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e05_expected_root_cas.py`
- `python3 -m mypy --strict src/core/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas.py experiments/fcis_m6_e05_expected_root_cas_check.py tools/build_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e05_expected_root_cas.py`
- `python3 -m json.tool config/deploy/fcis_m6_e05_expected_root_cas_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E05_EXPECTED_ROOT_CAS_V1.json`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E05`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E05_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused E05 tests passed: 12 passed.
- Full M6 core regression passed: 272 passed in 251.70 seconds.
- Independent checker passed: `E05_EXPECTED_ROOT_CAS_CHECKS_PASS`.
- Source-bound vector regeneration and check passed:
  `E05_EXPECTED_ROOT_CAS_VECTOR_MATCH`.
- The trace witness begins with `BEGIN IMMEDIATE`; the SQL head update is
  observed before publication insertion.
- One valid request commits one publication, one nullifier, and one effect;
  the receipt and reopened successor roots match.
- A retry carrying the old predecessor returns `STALE_SNAPSHOT_CAS` without
  changing rows.
- Mutated state and authority head fields return typed stale rejection.
- A trigger abort returns `SQL_ROLLBACK` and removes the head, publication,
  nullifier, and effect changes together.
- Nested attempt-wire mutation, missing effect projection, and crossed
  nullifier projection reject during reopen.
- Ruff, Ruff formatting, strict mypy, Python compilation, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: E05 covers old-predecessor retry, state-root mutation,
authority-epoch mutation, head-CAS ordering, trigger abort after partial
publication, direct effect-ID reuse, forged E04 state, crossed reopen receipt,
nested attempt-wire mutation, missing effect projection, and crossed nullifier
projection. Each witness is rejected by typed validation, the SQL CAS, schema
constraints, exact projection comparison, or transaction rollback.

FORMAL_EVIDENCE: None. E05 supplies a typed executable transaction contract,
source-bound vector, independent checker, SQL CAS trace evidence, and
mutation-killing tests. It does not add a machine-checked theorem.

REMAINING_NONCLAIMS:
- E05 consumes E04 verifier-owned attempt, state, and reopen-receipt values as
  research premises; it does not implement cryptographic authentication.
- The SQLite adapter is not a production datastore refinement and does not
  prove WAL/fsync behavior, filesystem durability, process-crash recovery,
  deployment isolation, or concurrent linearizability under production
  settings.
- The reopen receipt remains an external verifier-port premise; the adapter
  does not prove that a production datastore supplied a fresh authentic
  receipt.
- E05 does not mount runtime callers, destination authentication/idempotency,
  migration authority, no-bypass coverage, accounting, backing, zUSD safety,
  or value movement.
- E05 does not complete H02's DRA publication atom, proof-context, recovery,
  outbox, migration, or whole-system M6 obligations.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The E05 adapter is a research hotspot and stores canonical E04
attempt bytes alongside normalized projections. Its exact projection checks
reduce internal mutation risk, while production schema, authenticated
datastore reads, isolation configuration, crash recovery, and complete DRA
publication refinement remain open.
