# FCIS M6 Task E03 Report

TASK_ID: E03
BASE_SHA: 82aa75bfdaced4577404f2ce05e8ea06ed09640e
SOURCE_HEAD_SHA: cb47c333f13b47b2ced5ac668faf1bbddcd80a5b
SOURCE_HEAD_TREE: f33fc2ed362a1e8198faaae1b235384502a65d17
BRANCH: codex/task-m6-receipt-rebind-20260802
FILES_CHANGED:
- config/deploy/fcis_m6_e03_uniqueness_v1.json
- config/deploy/fcis_m6_e03_uniqueness_v1.sql
- docs/research/m6_tasks/FCIS_M6_E03_DATABASE_UNIQUENESS_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E03_DATABASE_UNIQUENESS_V1.json
- docs/research/m6_tasks/TASK_E03_PLAN.md
- docs/research/m6_tasks/TASK_E03_SOURCE_MANIFEST.sha256
- experiments/fcis_m6_e03_database_uniqueness.py
- experiments/fcis_m6_e03_database_uniqueness_check.py
- src/core/fcis_m6_e03_unique_commit_port.py
- tests/core/test_fcis_m6_e03_database_uniqueness.py
- tools/build_fcis_m6_e03_database_uniqueness.py

IMPLEMENTATION_HEAD_SHA: cb47c333f13b47b2ced5ac668faf1bbddcd80a5b
IMPLEMENTATION_TREE: f33fc2ed362a1e8198faaae1b235384502a65d17
IMPLEMENTATION_PARENT: 82aa75bfdaced4577404f2ce05e8ea06ed09640e

CLAIM_IMPLEMENTED: E03 refines one verifier-derived E02 nullifier into a
verifier-owned complete commit identity aggregate. The aggregate derives
effect IDs from commit and effect fields, derives a canonical fingerprint over
the complete ordered identity, and rejects invalid, forged, mutated, reordered,
or over-bounded values. The isolated SQLite shell publishes the commit,
nullifier, and effect rows in one transaction. Primary keys, unique
constraints, composite foreign-key binding, and rollback make duplicate
commit IDs, nullifiers, effect IDs, and per-commit ordinals fail closed at the
datastore boundary.

COMMANDS_RUN:
- `python3 tools/build_fcis_m6_e03_database_uniqueness.py`
- `python3 tools/build_fcis_m6_e03_database_uniqueness.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e03_database_uniqueness_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_*.py`
- `python3 -m py_compile src/core/fcis_m6_e03_unique_commit_port.py experiments/fcis_m6_e03_database_uniqueness.py experiments/fcis_m6_e03_database_uniqueness_check.py tools/build_fcis_m6_e03_database_uniqueness.py tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `python3 -m ruff check src/core/fcis_m6_e03_unique_commit_port.py experiments/fcis_m6_e03_database_uniqueness.py experiments/fcis_m6_e03_database_uniqueness_check.py tools/build_fcis_m6_e03_database_uniqueness.py tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `python3 -m ruff format --check src/core/fcis_m6_e03_unique_commit_port.py experiments/fcis_m6_e03_database_uniqueness.py experiments/fcis_m6_e03_database_uniqueness_check.py tools/build_fcis_m6_e03_database_uniqueness.py tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `python3 -m mypy --strict src/core/fcis_m6_e03_unique_commit_port.py experiments/fcis_m6_e03_database_uniqueness.py experiments/fcis_m6_e03_database_uniqueness_check.py tools/build_fcis_m6_e03_database_uniqueness.py tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `python3 -m json.tool config/deploy/fcis_m6_e03_uniqueness_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E03_DATABASE_UNIQUENESS_V1.json`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E03_SOURCE_MANIFEST.sha256`
- `git diff --check`

RESULTS:
- E03 vector regenerated with migration hash
  `bf03f9f0fcdb46ac507d6c7bd80ab3def6c11890d0ce2c6d328bfdaced672efb`,
  fingerprint
  `6cb9fdd797c4f1b462eaf9f65c19b07690a4092da32b844a942c026714555ad1`,
  and effect ID
  `b9255903f7bdf3b4c49f89232d0d362289e72c0446e28491f17b7f1f0a2b7103`.
- Focused E03 suite passed: 8 passed.
- Complete M6 core regression passed: 240 passed in 255.72 seconds.
- Independent checker passed: `E03_UNIQUENESS_MATCH`.
- Successful insertion published one commit, one nullifier, and one effect
  row; exact duplicate and same-nullifier/different-commit attempts returned
  `CONSTRAINT_COLLISION` without changing row counts.
- Direct hostile effect-ID reuse was rejected by the SQLite primary key.
- An injected failure after nullifier insertion returned `SQL_ROLLBACK` and
  left all three identity tables unchanged.
- Two concurrent duplicate insertions produced exactly one `COMMITTED` result
  and one `CONSTRAINT_COLLISION` result.
- Ruff, formatting, strict mypy, Python compilation, JSON parsing, vector
  freshness, source-manifest verification, and diff whitespace checks passed.
- No Lean theorem, production datastore, runtime mount, authority switch,
  deployment, migration activation, or value movement is claimed.

MUTANTS_ADDED: E03 covers caller-minted identity, exact-class forged identity,
mutated registered identity, Boolean ordinal, control-character destination,
non-tuple effects, noncanonical effect ordering, duplicate commit identity,
same-nullifier/different-commit collision, duplicate effect ID, injected
partial-insert failure, and concurrent duplicate insertion. Each is rejected
by the core boundary, the SQL constraint, or the atomic rollback test named in
the packet.

FORMAL_EVIDENCE: None. E03 supplies a typed executable identity relation, a
source-bound SQL migration, deterministic vector, SQLite transaction tests,
concurrency evidence, and mutation-killing tests. It does not add a
machine-checked theorem or production-durability proof.

REMAINING_NONCLAIMS:
- E03 consumes E02 authentication and nullifier provenance as an external
  research premise; it does not implement cryptographic authentication.
- E03 does not prove that a caller supplies a valid commit ID or that every
  production publisher reaches this port.
- E03 does not classify exact duplicates as already-committed retries. E04
  must read the durable fingerprint, command identity, expected root, and
  current state to produce the total retry partition.
- The SQLite experiment does not prove WAL/fsync behavior, process-crash
  recovery, production isolation settings, filesystem durability, destination
  idempotency, runtime reachability, migration authority, accounting, backing,
  zUSD safety, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The migration is an isolated E03 identity schema rather than a
mounted H02 production adapter. The composite foreign key binds the stored
nullifier projection to the E03 commit row, while effect-field binding remains
owned by the verifier-derived aggregate and staged-row revalidation. E04 and
the later H05-H08 work must connect this port to retry classification,
complete publication, crash recovery, and real datastore configuration.
