# FCIS M6 Task E03 Report

TASK_ID: E03
BASE_SHA: baa135380e7bd25072ad82a8bfa337e9c634c9d3
SOURCE_HEAD_SHA: 0f054387b3b8e378cf29323d58e00c79d3bfa90d
SOURCE_HEAD_TREE: 564c14735646704d9d23e2c92c543e21d8579e09
BRANCH: codex/task-E03-replayable-unique-commit-20260802
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

IMPLEMENTATION_HEAD_SHA: 0f054387b3b8e378cf29323d58e00c79d3bfa90d
IMPLEMENTATION_TREE: 564c14735646704d9d23e2c92c543e21d8579e09
IMPLEMENTATION_PARENT: 4b8a81f41216350150d6568b22b4977729b4c105

CLAIM_IMPLEMENTED: E03 refines one verifier-derived E02 nullifier into a
replayable complete commit identity aggregate. The aggregate retains a
canonical fingerprint seal over the complete ordered sources and is freshly
rederived without a process-local object registry at every verifier and
persistence boundary. The isolated SQLite shell accepts only the pinned
migration and an idle connection whose foreign-key mode and complete
main-schema descriptor match that migration. It snapshots immutable
publication rows before opening one transaction, repeats the connection
contract after acquiring `BEGIN IMMEDIATE`, and rolls back only a transaction
it acquired. Primary keys, unique constraints, composite foreign-key binding,
staged-row equality, and rollback make duplicate or partial identity
publication fail closed.

COMMANDS_RUN:
- `python3 tools/build_fcis_m6_e03_database_uniqueness.py`
- `python3 tools/build_fcis_m6_e03_database_uniqueness.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e03_database_uniqueness_check.py`
- `PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_e01_request_identity.py tests/core/test_fcis_m6_e02_nonce_nullifier.py tests/core/test_fcis_m6_e03_database_uniqueness.py`
- `PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_*.py`
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
- Focused E03 suite passed: 16 passed.
- E01-E03 refinement regression passed: 27 passed.
- Complete M6 core regression passed: 249 passed in 248.28 seconds.
- Independent checker passed: `E03_UNIQUENESS_MATCH`.
- Successful insertion published one commit, one nullifier, and one effect
  row; exact duplicate and same-nullifier/different-commit attempts returned
  `CONSTRAINT_COLLISION` without changing row counts.
- Direct hostile effect-ID reuse was rejected by the SQLite primary key.
- An injected failure after nullifier insertion returned `SQL_ROLLBACK` and
  left all three identity tables unchanged.
- Two concurrent duplicate insertions produced exactly one `COMMITTED` result
  and one `CONSTRAINT_COLLISION` result.
- A modified migration file, a pre-existing loose schema, an added trigger,
  and disabled foreign keys were rejected before publication. An
  already-active caller transaction was rejected without rollback or loss of
  its caller-owned row.
- Schema drift introduced after the precheck was rejected after E03 acquired
  the write transaction. A caller transaction started after the precheck was
  preserved because E03 records whether `BEGIN IMMEDIATE` succeeded before it
  may roll back.
- Fresh E03 derivation reconstructed the exact wire value without a process
  registry. A valid nested effect mutation broke the retained fingerprint seal.
- Ruff, formatting, strict mypy, Python compilation, JSON parsing, vector
  freshness, source-manifest verification, and diff whitespace checks passed.
- No Lean theorem, production datastore, runtime mount, authority switch,
  deployment, migration activation, or value movement is claimed.

MUTANTS_ADDED: E03 covers process-registry dependence, caller-minted identity,
exact-class forged identity, outer and nested mutation, Boolean ordinal,
control-character destination, non-tuple effects, noncanonical effect order,
modified migration SQL, pre-existing loose schema, point-of-use schema drift,
schema drift after the precheck, foreign keys disabled, caller-owned active
transaction at entry or after the precheck, duplicate commit identity,
same-nullifier/different-commit collision, duplicate effect ID, denied partial
insert, and concurrent duplicate insertion. Each is rejected by source replay,
the fingerprint seal, the connection contract, a SQL constraint, or atomic
rollback.

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
- E03 does not prove exclusive scheduling for an externally supplied SQLite
  connection configured for cross-thread use. A production port must own its
  connection/transaction scheduling capability.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The migration is an isolated E03 identity schema rather than a
mounted H02 production adapter. Exact schema comparison is runtime-local
attestation against the pinned migration source; it is not a production
migration authority, filesystem durability proof, or no-bypass result. The
composite foreign key binds the stored nullifier projection to the E03 commit
row, while effect-field binding remains owned by source replay, the retained
fingerprint, immutable publication rows, and staged-row revalidation. E04 and
the later H05-H08 work must connect this port to retry classification,
complete publication, crash recovery, exclusive connection ownership, and
real datastore configuration.
