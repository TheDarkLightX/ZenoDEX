# FCIS M6 Task H01 Report

TASK_ID: H01
BASE_SHA: a9eba746a5913649e2977ca5517ce8c42b470cae
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-H01-dra-publication-table-matrix-20260801
FILES_CHANGED:
- src/core/fcis_durable_retraction.py
- docs/research/m6_tasks/TASK_H01_PLAN.md
- docs/research/m6_tasks/TASK_H01_DRA_TABLE_MATRIX_V1.md
- docs/research/m6_tasks/TASK_H01_DRA_TABLE_MATRIX_V1.json
- experiments/fcis_m6_h01_table_matrix_check.py

IMPLEMENTATION_HEAD_SHA: 2c20dc2b46b3aba94c8676888e79a9a3d5c2aaba
IMPLEMENTATION_TREE: 601078bb300209c1dd7f26ca951d798d88ea50ed
IMPLEMENTATION_PARENT: a9eba746a5913649e2977ca5517ce8c42b470cae

CLAIM_IMPLEMENTED: H01 adds a source-pinned logical field-to-table matrix
covering every declared field of PublicationAtomV1 exactly once. Scalar atom
fields map to publication_atoms, context fields map to the canonical
snapshot_meta header with checked atom copies, and outbox maps to an ordered
publication_outbox projection. The packet also records authority, evidence,
nullifier, acknowledgment, snapshot-root, width, enum, collection, and
fixed-point relations. An executable checker compares the matrix field list
with dataclasses.fields(PublicationAtomV1) and fails on missing, duplicate, or
untyped entries.

COMMANDS_RUN:
- python3 -m json.tool docs/research/m6_tasks/TASK_H01_DRA_TABLE_MATRIX_V1.json
- PYTHONPATH=. python3 experiments/fcis_m6_h01_table_matrix_check.py
- python3 -m py_compile experiments/fcis_m6_h01_table_matrix_check.py
- python3 -m ruff check experiments/fcis_m6_h01_table_matrix_check.py
- python3 -m ruff format --check experiments/fcis_m6_h01_table_matrix_check.py
- python3 -m mypy --strict experiments/fcis_m6_h01_table_matrix_check.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H01
- sha256sum --check --strict docs/research/m6_tasks/TASK_H01_SOURCE_MANIFEST.sha256

RESULTS:
- The JSON matrix parsed successfully.
- The exhaustive checker passed with H01_TABLE_MATRIX_MATCH.
- Python compilation, Ruff, Ruff formatting, and strict mypy passed.
- The source model hash matches the same file at SOURCE_HEAD_SHA.
- The packet validator and source manifest checks are recorded after the
  receipt-only commit is created.
- The matrix explicitly retains anf_root as an H02/H07 boundary because the
  current PublicationAtomV1 has no such field.

MUTANTS_ADDED: None. The checker has fail-closed branches for duplicate,
missing, unsupported-role, missing locator, and missing relation entries.

FORMAL_EVIDENCE: None. H01 supplies a source-pinned logical relation matrix
and an executable structural checker; it adds no machine-checked theorem.

REMAINING_NONCLAIMS:
- H01 does not implement SQLite, PostgreSQL, RocksDB, or another datastore
  adapter.
- H01 does not prove transaction atomicity, isolation, WAL/fsync durability,
  crash recovery, concurrent linearization, or deployment configuration.
- H01 does not prove that production callers supply authenticated atoms or
  that any runtime publisher enforces the matrix.
- H01 does not define or prove the atomic ANF-root relation; that boundary is
  explicitly deferred to H02/H07.
- M6 remains unmounted and non-promotable. Outbox, migration, no-bypass,
  whole-system accounting, and value-moving obligations remain open.

REVIEW_RISKS: The table names and constraints are a proposed logical
refinement contract. They have not yet been instantiated against a concrete
datastore, and repeated foreign-key or cache values remain projections until
an adapter proves the stated equality and full-layout fixed point. The
research model stores digest roots rather than the referenced proof or
response bytes, so root presence does not establish blob durability.
