# FCIS M6 Task H07 Report

TASK_ID: H07
BASE_SHA: 568cdc014731c5f6d9c6b767af4baceaf7c64cb5
SOURCE_HEAD_SHA: 42b5f29e82d76df41f8c1ed25c8b4fefa675ae9a
SOURCE_HEAD_TREE: 876eccc843c9c366eb2385c966f56f6aa0bbc7a8
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- docs/research/m6_tasks/TASK_H07_REFINEMENT_MATRIX_V1.json
- tools/check_fcis_m6_h07_refinement_matrix.py
- tests/core/test_fcis_m6_h07_refinement_matrix.py
- docs/research/m6_tasks/TASK_H07_PLAN.md

IMPLEMENTATION_HEAD_SHA: 42b5f29e82d76df41f8c1ed25c8b4fefa675ae9a
IMPLEMENTATION_TREE: 876eccc843c9c366eb2385c966f56f6aa0bbc7a8
IMPLEMENTATION_PARENT: 568cdc014731c5f6d9c6b767af4baceaf7c64cb5

CLAIM_IMPLEMENTED: H07 supplies a closed, fail-closed refinement matrix for
the nine required DRA actions. Every row names the SQL transaction or records
an explicit open nonclaim, isolation assumptions, uniqueness constraints,
recovery behavior, and executable or packet evidence. The checker rejects
registry omissions, duplicate or unknown actions, missing fields, empty
evidence/nonclaim lists, and invalid field types.

COMMANDS_RUN:
- python3 tools/check_fcis_m6_h07_refinement_matrix.py docs/research/m6_tasks/TASK_H07_REFINEMENT_MATRIX_V1.json
- python3 -m ruff format tools/check_fcis_m6_h07_refinement_matrix.py tests/core/test_fcis_m6_h07_refinement_matrix.py
- python3 -m ruff check tools/check_fcis_m6_h07_refinement_matrix.py tests/core/test_fcis_m6_h07_refinement_matrix.py
- python3 -m mypy --strict tools/check_fcis_m6_h07_refinement_matrix.py tests/core/test_fcis_m6_h07_refinement_matrix.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_h07_refinement_matrix.py
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks H07
- sha256sum --check --strict docs/research/m6_tasks/TASK_H07_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- The H07 matrix checker accepted all nine required DRA actions.
- Ruff formatted one H07 source file, then Ruff check passed.
- Strict mypy passed for the checker and focused test.
- The focused H07 test passed: 1 passed.
- The packet validator and source manifest passed after the receipt commit.
- H02, H03, H04, and H06 remain independently packeted with their prior
  receipts and source manifests.

MUTANTS_ADDED: None. H07 is a structural refinement registry and checker; its
negative coverage is the fail-closed rejection of malformed or incomplete
matrix rows. The underlying transaction mutants remain covered by H02-H04.

FORMAL_EVIDENCE: None. H07 adds no machine-checked theorem. It records the
refinement boundary needed before a mounted datastore claim.

REMAINING_NONCLAIMS:
- H07 does not implement or verify a destination acknowledgment worker,
  retry classifier, or destination idempotency.
- H07 does not construct a full verifier-produced authority-transition atom.
- H07 does not bind the H06 durability profile to production startup or prove
  filesystem/power-loss durability.
- H07 does not prove concurrent linearizability, a production datastore
  refinement, runtime reachability, migration, no-bypass coverage, whole-
  system accounting, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The matrix is complete relative to its closed nine-action
registry, while several rows intentionally remain OPEN_NONCLAIM or carry a
fixture/mount gap. The 922-line H02 adapter and its long publication path
remain auditability risks. A future H08 review must attack the exact action
rows and preserve the open boundaries.

