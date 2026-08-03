# FCIS M6 Task C04 Report

TASK_ID: C04
BASE_SHA: ccc04a72a3d2feb612e52d40e8d393f3f6b117c3
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C04-sign-dual-transport-20260801

IMPLEMENTATION_HEAD_SHA: 559d11b6c0c13c763432a3ee07eb0426198baa32
IMPLEMENTATION_TREE: 3545c56263714dbc9efcf181e44f902dff489256
IMPLEMENTATION_PARENT: ccc04a72a3d2feb612e52d40e8d393f3f6b117c3

FILES_CHANGED:

- src/core/fcis_entitlement_transport_v1.py
- tests/core/test_fcis_entitlement_transport_v1.py
- experiments/fcis_m6_c04_vector_check.py
- docs/research/FCIS_M6_C04_SIGN_DUAL_TRANSPORT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_C04_PLAN.md
- docs/research/m6_tasks/TASK_C04_SIGN_DUAL_VECTOR.json
- docs/research/m6_tasks/TASK_C04_REPORT.md
- docs/research/m6_tasks/TASK_C04_EVIDENCE.json
- docs/research/m6_tasks/TASK_C04_SOURCE_MANIFEST.sha256

CLAIM_IMPLEMENTED: C04 adds a typed unmounted SRGD-to-AGQE transport that
negates every coordinate in the complete ordered entry set, preserves the
exact C02 semantic key and fixed role order, and exposes the inverse transport
for executable involution checks. A supplied target is accepted only after
strict source/target validation, direction-specific representation checks,
key equality, exact ordered entry equality, and coordinate equality. Zero
replacement of a nonzero source entry is a typed zero-reset rejection.

COMMANDS_RUN:

- python3 -m compileall -q src/core/fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- python3 -m ruff check src/core/fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- python3 -m mypy --strict src/core/fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- pytest -q tests/core/test_fcis_entitlement_transport_v1.py
- pytest -q tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- python3 -m experiments.fcis_m6_c04_vector_check
- python3 -m compileall -q experiments/fcis_m6_c04_vector_check.py
- python3 -m ruff check experiments/fcis_m6_c04_vector_check.py
- python3 -m mypy --strict experiments/fcis_m6_c04_vector_check.py
- python3 -m json.tool docs/research/m6_tasks/TASK_C04_SIGN_DUAL_VECTOR.json
- python3 experiments/fcis_m6_c04_vector_check.py
- python3 .claude/skills/zenodex-style-map/scripts/which_style.py src/core/fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py
- python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py src/core/fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_transport_v1.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks C04
- sha256sum --check --strict docs/research/m6_tasks/TASK_C04_SOURCE_MANIFEST.sha256

RESULTS:

- Focused C04 tests passed: 9 passed.
- Combined C03/C04 regression tests passed: 23 passed.
- Python compilation passed for the implementation, tests, and vector checker.
- Ruff passed for the implementation, tests, and vector checker.
- Strict mypy passed for the implementation, tests, and vector checker.
- The module-form vector checker passed: C04_VECTOR_MATCH.
- The vector JSON parsed successfully.
- The direct-file vector invocation failed with ModuleNotFoundError for the
  repository `src` package; module-form execution from the repository root is
  the accepted reproducible command and the failure is retained as a witness.
- The repository-local style-map and security-analysis scripts are absent from
  this isolated repair tree; their commands failed because their paths are
  missing.
- The implementation commit and tree above are local exact identities. No
  remote commit, hosted CI run, draft PR, or production promotion is claimed.
- The task validator and source-manifest check are run after this receipt is
  added.
- Git diff check passed before the implementation commit.

MUTANTS_ADDED: Assertion-backed C04 rejection cases cover wrong source type,
wrong source representation, wrong target type, wrong target representation,
semantic-key substitution, missing entry, surplus entry, coordinate drift,
and zero-reset history erasure. The involution test also detects a one-way or
non-negating transport implementation. No external mutation runner was used.

FORMAL_EVIDENCE: None added. C04 supplies typed executable relation evidence,
negative tests, canonical state roots, and an independent deterministic vector.
C05 remains responsible for the Lean complete-trace conjugacy theorem.

REMAINING_NONCLAIMS:

- C04 does not prove the complete allocator trace or establish a Lean theorem.
- C04 does not authenticate the migration authority epoch or bind a transport
  to authenticated current state.
- C04 does not mount a caller, datastore, runtime authority, deployment,
  migration switch, destination, or value-moving path.
- C04 does not establish policy, destination, or custody rotation behavior;
  C06 owns those broader mutation and stateful tests.
- No remote implementation commit, hosted CI run, draft PR, or production
  promotion is claimed.

REVIEW_RISKS: The exact target passed to the comparison function is a research
verifier input. A production migration adapter must obtain both source and
target state from authenticated current context, preserve authority epoch and
deployment binding, and make the transport check part of the same commit-time
acceptance boundary. The external-worktree patch helper was unavailable for
one mechanical type-only correction, which was applied as a narrowly scoped
file edit under the approved isolated worktree; the final staged diff was
reviewed and committed exactly.
