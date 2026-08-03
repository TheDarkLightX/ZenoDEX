# FCIS M6 Task C06 Report

TASK_ID: C06
BASE_SHA: 96f9fa3fa78bbe1f51a9da3be15a9026d8f84e0c
SOURCE_HEAD_SHA: 476ec022e755ff049c39bf9f08c6606ac87532ca
SOURCE_HEAD_TREE: a1d495eae0b26a369487ceb48cad5472abec74db
BRANCH: codex/task-C06-rotation-reset-mutants-20260801

IMPLEMENTATION_HEAD_SHA: f2967acfa7d1e744caac5cb85aceb7795f1e9fab
IMPLEMENTATION_TREE: 81572d8f9d44b166984152f2c6f6eb8612a72b05
IMPLEMENTATION_PARENT: 96f9fa3fa78bbe1f51a9da3be15a9026d8f84e0c

FILES_CHANGED:

- src/core/fcis_entitlement_rotation_admission_v1.py
- tests/core/test_fcis_entitlement_rotation_admission_v1.py
- docs/research/m6_tasks/TASK_C06_PLAN.md
- docs/research/FCIS_M6_C06_ROTATION_RESET_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_C06_REPORT.md
- docs/research/m6_tasks/TASK_C06_EVIDENCE.json
- docs/research/m6_tasks/TASK_C06_SOURCE_MANIFEST.sha256

CLAIM_IMPLEMENTED: C06 adds typed unmounted rotation snapshots and a
deployment-bound representation-migration comparison. Ordinary policy,
destination, and custody configuration changes are accepted only when the
exact C02 key, representation, and complete ordered residual history remain
unchanged. Migration checks bind source deployment, source authority epoch,
and current source state before invoking the C04 exact sign-dual transport.
Zero-reset, partial-entry, key, representation, history, and cross-deployment
substitutions reject with typed results.

COMMANDS_RUN:

- python3 -m compileall -q src/core/fcis_entitlement_rotation_admission_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 -m ruff check src/core/fcis_entitlement_rotation_admission_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 -m mypy --strict src/core/fcis_entitlement_rotation_admission_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- pytest -q tests/core/test_fcis_entitlement_rotation_admission_v1.py
- pytest -q tests/core/test_fcis_m6_profile_ids.py tests/core/test_fcis_entitlement_key_v1.py tests/core/test_fcis_entitlement_migration_v1.py tests/core/test_fcis_entitlement_transport_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 .claude/skills/zenodex-style-map/scripts/which_style.py src/core/fcis_entitlement_rotation_admission_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py
- python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py src/core/fcis_entitlement_rotation_admission_v1.py tests/core/test_fcis_entitlement_rotation_admission_v1.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks C06
- sha256sum --check --strict docs/research/m6_tasks/TASK_C06_SOURCE_MANIFEST.sha256

RESULTS:

- Focused C06 tests passed: 12 passed.
- Combined C01–C04/C06 regression tests passed: 53 passed.
- Python compilation passed.
- Ruff passed.
- Strict mypy passed.
- The stateful rotation sequence passed through policy, destination, and
  custody changes without changing the exact key or ordered residual history.
- Representation migration accepted only the exact C04 mapped target.
- Zero-reset and partial-entry migration mutants rejected at the authority
  comparison boundary.
- Cross-deployment source substitution rejected before transport evaluation.
- Repository-local style-map and security-analysis scripts are absent from
  this isolated repair tree; those commands failed because their paths are
  missing.
- The implementation identities above are exact local Git identities. No
  remote commit, hosted CI run, draft PR, or production promotion is claimed.
- The task validator and source-manifest check are run after this receipt is
  added.

MUTANTS_ADDED: Assertion-backed C06 cases cover policy rotation acceptance,
destination rotation acceptance, custody rotation acceptance, a stateful
rotation sequence, representation migration acceptance, key substitution,
representation substitution, residual-history mutation, zero-reset target,
partial-entry target, wrong context types, and cross-deployment state
substitution. No external mutation runner was used.

FORMAL_EVIDENCE: None added. C06 supplies typed executable comparison
evidence, a stateful rotation test sequence, and authority-boundary negative
tests. C04 supplies the tested sign-dual transport used by the migration
check; C05 supplies the separate Lean trace theorem.

REMAINING_NONCLAIMS:

- C06 does not authenticate deployment IDs or authority epoch roots; it checks
  their exact equality within a research context value.
- The accepted migration value is a check result, not an opaque production
  authority witness.
- C06 does not mount a caller, datastore, runtime authority, deployment,
  migration switch, destination worker, or value-moving path.
- C06 does not prove Python/Rust refinement, canonical serialization parity, or
  production state migration.
- No remote implementation commit, hosted CI run, draft PR, or production
  promotion is claimed.

REVIEW_RISKS: The deployment and epoch roots are format-checked research
inputs. Production must source them from authenticated current context and
perform the transport comparison in the same commit-time authority boundary.
The repository-local scanner paths are unavailable in this isolated tree and
were not replaced with weaker claims.
