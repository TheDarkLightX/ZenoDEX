# FCIS M6 Task J08 Report

TASK_ID: J08
BASE_SHA: b72aa9d997e7cfb5db49e8ea91dcebba2a1f2193
SOURCE_HEAD_SHA: 4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6
SOURCE_HEAD_TREE: 95ae78274eb6695be508283bd34eac2e3118b093
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_j08_rollback_v1.json
- docs/research/m6_tasks/TASK_J08_ROLLBACK_V1.json
- experiments/fcis_m6_j08_rollback_check.py
- src/core/fcis_m6_j08_rollback.py
- tests/core/test_fcis_m6_j08_rollback.py
- tests/core/test_fcis_m6_j08_rollback_properties.py
- tools/build_fcis_m6_j08_rollback.py

IMPLEMENTATION_HEAD_SHA: d92c98fd9911741c2be6a3a1af9d7d1ff1bccbb3
IMPLEMENTATION_TREE: f409c5381210827160a016f9eec78755b3f4690c
IMPLEMENTATION_PARENT: b72aa9d997e7cfb5db49e8ea91dcebba2a1f2193

DEPENDENCY_REFRESH_HEAD: 4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6
DEPENDENCY_REFRESH_TREE: 95ae78274eb6695be508283bd34eac2e3118b093
DEPENDENCY_REFRESH_PARENT: 6b3110f3d392d9fa23727e6b1e63be7edce6f8c2

DEPENDENCY_REBIND: The J07 switch rebind changed the complete source state
used by J08. J08 was regenerated at the exact dependency-refresh head above;
J08 implementation code is unchanged.

CLAIM_IMPLEMENTED: J08 defines an isolated verifier-gated rollback relation
over a complete state aggregate. The J07 post-switch source and pre-switch
anchor must agree on history, residual, nullifier, outbox, and effect identity
roots. The target restores all of those roots plus current state and
deployment configuration, appends a rollback history commitment, advances the
authority epoch exactly once, enters POST_SWITCH_VALIDATION, disables writers,
and requires fresh authorization.

COMMANDS_RUN:
- `PYTHONPATH=. python3 experiments/fcis_m6_j08_rollback_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_j08_rollback.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_j08_rollback.py tests/core/test_fcis_m6_j08_rollback_properties.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_j01_migration_lifecycle.py tests/core/test_fcis_m6_j02_writer_matrix.py tests/core/test_fcis_m6_j03_transport_map.py tests/core/test_fcis_m6_j04_migration_manifest.py tests/core/test_fcis_m6_j05_shadow_dual_check.py tests/core/test_fcis_m6_j06_quiescence.py tests/core/test_fcis_m6_j07_authority_switch.py tests/core/test_fcis_m6_j07_authority_switch_properties.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `python3 -m ruff check` on all J08 source, checker, tool, and test files
- `python3 -m ruff format --check` on all J08 source, checker, tool, and test files
- `python3 -m mypy --strict` on all J08 source, checker, tool, and test files
- `python3 -m py_compile` on all J08 Python files
- `python3 -m json.tool` on the J08 configuration and vector
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J08`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_J08_SOURCE_MANIFEST.sha256`

RESULTS:
- The independent checker passed with rollback root
  `a96d917c3939f277fec0ecf525f2413984403e4a4222b9d70b5ebeefbea69fa6`.
- The public vector matched source regeneration.
- Focused and property tests passed: 11 passed.
- The adjacent regression passed: 55 passed in 4.65 seconds.
- The target restored current-state, deployment, residual, nullifier, outbox,
  and effect-identity roots from the pre-switch anchor.
- The target history root changed through a canonical rollback commitment;
  history was not erased.
- The rollback advanced authority epoch 4 to 5, entered
  POST_SWITCH_VALIDATION, disabled writers, required fresh authorization, and
  exposed no value-moving capability.
- Source/anchor auxiliary-root disagreement rejected before target creation.
- Six target root substitutions and history erasure rejected during
  certificate validation.
- Strict Ruff, formatting, mypy, compilation, JSON, and diff checks passed.

MUTANTS_ADDED: Forged source state root, forged anchor residual root,
balance-only target state, deployment-only target mutation, residual-only
target mutation, nullifier-only target mutation, outbox-only target mutation,
effect-identity-only target mutation, history erasure, stale sequence, wrong
reason, wrong switch type, and empty/over-capacity/overlong rejection paths.

FORMAL_EVIDENCE: No new Lean theorem is claimed. J08 supplies a typed
deterministic relation, canonical roots, property evidence, and adversarial
negative evidence.

REMAINING_NONCLAIMS:
- J08 is research-only and unmounted.
- The complete-state verifier and construction registry are model premises;
  they do not authenticate production state.
- J08 does not prove a datastore transaction, crash recovery, filesystem
  durability, runtime reachability, no-bypass coverage, migration deployment,
  accounting, backing, or zUSD safety.
- M6 remains unmounted and non-promotable.

REVIEW_RISKS: The functional source is a 661-line hotspot and the checker is
an independent research fixture. A production refinement must replace the
research provenance registry with authenticated complete-state evidence and
perform the rollback aggregate atomically with history, authority, residual,
nullifier, outbox, and effect-identity rows. The target writer set remains
quiescent until a separate fresh authorization transition.
