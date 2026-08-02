TASK_ID: F08
BASE_SHA: 0da87995c3564cfcba6ca4a9b8fe35c1f8ad0472
SOURCE_HEAD_SHA: ebcf0a6377f6b7a58a089a32f63093158a8f7e94
SOURCE_HEAD_TREE: 7fda9c0400ac30fbaab0f1ecac2882e394690461
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f08_recovery_v1.json
- src/core/fcis_m6_f08_recovery_faults.py
- experiments/fcis_m6_f08_recovery_faults_check.py
- tests/core/test_fcis_m6_f08_recovery_faults.py
- tests/core/test_fcis_m6_f08_recovery_faults_properties.py
- tools/build_fcis_m6_f08_recovery_faults.py
- docs/research/m6_tasks/TASK_F08_RECOVERY_FAULTS_V1.json

CLAIM_IMPLEMENTED:
F08 implements a typed PRE/POST/rejected-locked observation relation over
canonical F04 fixed points. Exact PRE and POST bytes are exposed only as
root-labeled observations. Corruption, a valid third layout, and wrong-type
observations remain locked and expose no partial layout.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f08_recovery_faults.py tests/core/test_fcis_m6_f08_recovery_faults_properties.py`
- `PYTHONPATH=. python3 experiments/fcis_m6_f08_recovery_faults_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f08_recovery_faults.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py tests/core/test_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py tests/core/test_fcis_m6_f07_checkpoint.py tests/core/test_fcis_m6_f07_checkpoint_properties.py tests/core/test_fcis_m6_f08_recovery_faults.py tests/core/test_fcis_m6_f08_recovery_faults_properties.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py`
- `python3 -m ruff check ...` on all F08 source, checker, tool, and test files
- `python3 -m ruff format --check ...` on all F08 source, checker, tool, and test files
- `python3 -m mypy --strict ...` on all F08 source, checker, tool, and test files
- `python3 -m py_compile ...` on all F08 Python files
- `python3 -m json.tool ...` on the F08 configuration and vector
- `git diff --check`

RESULTS:
- focused and property tests: 4 passed in 34.17 seconds;
- independent checker: `F08_RECOVERY_FAULT_CHECKS_PASS 31`;
- public tool: `F08_RECOVERY_FAULT_VECTOR_MATCH 31`;
- combined adjacent F03-F08/G01/G02 regression: 38 passed in 41.82 seconds;
- 31 of 31 injected observed faults returned `REJECTED_LOCKED`;
- exact PRE and POST returned distinct roots and both required fresh
  authorization;
- valid third fixed point returned `REJECTED_LOCKED`;
- deterministic property campaign: 24 examples;
- Ruff, format, strict mypy, compilation, JSON, and diff checks passed;
- functional implementation commit and tree are recorded above.

MUTANTS_ADDED:
- missing, surplus, duplicate, reordered, and crossed authority rows;
- missing, surplus, duplicate, and crossed history rows;
- missing, surplus, duplicate, reordered, and crossed evidence rows;
- missing, surplus, duplicate, and crossed nullifier rows;
- missing, surplus, duplicate, and crossed outbox rows;
- missing, surplus, duplicate, and crossed acknowledgment rows;
- corrupted state header;
- selected-root-only mutation;
- truncated bytes;
- invalid UTF-8;
- valid third fixed point;
- untyped observed payload and PRE reference.

FORMAL_EVIDENCE:
No new Lean theorem is claimed for F08. The slice has deterministic reference,
property, and typed fault-matrix evidence only.

REMAINING_NONCLAIMS:
- F08 is research-only and unmounted;
- the model does not prove physical datastore atomicity or filesystem
  durability;
- no command, datastore, recovery worker, or value-moving path consumes this
  observation relation;
- R07/R09 and whole-system M6/R13 remain open.

REVIEW_RISKS:
- A production adapter must show that every crash point maps to exact PRE,
  exact POST, or reject/lock under its real transaction and durability model.
- A valid third fixed point is rejected by design, so the adapter must not
  manufacture a new authoritative layout outside the publication relation.
