TASK_ID: F07
BASE_SHA: defc3bf9c3475e1e7eb5efc000d9f98aa4a284c6
SOURCE_HEAD_SHA: af2a11aa8b815519524f505f8f75b31b6b101e5e
SOURCE_HEAD_TREE: 82123cc13c29d6f0a08b0278774f3c64ed96053b
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f07_checkpoint_v1.json
- src/core/fcis_m6_f07_checkpoint.py
- experiments/fcis_m6_f07_checkpoint_check.py
- tests/core/test_fcis_m6_f07_checkpoint.py
- tests/core/test_fcis_m6_f07_checkpoint_properties.py
- tools/build_fcis_m6_f07_checkpoint.py
- docs/research/m6_tasks/TASK_F07_CHECKPOINT_TRUNCATION_V1.json

CLAIM_IMPLEMENTED:
F07 implements a source-bound, full-tip checkpoint certificate and compacted
snapshot relation. The certificate commits to complete prior history,
state, nullifier, authority, outbox, genesis-admission, replay-proof, and
pending-outbox data. The use relation recomputes the expected certificate from
the F04 fixed point and F05 accepted genesis relation.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f07_checkpoint.py tests/core/test_fcis_m6_f07_checkpoint_properties.py`
- `PYTHONPATH=. python3 experiments/fcis_m6_f07_checkpoint_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f07_checkpoint.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py tests/core/test_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py tests/core/test_fcis_m6_f07_checkpoint.py tests/core/test_fcis_m6_f07_checkpoint_properties.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py`
- `python3 -m ruff check ...` on all F07 source, checker, tool, and test files
- `python3 -m ruff format --check ...` on all F07 source, checker, tool, and test files
- `python3 -m mypy --strict ...` on all F07 source, checker, tool, and test files
- `python3 -m py_compile ...` on all F07 Python files
- `python3 -m json.tool ...` on the F07 configuration and vector
- `git diff --check`

RESULTS:
- focused and property tests: 5 passed;
- independent checker: `F07_CHECKPOINT_CHECKS_PASS 0x69ff47f0e52297397fd5c0093c7545fc1e2ecf03f7077c4efe2de066a68abc43`;
- public tool: vector match;
- adjacent F03-F07/G01/G02 regression: 34 passed in 8.37 seconds;
- deterministic property campaign: 24 examples;
- pending source retained one complete unacknowledged effect identity;
- 10 root substitutions, pending omission, unsupported proof mode, partial
  sequence, and wrong-type witnesses rejected;
- Ruff, format, strict mypy, compilation, JSON, and diff checks passed;
- functional implementation commit and tree are recorded above.

MUTANTS_ADDED:
- prior layout root substitution;
- prior history root substitution;
- checkpoint state root substitution;
- deployment root substitution;
- verifier root substitution;
- F05 admission root substitution;
- nullifier accumulator root substitution;
- authority summary root substitution;
- outbox accumulator root substitution;
- replay proof root substitution;
- omitted pending outbox identity;
- approved snapshot proof without external certificate;
- zero/partial checkpoint sequence;
- untyped source or genesis relation.

FORMAL_EVIDENCE:
No new Lean theorem is claimed for F07. The slice has deterministic replay,
property, and typed rejection evidence only.

REMAINING_NONCLAIMS:
- F07 is research-only and unmounted;
- no physical datastore row is deleted;
- full-tip-only is a deliberate v1 boundary;
- approved-snapshot proof remains unavailable without an external verifier;
- crash recovery, concurrency, migration, effects, accounting, backing, zUSD,
  and M6 promotion remain open.

REVIEW_RISKS:
- The replay proof root is a deterministic source commitment, not an external
  cryptographic replay proof.
- The pending-outbox summary is a value-level transport obligation; a real
  worker and destination must still enforce idempotency.
- A production refinement must prove that compaction and its checkpoint are one
  durable atomic transition.
