TASK_ID: F04A
BASE_SHA: 9c58a90841f3e5f5dd85cef6cbabfda84bec0907
SOURCE_HEAD_SHA: 3a9606141c3762f8b2e57150b7b1a77531102bf1
SOURCE_HEAD_TREE: 46d56b1545d1632e82f3c62282648d9396cf0953
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f04_ack_progress_v1.json
- src/core/fcis_m6_f04_ack_progress.py
- experiments/fcis_m6_f04_ack_progress_check.py
- tests/core/test_fcis_m6_f04_ack_progress.py
- tests/core/test_fcis_m6_f04_ack_progress_properties.py
- tools/build_fcis_m6_f04_ack_progress.py
- docs/research/m6_tasks/TASK_F04A_ACK_PROGRESS_V1.json
- docs/research/m6_tasks/validate_companion_task_packet.py

CLAIM_IMPLEMENTED:
F04A implements source-bound monotone acknowledgment progress. It rejects
deletion or mutation of an acknowledgment present in the canonical prior
layout, rejects non-ack history changes, and exposes pending effect identities
when the current state remains unacknowledged.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f04_ack_progress.py tests/core/test_fcis_m6_f04_ack_progress_properties.py`
- `PYTHONPATH=. python3 experiments/fcis_m6_f04_ack_progress_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f04_ack_progress.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f04_ack_progress.py tests/core/test_fcis_m6_f04_ack_progress_properties.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f07_checkpoint.py tests/core/test_fcis_m6_f08_recovery_faults.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g02_proof_context_codec.py`
- `python3 -m ruff check ...` on all F04A source, checker, tool, and test files
- `python3 -m ruff format --check ...` on all F04A source, checker, tool, and test files
- `python3 -m mypy --strict ...` on all F04A source, checker, tool, and test files
- `python3 -m py_compile ...` on all F04A Python files
- `python3 -m json.tool ...` on the F04A configuration and vector
- `git diff --check`

RESULTS:
- focused and property tests: 4 passed in 1.89 seconds;
- independent checker: `F04A_ACK_PROGRESS_CHECKS_PASS acked`;
- public tool: `F04A_ACK_PROGRESS_VECTOR_MATCH acked`;
- adjacent regression: 33 passed in 13.58 seconds;
- pending-to-pending progress retained one pending effect;
- pending-to-acked progress recorded one added acknowledgment;
- prior ack deletion, prior ack mutation, history change, and wrong type
  returned typed rejection;
- Ruff, format, strict mypy, compilation, JSON, and diff checks passed.

MUTANTS_ADDED:
- deleted prior acknowledgment;
- mutated existing destination receipt root;
- changed non-ack history;
- untyped prior payload;
- generated deletion/mutation property witnesses.

FORMAL_EVIDENCE:
No new Lean theorem is claimed. F04A supplies deterministic relation,
property, and typed negative evidence.

REMAINING_NONCLAIMS:
- current-only missing acknowledgment remains a deliberate F04 GAP;
- R10 must define destination acknowledgment obligations and authenticity;
- F04A does not implement a datastore transaction or delivery worker;
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS:
- The prior layout is a checked value, not an external authenticated database
  snapshot in this slice.
- A production refinement must bind the prior root to the same transaction or
  an independently authenticated checkpoint.
