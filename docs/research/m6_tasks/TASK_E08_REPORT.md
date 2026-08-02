# FCIS M6 Task E08 report: public finite-state model

TASK_ID: E08
BASE_SHA: ad0e45eb0ac2512479f1c45b428c89ca8933552f
SOURCE_HEAD_SHA: e0f029932a6f52d5f1dec9983855ff33f3923ee2
SOURCE_HEAD_TREE: 1cc358d94ff0e7eaa7778d5a84e809ffcd80cb32
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_e08_finite_state_v1.json
- experiments/fcis_m6_e08_finite_state.py
- experiments/fcis_m6_e08_finite_state_check.py
- tests/core/test_fcis_m6_e08_finite_state.py
- tools/build_fcis_m6_e08_finite_state.py
- docs/research/m6_tasks/FCIS_M6_E08_FINITE_STATE_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E08_FINITE_STATE_V1.json
- docs/research/m6_tasks/TASK_E08_PLAN.md
- docs/research/m6_tasks/TASK_E08_REPORT.md
- docs/research/m6_tasks/TASK_E08_EVIDENCE.json
- docs/research/m6_tasks/TASK_E08_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: e0f029932a6f52d5f1dec9983855ff33f3923ee2
IMPLEMENTATION_TREE: 1cc358d94ff0e7eaa7778d5a84e809ffcd80cb32
IMPLEMENTATION_PARENT: ad0e45eb0ac2512479f1c45b428c89ca8933552f

CLAIM_IMPLEMENTED: E08 adds a public bounded finite-state model for commit,
retry, quiescence, and authority-switch words. Breadth-first exploration
through depth 6 reaches 9 safe states across 54 transitions, checks 324 named
invariant instances, finds no invariant failure, and kills five minimized
semantic mutants. Exact retries and rejected actions are explicit stutters;
successful publication is atomic over the head, commit ID, and nullifier.

COMMANDS_RUN:
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e08_finite_state.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 tools/build_fcis_m6_e08_finite_state.py`
- `python3 tools/build_fcis_m6_e08_finite_state.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_e08_finite_state_check.py`
- `python3 -m py_compile experiments/fcis_m6_e08_finite_state.py experiments/fcis_m6_e08_finite_state_check.py tools/build_fcis_m6_e08_finite_state.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m ruff check experiments/fcis_m6_e08_finite_state.py experiments/fcis_m6_e08_finite_state_check.py tools/build_fcis_m6_e08_finite_state.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m ruff format --check experiments/fcis_m6_e08_finite_state.py experiments/fcis_m6_e08_finite_state_check.py tools/build_fcis_m6_e08_finite_state.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m mypy --strict experiments/fcis_m6_e08_finite_state.py experiments/fcis_m6_e08_finite_state_check.py tools/build_fcis_m6_e08_finite_state.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m json.tool config/deploy/fcis_m6_e08_finite_state_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E08_FINITE_STATE_V1.json`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E08`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E08_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused E08 suite passed: 4 passed.
- Combined E05/E06/E07/E08 suite passed: 20 passed.
- Independent checker passed: `E08_FINITE_STATE_CHECKS_PASS 9 54`.
- Source-bound vector regeneration and check passed:
  `E08_FINITE_STATE_VECTOR_MATCH`.
- Bounded depth: 6.
- Reachable safe states: 9.
- Explored transitions: 54.
- Accepted transitions: 10.
- Rejected stutters: 44.
- Named invariant checks: 324.
- Invariant failures: 0.
- Killed mutants: authority-switch skip, commit after quiescence, duplicate
  nullifier, retry head increment, split publication.
- Two complete explorations produced byte-identical summaries.
- Ruff, Ruff formatting, strict mypy, Python compilation, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: The model kills duplicate nullifier, post-quiescence commit,
authority-switch skip, retry-head-increment, and split-publication witnesses.
Each is rejected by a closed constructor, lifecycle transition guard, or
head/cardinality invariant.

FORMAL_EVIDENCE: None. E08 supplies a public executable finite-state model and
repeatable exhaustive bounded exploration. It is not a machine-checked Lean
or TLA/TLC theorem.

REMAINING_NONCLAIMS:
- E08 is bounded to the declared six-action, depth-six model and does not
  prove unbounded behavior.
- E08 does not prove the E05 SQLite adapter, production database isolation,
  real migration authority, TLA/TLC execution, runtime no-bypass coverage,
  accounting, backing, zUSD safety, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The model has a deliberately tiny one-head state space and one
shared nullifier domain. It is a public semantic witness for the stated
bounded claims, while production phase transitions, multiple heads, real
authority records, and datastore refinement remain open.
