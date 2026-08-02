# FCIS M6 Task F04 report: whole-layout fixed-point gate

TASK_ID: F04
BASE_SHA: f4eed3b848350106a5eb0999a7ed9cb3cbd82ed5
SOURCE_HEAD_SHA: 998491ec15cefff789a99d60172bea7c5a0033a4
SOURCE_HEAD_TREE: d12ba0bb781573ae32eafa8cee8dbc3e5051c995
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f04_fixed_point_v1.json
- src/core/fcis_m6_f04_fixed_point.py
- experiments/fcis_m6_f04_fixed_point_check.py
- tests/core/test_fcis_m6_f04_fixed_point.py
- tools/build_fcis_m6_f04_fixed_point.py
- docs/research/m6_tasks/TASK_F04_FIXED_POINT_V1.json
- docs/research/m6_tasks/FCIS_M6_F04_FIXED_POINT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_F04_PLAN.md
- docs/research/m6_tasks/TASK_F04_REPORT.md
- docs/research/m6_tasks/TASK_F04_EVIDENCE.json
- docs/research/m6_tasks/TASK_F04_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 998491ec15cefff789a99d60172bea7c5a0033a4
IMPLEMENTATION_TREE: d12ba0bb781573ae32eafa8cee8dbc3e5051c995
IMPLEMENTATION_PARENT: f4eed3b848350106a5eb0999a7ed9cb3cbd82ed5

CLAIM_IMPLEMENTED: F04 exposes one typed gate that accepts only a complete
F03-reopened layout whose independently re-materialized F02 value and canonical
bytes equal the supplied layout. Selected-root equality is never used as a
substitute for complete equality.

STATUS: GAP. The current F02 schema permits an outbox with no durable
acknowledgment while delivery is pending. Removing the acknowledgment from the
review fixture therefore produces another valid canonical pending-delivery
layout after the layout root is recomputed. A single current layout cannot
classify that omission as corruption without prior-state or ack-obligation
evidence.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f04_fixed_point_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_F04_FIXED_POINT_V1.json`
- `python3 tools/build_fcis_m6_f04_fixed_point.py`
- `python3 tools/build_fcis_m6_f04_fixed_point.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f04_fixed_point_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f04_fixed_point.py`
- `python3 -m py_compile src/core/fcis_m6_f04_fixed_point.py experiments/fcis_m6_f04_fixed_point_check.py tools/build_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f04_fixed_point.py`
- `python3 -m ruff check src/core/fcis_m6_f04_fixed_point.py experiments/fcis_m6_f04_fixed_point_check.py tools/build_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f04_fixed_point.py`
- `python3 -m ruff format --check src/core/fcis_m6_f04_fixed_point.py experiments/fcis_m6_f04_fixed_point_check.py tools/build_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f04_fixed_point.py`
- `python3 -m mypy --strict src/core/fcis_m6_f04_fixed_point.py experiments/fcis_m6_f04_fixed_point_check.py tools/build_fcis_m6_f04_fixed_point.py tests/core/test_fcis_m6_f04_fixed_point.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F04`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F04_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused F04 suite passed: 3 passed.
- Mutation matrix generated 26 rehashed row-family cases.
- Twenty-five invalid cases returned typed rejection with F03 source
  provenance.
- `ack_rows:missing` was accepted as a valid pending-delivery fixed point under
  the current optional-ack schema; this is the preserved semantic-gap witness.
- Independent checker passed:
  `F04_FIXED_POINT_CHECKS_PASS 0x737e8137a2c83f3849ac68be9e059f7217bf552e20b145bc0eeba8142e2e2060`.
- Source-bound vector check passed: `F04_FIXED_POINT_VECTOR_MATCH`.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: Rehashed missing, extra, duplicate, and crossed cases for all
six row families; rehashed reordered cases for authority and evidence rows;
the acknowledged outbox deletion witness is retained as an accepted pending
delivery state rather than mislabeled as an invalid mutation.

FORMAL_EVIDENCE: None. F04 supplies a typed executable gate, deterministic
mutation evidence, and a minimized semantic counterexample. It adds no
machine-checked Lean theorem and no physical recovery proof.

REMAINING_NONCLAIMS:
- F04 does not prove that a current layout is descended from an authenticated
  prior layout or deployment-pinned genesis.
- F04 does not decide whether a particular acknowledgment is mandatory without
  an explicit R10 policy or prior-state witness.
- F04 does not read a filesystem or database and does not prove WAL, fsync,
  crash, rollback, or physical corruption behavior.
- F04 does not mint restart authorization or enable value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: Promoting F04 as a universal missing-row theorem would be
incorrect while optional pending acknowledgments remain in F02. The safe next
step is to bind ack obligation to R10 delivery state or retain the narrower
fixed-point claim.
