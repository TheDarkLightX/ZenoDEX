# FCIS M6 Task F03 report: total fail-closed reopen

TASK_ID: F03
BASE_SHA: ee7408d24736ce2f02bb035715449d686ffd8dd2
SOURCE_HEAD_SHA: 629381148ca25b86af7f464288e10df95d6f29ea
SOURCE_HEAD_TREE: af2c0d5d15058e16f117910f8a6de6b3e6f8fb33
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f03_reopen_v1.json
- src/core/fcis_m6_f03_reopen.py
- experiments/fcis_m6_f03_reopen_check.py
- tests/core/test_fcis_m6_f03_reopen.py
- tests/core/test_fcis_m6_f03_reopen_properties.py
- tools/build_fcis_m6_f03_reopen.py
- docs/research/m6_tasks/FCIS_M6_F03_REOPEN_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_F03_REOPEN_V1.json
- docs/research/m6_tasks/TASK_F03_PLAN.md
- docs/research/m6_tasks/TASK_F03_REPORT.md
- docs/research/m6_tasks/TASK_F03_EVIDENCE.json
- docs/research/m6_tasks/TASK_F03_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 629381148ca25b86af7f464288e10df95d6f29ea
IMPLEMENTATION_TREE: af2c0d5d15058e16f117910f8a6de6b3e6f8fb33
IMPLEMENTATION_PARENT: b0218404a320714b9d43448d42d92589d83f94c0

CLAIM_IMPLEMENTED: F03 defines a partial reopen relation for F02 canonical
layout bytes and exact layout values. It checks exact types, resource bounds,
UTF-8, duplicate keys, canonical bytes, closed row fields, nested F01 values,
state/context/authority lineage, all parallel projections, canonical
re-encoding, and exact whole-layout fixed-point equality. Success returns one
complete F02AuthorizedHistoryV1; every failure returns F03ReopenRejectV1.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f03_reopen_v1.json >/dev/null && python3 -m json.tool docs/research/m6_tasks/TASK_F03_EVIDENCE.json >/dev/null`
- `python3 tools/build_fcis_m6_f03_reopen.py`
- `python3 tools/build_fcis_m6_f03_reopen.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f03_reopen_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m py_compile src/core/fcis_m6_f01_history_atom.py src/core/fcis_m6_f02_history_encoder.py src/core/fcis_m6_f03_reopen.py experiments/fcis_m6_f01_history_atom_check.py experiments/fcis_m6_f02_history_encoder_check.py experiments/fcis_m6_f03_reopen_check.py tools/build_fcis_m6_f01_history_atom.py tools/build_fcis_m6_f02_history_encoder.py tools/build_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py`
- `python3 -m ruff check src/core/fcis_m6_f03_reopen.py experiments/fcis_m6_f03_reopen_check.py tools/build_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py`
- `python3 -m ruff format --check src/core/fcis_m6_f03_reopen.py experiments/fcis_m6_f03_reopen_check.py tools/build_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py`
- `python3 -m mypy --strict src/core/fcis_m6_f03_reopen.py experiments/fcis_m6_f03_reopen_check.py tools/build_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F03`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F03_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused F03 suite passed: 7 passed, including two deterministic Hypothesis
  property tests with 24 and 32 example caps.
- Combined F01/F02/F03/E05/E06/E07/E08 suite passed: 37 passed.
- Independent checker passed:
  `F03_REOPEN_CHECKS_PASS 0x737e8137a2c83f3849ac68be9e059f7217bf552e20b145bc0eeba8142e2e2060`.
- Source-bound vector regeneration and check passed:
  `F03_REOPEN_VECTOR_MATCH`.
- Valid layout bytes reopened to one complete history with byte-identical
  canonical re-encoding.
- Rejection witnesses covered missing and surplus evidence, reordered rows,
  selected-root-only mutation, crossed atom bytes, noncanonical bytes,
  invalid UTF-8, invalid JSON, wrong type, and an incomplete layout object.
- Property tests generated deletion, duplication, and reordering mutations for
  two parallel row collections and generated foreign selected roots. Every
  generated mutation was rejected with a typed result.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: F03 covers missing evidence, surplus evidence, reordered
evidence, foreign selected root, crossed atom projection, noncanonical bytes,
invalid UTF-8, invalid JSON, wrong exact layout type, and incomplete layout
object. The fixed-point gate rejects a layout whose re-encoded projections do
not equal the accepted input.

FORMAL_EVIDENCE: None. F03 supplies a typed partial decoder, deterministic
fixed-point checker, canonical vector, and mutation-killing tests. It adds no
machine-checked Lean theorem and no physical recovery proof.

REMAINING_NONCLAIMS:
- F03 does not read a filesystem or database and does not prove WAL, fsync,
  crash, rollback, or physical corruption behavior.
- F03 does not mint fresh post-restart authorization or enable value movement.
- F03 does not implement destination delivery, migration mounting, no-bypass
  reachability, accounting, backing, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: F03 assumes the F02 layout byte envelope and F01 atom codec are
the governed schemas. A production adapter still must refine physical rows to
this relation and prove crash observations are exact PRE, POST, or reject/lock.
