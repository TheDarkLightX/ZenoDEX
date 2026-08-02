# FCIS M6 Task F02 report: canonical history encoder

TASK_ID: F02
BASE_SHA: e1579d68041af14436f6ce6ce0308d19591bbc56
SOURCE_HEAD_SHA: 421fa3ec3290721423c1be5ee330d74b0375715a
SOURCE_HEAD_TREE: 1265d6dc9c3a1521c37ae17440bec826d1b803a3
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f02_history_encoder_v1.json
- src/core/fcis_m6_f02_history_encoder.py
- experiments/fcis_m6_f02_history_encoder_check.py
- tests/core/test_fcis_m6_f02_history_encoder.py
- tools/build_fcis_m6_f02_history_encoder.py
- docs/research/m6_tasks/FCIS_M6_F02_HISTORY_ENCODER_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_F02_HISTORY_ENCODER_V1.json
- docs/research/m6_tasks/TASK_F02_PLAN.md
- docs/research/m6_tasks/TASK_F02_REPORT.md
- docs/research/m6_tasks/TASK_F02_EVIDENCE.json
- docs/research/m6_tasks/TASK_F02_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 421fa3ec3290721423c1be5ee330d74b0375715a
IMPLEMENTATION_TREE: 1265d6dc9c3a1521c37ae17440bec826d1b803a3
IMPLEMENTATION_PARENT: e1579d68041af14436f6ce6ce0308d19591bbc56

CLAIM_IMPLEMENTED: F02 defines one exact F02AuthorizedHistoryV1 source and
one public `encode_history` materializer. It derives a singleton state header,
authority rows, complete canonical F01 atom-byte history rows, eight ordered
evidence rows per atom, E02 nullifier rows, outbox rows, and acknowledgment
rows. Exact parallel counts, canonical order, authority/context lineage,
outbox ancestry, acknowledgment provenance, and a complete layout root are
checked before the layout is returned. A layout codec retains the full rows
and verifies the cached layout root.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f02_history_encoder_v1.json`
- `python3 tools/build_fcis_m6_f02_history_encoder.py`
- `python3 tools/build_fcis_m6_f02_history_encoder.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f02_history_encoder_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f02_history_encoder.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m py_compile src/core/fcis_m6_f01_history_atom.py src/core/fcis_m6_f02_history_encoder.py experiments/fcis_m6_f01_history_atom_check.py experiments/fcis_m6_f02_history_encoder_check.py tools/build_fcis_m6_f01_history_atom.py tools/build_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py`
- `python3 -m ruff check src/core/fcis_m6_f01_history_atom.py src/core/fcis_m6_f02_history_encoder.py experiments/fcis_m6_f01_history_atom_check.py experiments/fcis_m6_f02_history_encoder_check.py tools/build_fcis_m6_f01_history_atom.py tools/build_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py`
- `python3 -m ruff format --check src/core/fcis_m6_f01_history_atom.py src/core/fcis_m6_f02_history_encoder.py experiments/fcis_m6_f01_history_atom_check.py experiments/fcis_m6_f02_history_encoder_check.py tools/build_fcis_m6_f01_history_atom.py tools/build_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py`
- `python3 -m mypy --strict src/core/fcis_m6_f01_history_atom.py src/core/fcis_m6_f02_history_encoder.py experiments/fcis_m6_f01_history_atom_check.py experiments/fcis_m6_f02_history_encoder_check.py tools/build_fcis_m6_f01_history_atom.py tools/build_fcis_m6_f02_history_encoder.py tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f02_history_encoder.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F02`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F02_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused F02 suite passed: 5 passed.
- Combined F01/F02/E05/E06/E07/E08 suite passed: 30 passed.
- Independent checker passed:
  `F02_HISTORY_ENCODER_CHECKS_PASS 0x737e8137a2c83f3849ac68be9e059f7217bf552e20b145bc0eeba8142e2e2060`.
- Source-bound vector regeneration and check passed:
  `F02_HISTORY_ENCODER_VECTOR_MATCH`.
- Reference layout counts: 1 history row, 8 evidence rows, 1 nullifier row,
  1 outbox row, 4 authority rows, and 1 acknowledgment row.
- Mutation checks reject missing evidence, stale header counts, foreign layout
  roots, reordered evidence, crossed authority rows, crossed outbox rows, and
  untyped source histories.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: The checker and focused tests cover omitted parallel rows, stale
header counts, reordered evidence, foreign layout roots, authority-row
crossing, outbox-row crossing, crossed source context, crossed acknowledgment
provenance, and untyped input history.

FORMAL_EVIDENCE: None. F02 supplies a typed executable encoder, canonical
layout vector, exact projection checks, and mutation-killing tests. It adds no
machine-checked Lean theorem and no physical datastore refinement proof.

REMAINING_NONCLAIMS:
- F02 does not write a database or prove transaction atomicity, isolation,
  WAL/fsync durability, crash recovery, or concurrent linearization.
- F02 does not implement F03 partial reopen, canonical fixed-point recovery,
  process restart authorization, or physical corruption handling.
- F02 does not authenticate callers, verify proofs, deliver external effects,
  mount migration authority, cover no-bypass reachability, or establish
  accounting, backing, zUSD safety, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: F02 is a source-owned research encoder. F03 must parse these
complete row families, reconstruct the same F01 atoms, and require exact
whole-layout equality. The current implementation does not establish that a
production publisher uses `encode_history`.
