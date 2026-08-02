# FCIS M6 Task F01 report: authoritative history atom schema

TASK_ID: F01
BASE_SHA: 58c0a5b206aafc4dfa327524032bcca2f8e1c773
SOURCE_HEAD_SHA: 0fcea1c43f69ef1eb29cd85248b9c4435c2d9516
SOURCE_HEAD_TREE: 4594804cdba78032d64cb4ae1800be069870fa92
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f01_history_atom_v1.json
- src/core/fcis_m6_f01_history_atom.py
- experiments/fcis_m6_f01_history_atom_check.py
- tests/core/test_fcis_m6_f01_history_atom.py
- tools/build_fcis_m6_f01_history_atom.py
- docs/research/m6_tasks/FCIS_M6_F01_HISTORY_ATOM_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_F01_HISTORY_ATOM_V1.json
- docs/research/m6_tasks/TASK_F01_PLAN.md
- docs/research/m6_tasks/TASK_F01_REPORT.md
- docs/research/m6_tasks/TASK_F01_EVIDENCE.json
- docs/research/m6_tasks/TASK_F01_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: 0fcea1c43f69ef1eb29cd85248b9c4435c2d9516
IMPLEMENTATION_TREE: 4594804cdba78032d64cb4ae1800be069870fa92
IMPLEMENTATION_PARENT: 58c0a5b206aafc4dfa327524032bcca2f8e1c773

CLAIM_IMPLEMENTED: F01 defines one immutable bounded history atom carrying
sequence, commit, command, pre/post state, deployment, verifier, writer,
authority, ANF, proof-context, E02 nullifier, response, receipt, decision,
bundle, replay, and ordered outbox facts. The canonical JSON codec derives one
atom root from the complete value. The partial decoder returns a complete atom
or a typed rejection. E02 nullifier, effect identity, and idempotency roots are
rederived at the atom boundary.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f01_history_atom_v1.json`
- `python3 tools/build_fcis_m6_f01_history_atom.py`
- `python3 tools/build_fcis_m6_f01_history_atom.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f01_history_atom_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f01_history_atom.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_e05_expected_root_cas.py tests/core/test_fcis_m6_e06_concurrency.py tests/core/test_fcis_m6_e07_transport_loss.py tests/core/test_fcis_m6_e08_finite_state.py`
- `python3 -m py_compile src/core/fcis_m6_f01_history_atom.py experiments/fcis_m6_f01_history_atom_check.py tools/build_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f01_history_atom.py`
- `python3 -m ruff check src/core/fcis_m6_f01_history_atom.py experiments/fcis_m6_f01_history_atom_check.py tools/build_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f01_history_atom.py`
- `python3 -m ruff format --check src/core/fcis_m6_f01_history_atom.py experiments/fcis_m6_f01_history_atom_check.py tools/build_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f01_history_atom.py`
- `python3 -m mypy --strict src/core/fcis_m6_f01_history_atom.py experiments/fcis_m6_f01_history_atom_check.py tools/build_fcis_m6_f01_history_atom.py tests/core/test_fcis_m6_f01_history_atom.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F01`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F01_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused F01 suite passed: 5 passed.
- Combined F01/E05/E06/E07/E08 suite passed: 25 passed.
- Independent checker passed: `F01_HISTORY_ATOM_CHECKS_PASS 0xb0ce80f709a727b6d66661470cd997dbc65c78d4b39cd525560925124e63cdd8`.
- Source-bound vector regeneration and check passed:
  `F01_HISTORY_ATOM_VECTOR_MATCH`.
- The complete atom contains 20 required top-level value fields and one
  ordered outbox record in the reference vector.
- Mutation checks reject omitted ANF, unknown fields, noncanonical bytes,
  crossed E02 nullifier, crossed effect identity, and invalid proof-context
  sentinel values.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: The checker and focused tests cover missing ANF root, unknown
atom field, noncanonical bytes, crossed nullifier projection, crossed outbox
effect identity, stale idempotency relation, invalid proof-context sentinel,
wrong exact atom type, and wrong outbox collection type.

FORMAL_EVIDENCE: None. F01 supplies a typed executable schema, canonical
codec, source-bound vector, and mutation-killing tests. It adds no machine-
checked Lean theorem and no datastore refinement proof.

REMAINING_NONCLAIMS:
- F01 does not authenticate the command or mint verifier authority.
- F01 retains an E02 projection and rederives its root; it does not prove the
  external authentication evidence behind the request identity.
- F01 does not implement F02 canonical history materialization, F03 partial
  reopen, fixed-point recovery, database transactions, crash durability,
  destination delivery, migration mounting, no-bypass coverage, accounting,
  backing, zUSD safety, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The atom schema is a research refinement boundary. F02 must make
this atom the sole source for every materialized authoritative row, and F03
must decode only complete atoms while requiring exact whole-layout equality.
The current module does not establish that any production caller uses it.
