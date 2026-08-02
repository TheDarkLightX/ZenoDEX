# FCIS M6 Task F05 report: authenticated genesis

TASK_ID: F05
BASE_SHA: b3e29478d890fc255da4d7d0186a159bd7f7f7c8
SOURCE_HEAD_SHA: a282d0e2dcb0785eeab233a800933819cd23c2df
SOURCE_HEAD_TREE: 2cb3981ba7005fbdada718d570d4a4d828f74770
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f05_authenticated_genesis_v1.json
- src/core/fcis_m6_f05_authenticated_genesis.py
- experiments/fcis_m6_f05_authenticated_genesis_check.py
- tests/core/test_fcis_m6_f05_authenticated_genesis.py
- tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py
- tools/build_fcis_m6_f05_authenticated_genesis.py
- docs/research/m6_tasks/TASK_F05_AUTHENTICATED_GENESIS_V1.json

IMPLEMENTATION_HEAD_SHA: a282d0e2dcb0785eeab233a800933819cd23c2df
IMPLEMENTATION_TREE: 2cb3981ba7005fbdada718d570d4a4d828f74770
IMPLEMENTATION_PARENT: b3e29478d890fc255da4d7d0186a159bd7f7f7c8

CLAIM_IMPLEMENTED: F05 defines an immutable genesis value and a separate
deployment-pinned genesis relation. The relation binds chain, deployment,
initial state, configuration, authority profile, history schema, proof policy,
and migration policy, derives roots from the complete fields, and returns
typed rejection for crossed or forged values. It does not grant runtime
authority.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f05_authenticated_genesis_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_F05_AUTHENTICATED_GENESIS_V1.json`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f05_authenticated_genesis.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f05_authenticated_genesis.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f05_authenticated_genesis_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_*.py`
- `python3 -m py_compile src/core/fcis_m6_f05_authenticated_genesis.py experiments/fcis_m6_f05_authenticated_genesis_check.py tools/build_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py`
- `python3 -m ruff check src/core/fcis_m6_f05_authenticated_genesis.py experiments/fcis_m6_f05_authenticated_genesis_check.py tools/build_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py`
- `python3 -m ruff format --check src/core/fcis_m6_f05_authenticated_genesis.py experiments/fcis_m6_f05_authenticated_genesis_check.py tools/build_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py`
- `python3 -m mypy --strict src/core/fcis_m6_f05_authenticated_genesis.py experiments/fcis_m6_f05_authenticated_genesis_check.py tools/build_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F05`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F05_SOURCE_MANIFEST.sha256`

RESULTS:
- F05 focused and property suite passed: 4 passed.
- Broad M6 core regression passed: 316 passed in 289.79 seconds.
- The property campaign used a deterministic 24-example cap and rejected
  generated foreign initial-state roots.
- Independent checker passed:
  `F05_AUTHENTICATED_GENESIS_CHECKS_PASS 0x2429a95eb0e2d9cbd8d18224107b0a2a4416e86bd797579948bf9f7473404bea`.
- Source-bound vector check passed: `F05_AUTHENTICATED_GENESIS_VECTOR_MATCH`.
- Vector roots were genesis `0x490f37c731987e864c923dd30fc275b2fd8cde02cd70b07931aedc4ce5a870bb`,
  pin `0x0bf47a21d45a19245cb47be7bc0ca35f1f26eba557516f4113606084de12db0b`,
  and admission `0x2429a95eb0e2d9cbd8d18224107b0a2a4416e86bd797579948bf9f7473404bea`.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: foreign initial state root, genesis root crossed with the
deployment pin, foreign chain pin, foreign authority profile pin, forged
genesis root, and generated initial-state-root substitutions.

FORMAL_EVIDENCE: None. F05 supplies typed executable evidence and deterministic
property tests. It adds no machine-checked Lean theorem, signature proof, or
configuration-authentication proof.

REMAINING_NONCLAIMS:
- F05 does not authenticate the source of the deployment pin; production must
  load it through an authenticated deployment/configuration boundary.
- F05 does not issue F06's fresh reopen-head authorization token.
- F05 does not prove canonical durable layouts, crash recovery, migration,
  destination effects, accounting, backing, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The acceptance result is a checked relation with public Python
construction paths. It must remain a value checked at use until a production
configuration authority and opaque runtime authorization boundary are mounted.
