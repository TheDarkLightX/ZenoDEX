# FCIS M6 Task F06 report: fresh reopen-head authorization

TASK_ID: F06
BASE_SHA: d1c67df83bbe2d7ec3d08817d3442196dedc8de0
SOURCE_HEAD_SHA: 09c5275f8aa97283a76894f1030d4f6d7f724986
SOURCE_HEAD_TREE: ab68e554929229fdeb6f10577fb8970f9492d85d
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_f06_reopen_authorization_v1.json
- src/core/fcis_m6_f06_reopen_authorization.py
- experiments/fcis_m6_f06_reopen_authorization_check.py
- tests/core/test_fcis_m6_f06_reopen_authorization.py
- tests/core/test_fcis_m6_f06_reopen_authorization_properties.py
- tools/build_fcis_m6_f06_reopen_authorization.py
- docs/research/m6_tasks/TASK_F06_REOPEN_AUTHORIZATION_V1.json

IMPLEMENTATION_HEAD_SHA: 09c5275f8aa97283a76894f1030d4f6d7f724986
IMPLEMENTATION_TREE: ab68e554929229fdeb6f10577fb8970f9492d85d
IMPLEMENTATION_PARENT: d1c67df83bbe2d7ec3d08817d3442196dedc8de0

CLAIM_IMPLEMENTED: F06 derives an exact reopen head only after F03 canonical
reopen and F05 genesis binding. It requires matching external evidence and an
external verifier decision before token issue, then repeats the same checks at
each commit, acknowledgment-publication, and migration use. A changed head,
forged token, crossed evidence, rejecting verifier, or expired window returns
typed rejection.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_f06_reopen_authorization_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_F06_REOPEN_AUTHORIZATION_V1.json`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f06_reopen_authorization.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_f06_reopen_authorization.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_f06_reopen_authorization_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_f03_reopen.py tests/core/test_fcis_m6_f03_reopen_properties.py tests/core/test_fcis_m6_f05_authenticated_genesis.py tests/core/test_fcis_m6_f05_authenticated_genesis_properties.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py tests/core/test_fcis_m6_g02_proof_context_codec.py tests/core/test_fcis_m6_g02_proof_context_codec_properties.py`
- `python3 -m py_compile src/core/fcis_m6_f06_reopen_authorization.py experiments/fcis_m6_f06_reopen_authorization_check.py tools/build_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `python3 -m ruff check src/core/fcis_m6_f06_reopen_authorization.py experiments/fcis_m6_f06_reopen_authorization_check.py tools/build_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `python3 -m ruff format --check src/core/fcis_m6_f06_reopen_authorization.py experiments/fcis_m6_f06_reopen_authorization_check.py tools/build_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `python3 -m mypy --strict src/core/fcis_m6_f06_reopen_authorization.py experiments/fcis_m6_f06_reopen_authorization_check.py tools/build_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization.py tests/core/test_fcis_m6_f06_reopen_authorization_properties.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks F06`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_F06_SOURCE_MANIFEST.sha256`

RESULTS:
- F06 focused and property suite passed: 3 passed.
- Adjacent F03/F05/F06/G01/G02 regression passed: 26 passed in 4.47 seconds.
- The property campaign used a deterministic 24-example cap and rejected
  generated token-root substitutions at use.
- Independent checker passed:
  `F06_REOPEN_AUTHORIZATION_CHECKS_PASS 0x5e6b51ffcaa974b8d6a2b39a8ccc6df291238ce8bb6a5cb66d4d4ab9e9d55a6e`.
- Source-bound vector check passed: `F06_REOPEN_AUTHORIZATION_VECTOR_MATCH`.
- The vector records four fresh verifier calls, one at issue and one per
  operation kind.
- Head root: `0xe6f8b654de286da4fbd3e725ba8a43e3fa6832de77b87943469439866bb510d2`.
- Evidence root: `0x58270127cf643a076855dbd25c2f2065a0a2299f52d2c1d3a27ada9719ae33b3`.
- Token root: `0x5e6b51ffcaa974b8d6a2b39a8ccc6df291238ce8bb6a5cb66d4d4ab9e9d55a6e`.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: crossed evidence snapshot, forged token root, changed reopened
head, rejecting external verifier, expired token, and generated token-root
substitutions.

FORMAL_EVIDENCE: None. F06 supplies typed executable evidence and deterministic
property tests. It adds no machine-checked Lean theorem and no production
external-authentication proof.

REMAINING_NONCLAIMS:
- The verifier adapter is an external authority premise and is not implemented
  or cryptographically authenticated by F06.
- F06 does not prove datastore transactionality, crash recovery, destination
  idempotency, migration execution, no-bypass coverage, accounting, backing,
  or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: A caller can construct a structurally valid token in Python. The
point-of-use relation revalidates it and calls the external verifier again;
production still needs an opaque capability boundary and a mounted verifier.
