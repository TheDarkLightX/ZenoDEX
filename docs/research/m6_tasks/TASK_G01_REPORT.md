# FCIS M6 Task G01 report: proof-context values

TASK_ID: G01
BASE_SHA: a3e1b8a7d03ab6ca810b774f5f899053a5bd384b
SOURCE_HEAD_SHA: dff97e38392c5c8febf5c0c13acd8e29a9db17c2
SOURCE_HEAD_TREE: 1f1814098c64dc744a42b44e92348b3fd2e3213f
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_g01_proof_context_v1.json
- src/core/fcis_m6_g01_proof_context.py
- experiments/fcis_m6_g01_proof_context_check.py
- tests/core/test_fcis_m6_g01_proof_context.py
- tests/core/test_fcis_m6_g01_proof_context_properties.py
- tools/build_fcis_m6_g01_proof_context.py
- docs/research/m6_tasks/TASK_G01_PROOF_CONTEXT_V1.json
- docs/research/m6_tasks/FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_G01_PLAN.md
- docs/research/m6_tasks/TASK_G01_REPORT.md
- docs/research/m6_tasks/TASK_G01_EVIDENCE.json
- docs/research/m6_tasks/TASK_G01_SOURCE_MANIFEST.sha256

IMPLEMENTATION_HEAD_SHA: dff97e38392c5c8febf5c0c13acd8e29a9db17c2
IMPLEMENTATION_TREE: 1f1814098c64dc744a42b44e92348b3fd2e3213f
IMPLEMENTATION_PARENT: a3e1b8a7d03ab6ca810b774f5f899053a5bd384b

CLAIM_IMPLEMENTED: G01 defines one immutable typed proof-context value with
bounded exact fields, deterministic context-root rederivation, inclusive
not-before/expiry epoch rules, and a typed point-of-use revalidation relation.
Construction and revalidation create no proof authority or verifier selection.

COMMANDS_RUN:
- `python3 -m json.tool config/deploy/fcis_m6_g01_proof_context_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_G01_PROOF_CONTEXT_V1.json`
- `python3 tools/build_fcis_m6_g01_proof_context.py`
- `python3 tools/build_fcis_m6_g01_proof_context.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_g01_proof_context_check.py`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py`
- `python3 -m py_compile src/core/fcis_m6_g01_proof_context.py experiments/fcis_m6_g01_proof_context_check.py tools/build_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py`
- `python3 -m ruff check src/core/fcis_m6_g01_proof_context.py experiments/fcis_m6_g01_proof_context_check.py tools/build_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py`
- `python3 -m ruff format --check src/core/fcis_m6_g01_proof_context.py experiments/fcis_m6_g01_proof_context_check.py tools/build_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py`
- `python3 -m mypy --strict src/core/fcis_m6_g01_proof_context.py experiments/fcis_m6_g01_proof_context_check.py tools/build_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context.py tests/core/test_fcis_m6_g01_proof_context_properties.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks G01`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_G01_SOURCE_MANIFEST.sha256`

RESULTS:
- Focused and property suite passed: 6 passed.
- The property campaign ran with a deterministic 24-example cap and rejected
  generated state-root substitutions through context-root revalidation.
- Inclusive epoch boundaries 5 and 10 accepted; epochs 4 and 11 rejected.
- Wrong exact type, boolean epoch, forged root, hostile state mutation, and
  incomplete exact-object witnesses returned typed rejection.
- Independent checker passed:
  `G01_PROOF_CONTEXT_CHECKS_PASS 0xbea741b344275061cb32a4814db551900f4f0511dbbffc8e46c3bbf9e320a5cf`.
- Source-bound vector check passed: `G01_PROOF_CONTEXT_VECTOR_MATCH`.
- Python compilation, Ruff, Ruff formatting, strict mypy, JSON parsing, and
  diff checks passed.

MUTANTS_ADDED: state-root substitution, context-root forgery, incomplete exact
object, boolean epoch, before-not-before epoch, after-expiry epoch, and
generated state-root substitutions.

FORMAL_EVIDENCE: None. G01 supplies typed executable evidence and deterministic
property tests. It adds no machine-checked Lean theorem and no verifier proof.

REMAINING_NONCLAIMS:
- G01 does not provide canonical byte/Rust parity; that is G02.
- G01 does not pin or authorize a verifier registry entry; that is G03.
- G01 does not bind public inputs to ANF; that is G04.
- G01 does not authenticate callers, verify proofs, mount runtime paths, or
  enable value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: A caller can construct a structurally valid context value. This
is intentional for the value layer and becomes safe only when later verifier
and registry boundaries revalidate it and own proof authority.
