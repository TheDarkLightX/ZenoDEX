# FCIS M6 Task E01 Report

TASK_ID: E01
BASE_SHA: 5e7c0824e06bfbafb8af6ba28e10dfa5cf1c48fb
SOURCE_HEAD_SHA: d620535366cbfad4047786eb1a4284e7ee006093
SOURCE_HEAD_TREE: e2cb860faf14685c99f52b08959dd0207229d5fe
BRANCH: codex/task-H03-deterministic-crash-20260801
FILES_CHANGED:
- config/deploy/fcis_m6_e01_request_identity_v1.json
- docs/research/m6_tasks/FCIS_M6_E01_REQUEST_IDENTITY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E01_PLAN.md
- docs/research/m6_tasks/TASK_E01_REQUEST_IDENTITY_SCHEMA_V1.json
- docs/research/m6_tasks/TASK_E01_REQUEST_IDENTITY_V1.json
- experiments/fcis_m6_e01_request_identity_check.py
- src/core/fcis_m6_e01_request_identity.py
- tests/core/test_fcis_m6_e01_request_identity.py
- tools/build_fcis_m6_e01_request_identity.py

IMPLEMENTATION_HEAD_SHA: d620535366cbfad4047786eb1a4284e7ee006093
IMPLEMENTATION_TREE: e2cb860faf14685c99f52b08959dd0207229d5fe
IMPLEMENTATION_PARENT: 5e7c0824e06bfbafb8af6ba28e10dfa5cf1c48fb

CLAIM_IMPLEMENTED: E01 derives a canonical request identity only from a
verifier-owned authenticated-command witness and explicit deployment,
sequence, and authority context. The public command and identity constructors
reject ordinary caller construction. The strict codec rejects extra or
missing fields, malformed digests, unsupported command families, booleans in
integer positions, and width violations. The stable identity binds the
authentication profile root while retaining evidence-root provenance on the
command witness.

COMMANDS_RUN:
- `python3 tools/build_fcis_m6_e01_request_identity.py --check`
- `python3 experiments/fcis_m6_e01_request_identity_check.py`
- `PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_e01_request_identity.py`
- `python3 -m py_compile src/core/fcis_m6_e01_request_identity.py tools/build_fcis_m6_e01_request_identity.py experiments/fcis_m6_e01_request_identity_check.py tests/core/test_fcis_m6_e01_request_identity.py`
- `python3 -m ruff check src/core/fcis_m6_e01_request_identity.py tools/build_fcis_m6_e01_request_identity.py experiments/fcis_m6_e01_request_identity_check.py tests/core/test_fcis_m6_e01_request_identity.py`
- `python3 -m ruff format --check src/core/fcis_m6_e01_request_identity.py tools/build_fcis_m6_e01_request_identity.py experiments/fcis_m6_e01_request_identity_check.py tests/core/test_fcis_m6_e01_request_identity.py`
- `python3 -m mypy --strict src/core/fcis_m6_e01_request_identity.py tools/build_fcis_m6_e01_request_identity.py experiments/fcis_m6_e01_request_identity_check.py tests/core/test_fcis_m6_e01_request_identity.py`
- `python3 -m json.tool config/deploy/fcis_m6_e01_request_identity_v1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E01_REQUEST_IDENTITY_SCHEMA_V1.json`
- `python3 -m json.tool docs/research/m6_tasks/TASK_E01_REQUEST_IDENTITY_V1.json`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E01`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_E01_SOURCE_MANIFEST.sha256`
- `git diff --check`

RESULTS:
- E01 vector regenerated exactly with request identity root
  `77e6b68d217fe7553c87cc6e82d60f67aaa7292e4c09d8df277c2a6add0819c4`.
- Same authenticated command and context produce the same retry identity;
  command-root and sequence mutations produce distinct roots.
- Extra, missing, malformed, and boolean fields reject at the strict root
  codec.
- Public authenticated-command and identity constructors reject caller-minted
  values.
- Focused E01 suite passed: 4 passed.
- Ruff, formatting, strict mypy, Python compilation, JSON parsing, packet
  validation, source manifest verification, and diff whitespace checks pass.

MUTANTS_ADDED: Caller-minted authenticated command, caller-minted request
identity, extra field, missing field, malformed digest, boolean nonce, command
family mutation, command-root mutation, and sequence mutation are retained as
negative witnesses.

FORMAL_EVIDENCE: None. E01 supplies executable typed-model evidence and adds
no machine-checked cryptographic authentication theorem.

REMAINING_NONCLAIMS:
- The private fixture mint helper represents an external verifier premise; E01
  does not implement signatures, credentials, or cryptographic authentication.
- E01 does not authorize a commit, consume a nonce, provide a concurrent
  transaction, mount an API, or mutate a datastore.
- E01 does not prove retry classification, publication, recovery, outbox
  delivery, migration, accounting, backing, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The opaque witness boundary is modeled in Python and requires a
production verifier adapter with controlled construction, canonical command
decoding, authentication evidence verification, and exact sequence/epoch
binding before it can support any mounted transition.
