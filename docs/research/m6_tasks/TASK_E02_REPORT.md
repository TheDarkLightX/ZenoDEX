# FCIS M6 Task E02 Report

TASK_ID: E02
BASE_SHA: 7e202c58cfae8aa678f6d4ca044dde9b0461bcc2
SOURCE_HEAD_SHA: f21d55699fa833396d335183f61913418e9e1c02
SOURCE_HEAD_TREE: fb5b8105eb0fc8be24acc94e76a2816b6cb920fc
BRANCH: codex/task-m6-receipt-rebind-20260802
FILES_CHANGED:
- config/deploy/fcis_m6_e02_nonce_nullifier_v1.json
- docs/research/m6_tasks/FCIS_M6_E02_NONCE_NULLIFIER_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_E02_NONCE_NULLIFIER_V1.json
- docs/research/m6_tasks/TASK_E02_PLAN.md
- experiments/fcis_m6_e02_nonce_nullifier_check.py
- src/core/fcis_m6_e02_nonce_nullifier.py
- tests/core/test_fcis_m6_e02_nonce_nullifier.py
- tools/build_fcis_m6_e02_nonce_nullifier.py

CLAIM_IMPLEMENTED: E02 derives one canonical deployment/sender/nonce/family
nullifier from a verifier-derived E01 request identity only when the command
nonce is exactly the next sender nonce. The bounded increment rejects Boolean
aliases, non-next values, and u64 overflow. The exact preimage field set and
domain separator are canonicalized, and the derived nullifier retains the E01
request-identity root as provenance. The nullifier witness has a controlled
construction boundary and point-of-use mutation/provenance checks.

IMPLEMENTATION_HEAD_SHA: f21d55699fa833396d335183f61913418e9e1c02
IMPLEMENTATION_TREE: fb5b8105eb0fc8be24acc94e76a2816b6cb920fc
IMPLEMENTATION_PARENT: 7e202c58cfae8aa678f6d4ca044dde9b0461bcc2

COMMANDS_RUN:
- python3 tools/build_fcis_m6_e02_nonce_nullifier.py --check
- PYTHONPATH=. python3 experiments/fcis_m6_e02_nonce_nullifier_check.py
- PYTHONPATH=. pytest -q tests/core/test_fcis_m6_e01_request_identity.py tests/core/test_fcis_m6_e02_nonce_nullifier.py
- python3 -m py_compile src/core/fcis_m6_e02_nonce_nullifier.py tools/build_fcis_m6_e02_nonce_nullifier.py experiments/fcis_m6_e02_nonce_nullifier_check.py tests/core/test_fcis_m6_e02_nonce_nullifier.py
- python3 -m ruff check src/core/fcis_m6_e02_nonce_nullifier.py tools/build_fcis_m6_e02_nonce_nullifier.py experiments/fcis_m6_e02_nonce_nullifier_check.py tests/core/test_fcis_m6_e02_nonce_nullifier.py
- python3 -m ruff format --check src/core/fcis_m6_e02_nonce_nullifier.py tools/build_fcis_m6_e02_nonce_nullifier.py experiments/fcis_m6_e02_nonce_nullifier_check.py tests/core/test_fcis_m6_e02_nonce_nullifier.py
- python3 -m mypy --strict src/core/fcis_m6_e02_nonce_nullifier.py tools/build_fcis_m6_e02_nonce_nullifier.py experiments/fcis_m6_e02_nonce_nullifier_check.py tests/core/test_fcis_m6_e02_nonce_nullifier.py
- python3 -m json.tool config/deploy/fcis_m6_e02_nonce_nullifier_v1.json
- python3 -m json.tool docs/research/m6_tasks/TASK_E02_NONCE_NULLIFIER_V1.json
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks E02
- sha256sum --check --strict docs/research/m6_tasks/TASK_E02_SOURCE_MANIFEST.sha256
- git diff --check

RESULTS:
- E02 vector regenerated exactly with nullifier root
  `bb4d65007c0346d225879479a983d4094595091b7fce5e7bdbbf7f5b0ea44f58`.
- Focused E02 suite passed: 5 passed.
- E01 regression plus E02 suite passed: 10 passed.
- The independent checker passed: `E02_NONCE_NULLIFIER_MATCH`.
- Exact next-nonce relation passed at zero and maximum-u64 command boundaries;
  non-next and overflow candidates rejected.
- Deployment, sender, nonce, and command-family substitutions changed the
  canonical root; extra, missing, Boolean, and unknown-enum fields rejected.
- Caller-minted, exact-class forged, and mutated E02 witnesses were rejected.
- Strict Ruff, formatting, mypy, Python compilation, JSON parsing, vector
  freshness, packet validation, source-manifest verification, and whitespace
  checks passed.
- No Lean proof, datastore uniqueness constraint, concurrent transaction,
  runtime mount, authority switch, deployment, migration, or value movement is
  claimed.

MUTANTS_ADDED: E02 retains non-next nonce, u64 overflow, deployment
substitution, sender substitution, nonce substitution, command-family
substitution, extra field, missing field, Boolean nonce, unknown enum,
caller-minted nullifier, exact-class forged E01 identity, exact-class forged
E02 nullifier, and mutated registered nullifier witnesses.

FORMAL_EVIDENCE: None. E02 supplies a typed executable relation, a canonical
vector, deterministic root derivation, and mutation-killing tests. The E01
authentication witness remains an explicit research premise.

REMAINING_NONCLAIMS:
- E02 does not implement cryptographic authentication or prove that a
  production caller supplies a valid E01 witness.
- E02 does not consume or persist a production nonce, enforce database
  uniqueness, classify retries, or provide a concurrent transaction.
- E03 must enforce unique nullifier/commit/effect rows and hard collision
  behavior at the datastore boundary.
- E02 does not prove publication, recovery, outbox delivery, migration,
  accounting, backing, zUSD safety, runtime reachability, or value movement.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The nullifier root intentionally excludes command bytes and
post-state so a sender/nonce/family tuple has one replay namespace. A same
nullifier with a different command is therefore a datastore collision case,
which E03 must reject rather than treat as idempotent success. The in-memory
provenance registry is a bounded model mechanism and is not a production
authentication or persistence adapter.
