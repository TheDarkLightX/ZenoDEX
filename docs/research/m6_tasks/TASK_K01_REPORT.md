# FCIS M6 Task K01 Report

TASK_ID: K01
BASE_SHA: 868ae8ef0da8a4f7fc52f444d7b459987f76c51e
SOURCE_HEAD_SHA: 8cd4e451138e86a3fa1012b1081112644114fa97
SOURCE_HEAD_TREE: e58d21d10835bfe5dddb314d1cc11bf7bd773dd8
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:

- config/deploy/fcis_m6_k01_entrypoint_inventory_v1.json
- src/core/fcis_m6_k01_entrypoint_inventory.py
- tools/build_fcis_m6_k01_entrypoint_inventory.py
- experiments/fcis_m6_k01_entrypoint_inventory_check.py
- tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- docs/research/m6_tasks/TASK_K01_VALUE_MOVING_ENTRYPOINT_INVENTORY_V1.json
- docs/research/m6_tasks/FCIS_M6_K01_VALUE_MOVING_ENTRYPOINT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K01_PLAN.md

IMPLEMENTATION_HEAD_SHA: 8cd4e451138e86a3fa1012b1081112644114fa97
IMPLEMENTATION_TREE: e58d21d10835bfe5dddb314d1cc11bf7bd773dd8
IMPLEMENTATION_PARENT: 868ae8ef0da8a4f7fc52f444d7b459987f76c51e

DEPENDENCY_REBIND: The later H02 source edit changed a file included in the
K01 source set. K01 was regenerated at the exact repair head before J06 was
rebuilt, and the current K01 root is pinned by J06.

CLAIM_IMPLEMENTED: K01 adds a typed, source-bound inventory for fifteen
reviewed command, authority, datastore, migration, recovery, legacy,
proof-input, and external-effect candidate surfaces. The inventory requires
the nine D05 publisher IDs, records caller/input/state-effect/ANF-commit-port
fields, classifies legacy and proof-only paths, hashes its exact source set,
and derives the canonical entrypoint inventory root
fc150266a7932c32d67ac5674251ae96db7f65a633a0e0b8eba791431682e31a.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k01_entrypoint_inventory.py tools/build_fcis_m6_k01_entrypoint_inventory.py experiments/fcis_m6_k01_entrypoint_inventory_check.py tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- python3 -m ruff check src/core/fcis_m6_k01_entrypoint_inventory.py tools/build_fcis_m6_k01_entrypoint_inventory.py experiments/fcis_m6_k01_entrypoint_inventory_check.py tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- python3 -m ruff format --check src/core/fcis_m6_k01_entrypoint_inventory.py tools/build_fcis_m6_k01_entrypoint_inventory.py experiments/fcis_m6_k01_entrypoint_inventory_check.py tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- python3 -m mypy --strict src/core/fcis_m6_k01_entrypoint_inventory.py tools/build_fcis_m6_k01_entrypoint_inventory.py experiments/fcis_m6_k01_entrypoint_inventory_check.py tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- PYTHONPATH=. python3 -m pytest -q tests/core/test_fcis_m6_k01_entrypoint_inventory.py
- python3 tools/build_fcis_m6_k01_entrypoint_inventory.py --check
- python3 experiments/fcis_m6_k01_entrypoint_inventory_check.py
- python3 -m json.tool config/deploy/fcis_m6_k01_entrypoint_inventory_v1.json
- python3 -m json.tool docs/research/m6_tasks/TASK_K01_VALUE_MOVING_ENTRYPOINT_INVENTORY_V1.json
- python3 tools/build_fcis_m6_k01_entrypoint_inventory.py (dependency rebind)
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K01
- sha256sum --check --strict docs/research/m6_tasks/TASK_K01_SOURCE_MANIFEST.sha256

RESULTS:

- K01 vector regeneration passed with the exact root
  fc150266a7932c32d67ac5674251ae96db7f65a633a0e0b8eba791431682e31a.
- The source-bound vector was regenerated after the later H02 source edit;
  the changed H02 bytes are therefore included in the K01 root.
- The inventory contains fifteen canonically ordered rows and four explicit
  coverage notes.
- The nine required D05 publisher IDs are present; omission is rejected.
- Focused K01 tests passed: 5 passed.
- The deterministic checker passed inserted-surface, source-digest,
  proof-verifier, and legacy-path witnesses.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

MUTANTS_ADDED: K01 rejects omission of a required publisher, source-byte
digest substitution changes the inventory root, an inserted unreviewed
surface changes the root, proof-verifier value movement is rejected, and a
legacy path cannot replace its post-switch rejection requirement with an
ordinary publication requirement.

FORMAL_EVIDENCE: None. K01 supplies typed source-bound evidence and
deterministic negative tests. It adds no Lean theorem, deployment proof,
dynamic call-graph proof, or production no-bypass theorem.

REMAINING_NONCLAIMS:

- `reviewed_source_set_only` is the generated completeness status.
- K01 does not prove that the reviewed configuration contains every production
  publisher, API route, worker, migration command, direct table writer,
  credential, container process, or effect sink.
- K01 does not prove runtime reachability, build inclusion, process isolation,
  datastore authority, caller authentication, or destination effect semantics.
- No unique production commit port, mounted M6 caller, runtime authority
  switch, deployment scan, migration, deployment, or value movement is
  claimed.
- The zUSD, perps, and autotrader rows are explicit outside-M6 candidates;
  R13 remains open.

REVIEW_RISKS: The inventory is source-bound and conservative, while its
coverage is still a reviewed input. K03/K04 must add syntax-aware structural
checks and an anchored topology relation. K06/K07 must seal legacy paths and
audit actual deployment/build/credential reachability before any R12 mounted
claim.
