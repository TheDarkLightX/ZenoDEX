# FCIS M6 Task K04 Report

TASK_ID: K04
BASE_SHA: 7da3b05d4161c961f1a57cf798307a3e125a2dab
SOURCE_HEAD_SHA: dcca70a8fcf02cb00d4b5dd22ca0b9d55bff0240
SOURCE_HEAD_TREE: 1bf3896b12f238e693c11d2726a75d2346643b51
BRANCH: codex/j07-k01-j06-dependency-rebind-20260804

FILES_CHANGED:

- config/deploy/fcis_m6_k04_topology_anchor_v1.json
- docs/research/m6_tasks/TASK_K04_TOPOLOGY_ANCHOR_V1.json
- src/core/fcis_m6_k04_topology_anchor.py
- tools/build_fcis_m6_k04_topology_anchor.py
- experiments/fcis_m6_k04_topology_anchor_check.py
- tests/tools/test_fcis_m6_k04_topology_anchor.py
- docs/research/m6_tasks/FCIS_M6_K04_ANCHORED_TOPOLOGY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K04_PLAN.md

IMPLEMENTATION_HEAD_SHA: 26da7c198a43e0c248cd5823d98c6ce3037c2813
IMPLEMENTATION_TREE: 556ded187ad630ff3e5a4b5ec5422faca7946d9f
IMPLEMENTATION_PARENT: 7da3b05d4161c961f1a57cf798307a3e125a2dab

DEPENDENCY_REFRESH_HEAD: dcca70a8fcf02cb00d4b5dd22ca0b9d55bff0240
DEPENDENCY_REFRESH_TREE: 1bf3896b12f238e693c11d2726a75d2346643b51
DEPENDENCY_REFRESH_PARENT: e45e4c685e70eb0fa54a69e678132cb134ccb920

CLAIM_IMPLEMENTED: K04 has been rebound to the unchanged D05 publisher
inventory/topology and the current K01 entrypoint inventory. The existing typed
builder and checker were unchanged; the repair updates the authoritative
configuration and generated vector so the builder again regenerates and pins
the current topology anchor. The current K04 root is
4db1203f194a99a144c4b2a0a2613df288ac0f428959f87e9e529b4a35f576dd.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k04_topology_anchor.py tools/build_fcis_m6_k04_topology_anchor.py experiments/fcis_m6_k04_topology_anchor_check.py tests/tools/test_fcis_m6_k04_topology_anchor.py
- python3 -m ruff check src/core/fcis_m6_k04_topology_anchor.py tools/build_fcis_m6_k04_topology_anchor.py experiments/fcis_m6_k04_topology_anchor_check.py tests/tools/test_fcis_m6_k04_topology_anchor.py
- python3 -m ruff format --check src/core/fcis_m6_k04_topology_anchor.py tools/build_fcis_m6_k04_topology_anchor.py experiments/fcis_m6_k04_topology_anchor_check.py tests/tools/test_fcis_m6_k04_topology_anchor.py
- python3 -m mypy --strict src/core/fcis_m6_k04_topology_anchor.py tools/build_fcis_m6_k04_topology_anchor.py experiments/fcis_m6_k04_topology_anchor_check.py tests/tools/test_fcis_m6_k04_topology_anchor.py
- python3 -m json.tool config/deploy/fcis_m6_k04_topology_anchor_v1.json
- python3 -m json.tool docs/research/m6_tasks/TASK_K04_TOPOLOGY_ANCHOR_V1.json
- python3 tools/build_fcis_m6_d05_tcg_inventory.py --check
- python3 tools/build_fcis_m6_k01_entrypoint_inventory.py --check
- python3 tools/build_fcis_m6_k04_topology_anchor.py --check
- python3 experiments/fcis_m6_k04_topology_anchor_check.py
- PYTHONPATH=. python3 -m pytest -q tests/tools/test_fcis_m6_k04_topology_anchor.py
- git diff --check
- python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K04
- sha256sum --check --strict docs/research/m6_tasks/TASK_K04_SOURCE_MANIFEST.sha256

RESULTS:

- D05 regeneration passed with current inventory root
  `fe407a21588db0932df41b224234a5a5950478aa12cc1c564857b7a5bbc41ac2` and
  current topology root
  `9b2db149fd06876cf9e9fa592d891042320e52dcf0640c952431d913f12402e1`.
- K01 regeneration passed with current entrypoint root
  `b8c1ff0c8d8d8fba815cd500909e923aa2cf6b41ebbca92e9056cd9b33f98559`.
- K04 regeneration and checked vector passed with root
  `4db1203f194a99a144c4b2a0a2613df288ac0f428959f87e9e529b4a35f576dd`.
- Publisher insertion, source-set insertion, D05-root substitution, and
  noncanonical ordering changed or rejected the topology anchor as expected.
- Focused K04 suite passed: 3 passed.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

MUTANTS_ADDED: K04 covers inserted publisher, inserted source path, crossed
D05 topology root, and reversed publisher-order witnesses. The vector check
also rejects a derived root that differs from the reviewed pin.

FORMAL_EVIDENCE: None. K04 supplies deterministic source-root composition and
mutation evidence. It adds no formal TCG completeness theorem, deployment
reachability proof, or mounted authority certificate.

REMAINING_NONCLAIMS:

- The K04 anchor is complete only relative to the reviewed current D05/K01
  inputs and their declared source sets.
- K04 does not prove that all production publishers, workers, credentials,
  processes, or effect sinks are represented.
- K04 does not prove runtime reachability, datastore authority, deployment
  inclusion, legacy sealing, or value movement.
- No mounted caller, migration, deployment, runtime switch, or value movement
  is claimed. M6 remains unmounted.

REVIEW_RISKS: The pinned root detects drift after the reviewed source set is
chosen. It cannot detect an omitted publisher that never entered D05 or K01.
K05-K08 must add dynamic, legacy, deployment, and mounted theorem evidence.
