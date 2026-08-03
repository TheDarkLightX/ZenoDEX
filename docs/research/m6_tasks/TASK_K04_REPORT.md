# FCIS M6 Task K04 Report

TASK_ID: K04
BASE_SHA: 7da3b05d4161c961f1a57cf798307a3e125a2dab
SOURCE_HEAD_SHA: 26da7c198a43e0c248cd5823d98c6ce3037c2813
SOURCE_HEAD_TREE: 556ded187ad630ff3e5a4b5ec5422faca7946d9f
BRANCH: codex/task-m6-receipt-rebind-20260802

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

CLAIM_IMPLEMENTED: K04 has been rebound to the current D05 publisher
inventory, D05 topology, and K01 entrypoint inventory. The existing typed
builder and checker were unchanged; the repair updates the authoritative
configuration and generated vector so the builder again regenerates and pins
the current topology anchor. The current K04 root is
da8e43caab444a5f88e7f7affede1671822fb63d6de890daf80fea88c07a5c35.

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
  `e3b8fc99092de0fb56d08bf68ccb2f03278c776b684939765f86f1284fa9379e` and
  current topology root
  `e9fa1351ab36ecafa75ea9919ed791e31e17e998aa25521c4e3ce8a8f18f1857`.
- K01 regeneration passed with current entrypoint root
  `fc150266a7932c32d67ac5674251ae96db7f65a633a0e0b8eba791431682e31a`.
- K04 regeneration and checked vector passed with root
  `da8e43caab444a5f88e7f7affede1671822fb63d6de890daf80fea88c07a5c35`.
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
