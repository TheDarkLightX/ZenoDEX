# FCIS M6 Task K04 Report

TASK_ID: K04
BASE_SHA: 83d033e4c914c89638b33620b1977abf3a4db9d7
SOURCE_HEAD_SHA: a2399ef21e36eacc4ba1aa3d51a4651bb1f05365
SOURCE_HEAD_TREE: 86a2ca351419ecef3b96053888b8618342924d19
BRANCH: codex/task-H03-deterministic-crash-20260801

FILES_CHANGED:

- config/deploy/fcis_m6_k04_topology_anchor_v1.json
- src/core/fcis_m6_k04_topology_anchor.py
- tools/build_fcis_m6_k04_topology_anchor.py
- experiments/fcis_m6_k04_topology_anchor_check.py
- tests/tools/test_fcis_m6_k04_topology_anchor.py
- docs/research/m6_tasks/TASK_K04_TOPOLOGY_ANCHOR_V1.json
- docs/research/m6_tasks/FCIS_M6_K04_ANCHORED_TOPOLOGY_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K04_PLAN.md

IMPLEMENTATION_HEAD_SHA: a2399ef21e36eacc4ba1aa3d51a4651bb1f05365
IMPLEMENTATION_TREE: 86a2ca351419ecef3b96053888b8618342924d19
IMPLEMENTATION_PARENT: 83d033e4c914c89638b33620b1977abf3a4db9d7

CLAIM_IMPLEMENTED: K04 derives and pins a domain-separated topology anchor
from the D05 publisher inventory root, D05 topology root, K01 entrypoint
inventory root, K02 unique port ID, fifteen K01 publisher IDs, and the union
of D05/K01 source paths. The builder regenerates D05 and K01 before accepting
the K04 pin. The pinned K04 root is
60c11a0b9f694712abb452434481105f63c8576f1897994fa745bed0f42e0577.

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

- D05 regeneration passed with its pinned roots.
- K01 regeneration passed with its pinned entrypoint inventory root.
- K04 regeneration and checked vector passed with root
  60c11a0b9f694712abb452434481105f63c8576f1897994fa745bed0f42e0577.
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

- The K04 anchor is complete only relative to the reviewed D05/K01 inputs and
  their declared source sets.
- K04 does not prove that all production publishers, workers, credentials,
  processes, or effect sinks are represented.
- K04 does not prove runtime reachability, datastore authority, deployment
  inclusion, legacy sealing, or value movement.
- No mounted caller, migration, deployment, runtime switch, or value movement
  is claimed. M6 remains unmounted.

REVIEW_RISKS: The pinned root detects drift after the reviewed source set is
chosen. It cannot detect an omitted publisher that never entered D05 or K01.
K05-K08 must add dynamic, legacy, deployment, and mounted theorem evidence.
