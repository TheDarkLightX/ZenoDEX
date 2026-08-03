# FCIS M6 Task K07 Report

TASK_ID: K07
BASE_SHA: 31b4f9d8608db11cdd181a245c3686856fe29c71
SOURCE_HEAD_SHA: 78630667dc7c1bdbc6386d0151c20860cda21e7f
SOURCE_HEAD_TREE: 30c912ce3b76ec71746448a74be997610c52d8b4
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:

- config/deploy/fcis_m6_k07_deployment_audit_v1.json
- src/core/fcis_m6_k07_deployment_audit.py
- tools/build_fcis_m6_k07_deployment_audit.py
- experiments/fcis_m6_k07_deployment_audit_check.py
- tests/tools/test_fcis_m6_k07_deployment_audit.py
- docs/research/m6_tasks/TASK_K07_DEPLOYMENT_AUDIT_V1.json
- docs/research/m6_tasks/FCIS_M6_K07_DEPLOYMENT_AUDIT_SCHEMA_V1.md
- docs/research/m6_tasks/TASK_K07_PLAN.md

CLAIM_IMPLEMENTED: K07 implements a source-bound deployment-boundary audit.
The builder regenerates K01, K04, and K06, requires exact roots, audits 26
anchored source paths and four deployment paths, verifies two declared launch
bindings, checks inventoried worker coverage, scans direct protected-writer
markers and forbidden plaintext credential markers, and binds all findings into
one verifier-owned audit root. The clean-deployment gate returns a typed block
while findings remain.

STATUS_GAP: The current audit is not clean. It finds three direct protected
writer markers in `experiments/fcis_m6_h02_sqlite_publication.py` and two
plaintext demo-token markers in `.docker/entrypoint.sh`.

COMMANDS_RUN:

- python3 -m py_compile src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py
- python3 -m ruff check src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py
- python3 -m ruff format --check src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py
- python3 -m mypy --strict src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py
- python3 -m json.tool config/deploy/fcis_m6_k07_deployment_audit_v1.json
- python3 -m json.tool docs/research/m6_tasks/TASK_K07_DEPLOYMENT_AUDIT_V1.json
- python3 tools/build_fcis_m6_d05_tcg_inventory.py --check
- python3 tools/build_fcis_m6_k01_entrypoint_inventory.py --check
- python3 tools/build_fcis_m6_k04_topology_anchor.py --check
- python3 tools/build_fcis_m6_k06_legacy_seal.py --check
- python3 tools/build_fcis_m6_k07_deployment_audit.py --check
- PYTHONPATH=. python3 experiments/fcis_m6_k07_deployment_audit_check.py
- PYTHONPATH=. python3 -m pytest -q tests/tools/test_fcis_m6_k07_deployment_audit.py
- git diff --check

RESULTS:

- K01 root matched: `fc150266a7932c32d67ac5674251ae96db7f65a633a0e0b8eba791431682e31a`.
- K04 root matched: `da8e43caab444a5f88e7f7affede1671822fb63d6de890daf80fea88c07a5c35`.
- K06 seal root matched: `139a29f1938dfffb9ea4c72b5f6e99765bb9d1d0254654941ddf3c9f20a82ab0`.
- K07 audit root: `71807e0babf526928db94b8d7ecd2b6c13c1ca929a2a7700f3ca05f5c7aa463c`.
- Audited 26 anchored source paths and 4 deployment paths.
- Verified 2 declared launch bindings; no untracked-worker finding was emitted.
- Findings: 3 direct protected-writer markers and 2 credential-policy gaps.
- Clean-deployment gate: typed `GAP` block with finding count 5.
- Focused K07 suite passed: 1 passed.
- Four provenance/status/root/constructor mutants were killed.
- Python compilation, Ruff, formatting, strict mypy, JSON parsing, and diff
  whitespace checks passed.

MUTANTS_ADDED: K07 kills mutated status, crossed K04 root, `object.__new__`
audit provenance, caller audit construction, and caller clean-decision
construction. The baseline findings preserve the direct writer and plaintext
credential witnesses.

FORMAL_EVIDENCE: None. K07 supplies typed boundary checks, canonical audit
root recomputation, source scanning, and negative executable evidence. It adds
no Lean, SMT, TLA, production image, live process, or datastore theorem.

REMAINING_NONCLAIMS:

- K07 is a research-only audit over the exact reviewed K04 source set and four
  declared deployment paths.
- The H02 SQLite adapter remains a direct protected-table writer in this slice.
- The container entrypoint retains a plaintext demo-token default under its
  testnet-demo branch.
- K07 does not prove complete process reachability, image contents, credential
  isolation, datastore ownership, or runtime call-graph closure.
- No mounted caller, deployment, migration, authority switch, or value movement
  is claimed. M6 remains unmounted and non-promotable.

REVIEW_RISKS: The audit model and builder are a 425-line plus 496-line research
hotspot. The `GAP` result is the stronger safety outcome for the current source
set, while direct-writer remediation and production-boundary refinement remain
open.
