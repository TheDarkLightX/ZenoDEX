# FCIS M6 Task K07 Report

TASK_ID: K07
BASE_SHA: f0abe01a98247a1cf803e0a11c710786cfccfbce
SOURCE_HEAD_SHA: 92040e214c4dcd36c4e5172e7098f19e26f0300f
SOURCE_HEAD_TREE: 89b4704ef62940fcfd24f568f8f74152420a0e5a
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:

- .docker/entrypoint.sh
- config/deploy/fcis_m6_k04_topology_anchor_v1.json
- config/deploy/fcis_m6_k06_legacy_seal_v1.json
- config/deploy/fcis_m6_k07_deployment_audit_v1.json
- docs/research/m6_tasks/TASK_D05_TCG_INVENTORY_VECTOR.json
- docs/research/m6_tasks/TASK_K01_VALUE_MOVING_ENTRYPOINT_INVENTORY_V1.json
- docs/research/m6_tasks/TASK_K04_TOPOLOGY_ANCHOR_V1.json
- docs/research/m6_tasks/TASK_K06_LEGACY_SEAL_V1.json
- docs/research/m6_tasks/TASK_K07_DEPLOYMENT_AUDIT_V1.json
- experiments/fcis_m6_k07_deployment_audit_check.py
- tests/tools/test_fcis_m6_k07_deployment_audit.py

CLAIM_IMPLEMENTED: K07 continues to provide a source-bound deployment-boundary
audit. The entrypoint testnet-demo branch now requires an explicitly supplied
secret token and rejects an absent or empty `DEMO_API_TOKEN`. D05, K01, K04,
and K06 vectors were regenerated because their source-bound roots include the
deployment entrypoint. K07 still audits the current K04 source set and four
declared deployment paths, binds all findings into a verifier-owned root, and
blocks a clean deployment decision while findings remain.

STATUS_GAP: K07 remains blocked by three direct protected-writer markers in
`experiments/fcis_m6_h02_sqlite_publication.py`: `INSERT INTO`, `UPDATE `, and
`sqlite3.connect`. The entrypoint credential findings are absent after the
repair.

FUNCTIONAL_HEAD:

- commit: `379e0717137fb122175995de7c20250856375151`
- tree: `5ff6f00973a948315d1c25575eab6c348055c5b2`
- parent: `f0abe01a98247a1cf803e0a11c710786cfccfbce`

DEPENDENCY_REFRESH_HEAD:

- commit: `92040e214c4dcd36c4e5172e7098f19e26f0300f`
- tree: `89b4704ef62940fcfd24f568f8f74152420a0e5a`
- parent: `4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6`

The J07 switch and K06 seal were regenerated after the J06/K01 rebind. K07
implementation code is unchanged.

ROOTS:

- D05 publisher inventory: `fe407a21588db0932df41b224234a5a5950478aa12cc1c564857b7a5bbc41ac2`
- D05 topology: `9b2db149fd06876cf9e9fa592d891042320e52dcf0640c952431d913f12402e1`
- K01 entrypoint inventory: `c8be9fb9b9ef3a997f062752b829c4a2f887e439276d938628da59ae63902df2`
- K04 topology anchor: `6644cae606656411d0da64461d80a13030be65905cfd31916a33f1143bc25ee3`
- K06 legacy seal: `fa7707f4bb75a01643bdc375ab74cbcf9f108162bdbf462868b707f12e96a753`
- K07 audit: `7bea72c3418b600a3f34bc06473aa84c33747287d00b9597964c9a3729724d30`

COMMANDS_RUN:

- `bash -n .docker/entrypoint.sh`
- `ZENODEX_TESTNET_DEMO=1 env -u DEMO_API_TOKEN bash .docker/entrypoint.sh` and checked typed missing-secret rejection
- `python3 -m py_compile src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py`
- `python3 -m ruff check src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py`
- `python3 -m ruff format --check src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py`
- `python3 -m mypy --strict src/core/fcis_m6_k07_deployment_audit.py tools/build_fcis_m6_k07_deployment_audit.py experiments/fcis_m6_k07_deployment_audit_check.py tests/tools/test_fcis_m6_k07_deployment_audit.py`
- `python3 tools/build_fcis_m6_d05_tcg_inventory.py --check`
- `python3 tools/build_fcis_m6_k01_entrypoint_inventory.py --check`
- `python3 tools/build_fcis_m6_k04_topology_anchor.py --check`
- `python3 tools/build_fcis_m6_k06_legacy_seal.py --check`
- `python3 tools/build_fcis_m6_k07_deployment_audit.py --check`
- `PYTHONPATH=. python3 experiments/fcis_m6_k07_deployment_audit_check.py`
- `python3 -m pytest -q tests/tools/test_fcis_m6_k07_deployment_audit.py`
- `python3 -m pytest -q tests/tools/test_fcis_m6_k07_deployment_audit.py tests/tools/test_fcis_m6_k04_topology_anchor.py tests/tools/test_fcis_m6_k06_legacy_seal.py tests/tools/test_check_fcis_m6_k03_static_no_bypass.py tests/tools/test_fcis_m6_k05_bypass_mutation.py tests/core/test_fcis_m6_j07_authority_switch.py tests/core/test_fcis_m6_j07_authority_switch_properties.py tests/core/test_fcis_m6_j08_rollback.py tests/core/test_fcis_m6_j08_rollback_properties.py tests/core/test_fcis_m6_j09_migration_crash.py tests/core/test_fcis_m6_j09_migration_crash_properties.py`
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K07 --expected-head 91bce42607c2c2365087976bed1bee4a38cc1812`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_K07_SOURCE_MANIFEST.sha256`

RESULTS:

- The entrypoint rejects testnet-demo startup without an explicit secret
  token; no service process is started on that path.
- K07 regenerates and matches D05, K01, K04, and K06 exact current roots.
- K07 audits 26 anchored source paths and four deployment paths.
- K07 verifies two declared launch bindings and emits no untracked-worker
  finding.
- Findings: three direct protected-writer markers, zero credential-policy
  findings, zero missing-marker findings, and zero missing-binding findings.
- Clean-deployment gate: typed `GAP` block with finding count 3.
- Focused K07 suite passed: 3 passed, including the credential-default
  mutation witness and missing-secret startup test.
- Adjacent K03-K07/J07-J09 regression passed: 48 passed in 28.41 seconds.
- Python compilation, Ruff, formatting, strict mypy, JSON/vector checks, and
  diff whitespace checks passed.
- The packet lineage gate passed: Git objects, commit/tree pairs,
  report/evidence identities, and ancestry resolve to expected packet head
  `91bce42607c2c2365087976bed1bee4a38cc1812`.

MUTANTS_ADDED: K07 preserves four verifier-provenance/status/root/constructor
mutants. The repair slice adds a synthetic credential-default mutation witness
and a missing-secret entrypoint startup witness. Reintroducing the old
fallback pattern produces typed credential-policy findings.

FORMAL_EVIDENCE: None. K07 supplies typed boundary checks, canonical audit
root recomputation, source scanning, and executable negative evidence. It adds
no Lean, SMT, TLA, production image, live process, or datastore theorem.

REMAINING_NONCLAIMS:

- K07 is a deterministic research-only audit over the exact reviewed source
  set and four declared deployment paths.
- The H02 SQLite adapter remains a direct protected-table writer and prevents
  a clean K07 result.
- K07 does not prove complete process reachability, image contents, credential
  isolation, datastore ownership, unique-port mounting, or runtime call-graph
  closure.
- No mounted caller, deployment, migration, authority switch, or value
  movement is claimed. M6 remains unmounted and non-promotable.

REVIEW_RISKS: H02 direct-writer ownership and its refinement into a mounted
unique atomic commit port remain open. Root rebinding confirms source drift
through the dependency chain; it does not establish runtime authority.
