# FCIS M6 Task K07 Report

TASK_ID: K07
BASE_SHA: f0abe01a98247a1cf803e0a11c710786cfccfbce
SOURCE_HEAD_SHA: dcca70a8fcf02cb00d4b5dd22ca0b9d55bff0240
SOURCE_HEAD_TREE: 1bf3896b12f238e693c11d2726a75d2346643b51
BRANCH: codex/j07-k01-j06-dependency-rebind-20260804

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

DEPENDENCY_REFRESH_HEAD: dcca70a8fcf02cb00d4b5dd22ca0b9d55bff0240
DEPENDENCY_REFRESH_TREE: 1bf3896b12f238e693c11d2726a75d2346643b51
DEPENDENCY_REFRESH_PARENT: e45e4c685e70eb0fa54a69e678132cb134ccb920

The J07 switch and K06 seal were regenerated after the J06/K01 rebind. K07
implementation code is unchanged.

ROOTS:

- D05 publisher inventory: `fe407a21588db0932df41b224234a5a5950478aa12cc1c564857b7a5bbc41ac2`
- D05 topology: `9b2db149fd06876cf9e9fa592d891042320e52dcf0640c952431d913f12402e1`
- K01 entrypoint inventory: `b8c1ff0c8d8d8fba815cd500909e923aa2cf6b41ebbca92e9056cd9b33f98559`
- K04 topology anchor: `4db1203f194a99a144c4b2a0a2613df288ac0f428959f87e9e529b4a35f576dd`
- K06 legacy seal: `5aa284fb6a2bd352a986e651df503e267e6a2c35e8ea52e0c1d6a6620745751e`
- K07 audit: `db9284ba9a5506466df2f4f00e9aa70eeb2d229696a62b94473d053a390cb508`

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
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks K07 --expected-head $(git rev-parse HEAD)`
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
  report/evidence identities, and ancestry resolve to the supplied exact
  packet head.

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
