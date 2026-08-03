# FCIS M6 Task J07 Report

TASK_ID: J07
BASE_SHA: c8a861119e59701c96c9106ff4ba154f7b4650a2
SOURCE_HEAD_SHA: 4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6
SOURCE_HEAD_TREE: 95ae78274eb6695be508283bd34eac2e3118b093
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_j07_authority_switch_v1.json
- docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json
- experiments/fcis_m6_j07_authority_switch_check.py
- src/core/fcis_m6_j07_authority_switch.py
- tests/core/test_fcis_m6_j07_authority_switch.py
- tests/core/test_fcis_m6_j07_authority_switch_properties.py
- tools/build_fcis_m6_j07_authority_switch.py

IMPLEMENTATION_HEAD_SHA: d40e2d7bc028d93c5f38f24b158567a9fff752fc
IMPLEMENTATION_TREE: 3e1c984da840c02854e7846362bcffc340e7981b
IMPLEMENTATION_PARENT: c8a861119e59701c96c9106ff4ba154f7b4650a2

DEPENDENCY_REFRESH_HEAD: 4ecbc7b6992ea66dfd0f15d1f1ead6d4b84227e6
DEPENDENCY_REFRESH_TREE: 95ae78274eb6695be508283bd34eac2e3118b093
DEPENDENCY_REFRESH_PARENT: 6b3110f3d392d9fa23727e6b1e63be7edce6f8c2

DEPENDENCY_REBIND: The J06 K01 inventory rebind changed the gate and switch
roots. J07 was regenerated at the exact dependency-refresh head above; J07
implementation code is unchanged.

CLAIM_IMPLEMENTED: J07 adds an isolated authority-switch relation. It
requires a verifier-owned J06 QUIESCED gate and rechecks the F06 migration
authorization at point of use. The resulting atom advances the authority
epoch exactly once, changes authority/snapshot/head roots together, preserves
state and deployment roots, enables only the target profile, and rejects an
old writer token against the post-switch context. The repair independently
enforces state/deployment carry-forward, binds both contexts to the same
gate/token and predecessor lineage, and bounds typed rejection paths.

COMMANDS_RUN:
- `PYTHONPATH=. python3 experiments/fcis_m6_j07_authority_switch_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_j07_authority_switch.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_j07_authority_switch.py tests/core/test_fcis_m6_j07_authority_switch_properties.py`
- J01-J06, F05, and F06 focused regression suite
- Python compilation, Ruff, Ruff formatting, and strict mypy for all J07
  source, checker, tool, and test files
- JSON parsing for the J07 configuration and vector
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J07 --expected-head 91bce42607c2c2365087976bed1bee4a38cc1812`

RESULTS:
- The independent checker passed with switch root
  `acdc6ceaa486f697f12d249b5c72af5c8290b0bdf6532059995c75ea54028686`.
- The public vector matched source regeneration.
- Focused and property tests passed: 15 passed.
- The adjacent regression passed: 55 passed in 4.70 seconds.
- The packet lineage gate passed: Git objects, commit/tree pairs,
  report/evidence identities, and ancestry resolve to expected packet head
  `91bce42607c2c2365087976bed1bee4a38cc1812`.
- F06 migration authorization was checked at issue and use; the J07 fixture
  recorded two verifier calls.
- Exact-class forged J06 gates and F06 tokens rejected.
- A mutated registered J07 context and writer token rejected at use.
- A legacy token rejected as stale after the switch; a fresh target token was
  accepted by the isolated post-switch writer gate.
- A post context with changed state or deployment roots rejected during field
  validation after canonical root recomputation.
- A forged post context with a changed legacy profile rejected during switch
  result validation.
- Empty, over-capacity, and overlong typed rejection paths rejected.
- The fixture’s final authority row is QUIESCED and the atom is authorized at
  DUAL_CHECK, preserving dependency coherence.

MUTANTS_ADDED: Exact-class forged J06 gate, forged F06 token, mutated
registered J07 context, mutated registered writer token, rejecting external
verifier, profile collision, stale legacy token, target/legacy writer policy,
phase mismatch, epoch mismatch, root-change witnesses, state/deployment
carry-forward mutation, predecessor-lineage mutation, and rejection-path
bound violations.

FORMAL_EVIDENCE: No new Lean theorem is claimed. J07 supplies typed
deterministic relation, canonical-root, property, and negative evidence.

REMAINING_NONCLAIMS:
- J07 does not prove a production transaction, SQL isolation, crash behavior,
  or process-level atomicity.
- J07 does not authenticate the external F06 authority; the verifier adapter
  is a research premise.
- J07 does not prove runtime reachability, no-bypass coverage, rollback,
  accounting, backing, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: The identity registries are bounded research provenance
mechanisms. A production refinement must replace them with authenticated
verifier outputs and enforce the same complete switch atom inside the
linearized datastore transaction. The J07 fixture is independent of the
production runtime and does not establish that any real writer consults this
gate. The repair closes the declared bounded model obligations; it does not
remove the external-verifier, datastore, or runtime-mounting premises.
