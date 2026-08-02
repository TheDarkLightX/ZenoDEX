# FCIS M6 Task J07 Report

TASK_ID: J07
BASE_SHA: 1d6f4441ada8baec64c8768985e552b97ee6dc65
SOURCE_HEAD_SHA: 006e2507748d0de0525d636fdbb648b1f7f2f1e9
SOURCE_HEAD_TREE: 676590e5899ef150ed8aae476d66305023f92f58
BRANCH: codex/task-m6-receipt-rebind-20260802

FILES_CHANGED:
- config/deploy/fcis_m6_j07_authority_switch_v1.json
- docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json
- experiments/fcis_m6_j07_authority_switch_check.py
- src/core/fcis_m6_j07_authority_switch.py
- tests/core/test_fcis_m6_j07_authority_switch.py
- tests/core/test_fcis_m6_j07_authority_switch_properties.py
- tools/build_fcis_m6_j07_authority_switch.py

IMPLEMENTATION_HEAD_SHA: 006e2507748d0de0525d636fdbb648b1f7f2f1e9
IMPLEMENTATION_TREE: 676590e5899ef150ed8aae476d66305023f92f58
IMPLEMENTATION_PARENT: 1d6f4441ada8baec64c8768985e552b97ee6dc65

CLAIM_IMPLEMENTED: J07 adds an isolated authority-switch relation. It
requires a verifier-owned J06 QUIESCED gate and rechecks the F06 migration
authorization at point of use. The resulting atom advances the authority
epoch exactly once, changes authority/snapshot/head roots together, preserves
state and deployment roots, enables only the target profile, and rejects an
old writer token against the post-switch context.

COMMANDS_RUN:
- `PYTHONPATH=. python3 experiments/fcis_m6_j07_authority_switch_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_j07_authority_switch.py --check`
- `PYTHONPATH=. pytest -q tests/core/test_fcis_m6_j07_authority_switch.py tests/core/test_fcis_m6_j07_authority_switch_properties.py`
- J01-J06, F05, and F06 focused regression suite
- Python compilation, Ruff, Ruff formatting, and strict mypy for all J07
  source, checker, tool, and test files
- JSON parsing for the J07 configuration and vector
- `git diff --check`

RESULTS:
- The independent checker passed with switch root
  `e44729c68c7b9de2876772f2d08123b048f1a6767dc26f45c10cec1f35e73fcb`.
- The public vector matched source regeneration.
- Focused and property tests passed: 6 passed.
- The adjacent regression passed: 46 passed in 4.25 seconds before the final
  packet-only changes.
- F06 migration authorization was checked at issue and use; the J07 fixture
  recorded two verifier calls.
- Exact-class forged J06 gates and F06 tokens rejected.
- A mutated registered J07 context and writer token rejected at use.
- A legacy token rejected as stale after the switch; a fresh target token was
  accepted by the isolated post-switch writer gate.
- The fixture’s final authority row is QUIESCED and the atom is authorized at
  DUAL_CHECK, preserving dependency coherence.

MUTANTS_ADDED: Exact-class forged J06 gate, forged F06 token, mutated
registered J07 context, mutated registered writer token, rejecting external
verifier, profile collision, stale legacy token, target/legacy writer policy,
phase mismatch, epoch mismatch, and root-change witnesses.

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
gate.
