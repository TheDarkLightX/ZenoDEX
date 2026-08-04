# FCIS M6 Task J07 Report

TASK_ID: J07
BASE_SHA: 225e99f9fe862cb06818515c53666352a031ee5d
SOURCE_HEAD_SHA: cd29859c3c8604279c80fec5956f8dc9595ab359
SOURCE_HEAD_TREE: 75165d79a31a9d69066eec7e7b6b2677b8a8db28
BRANCH: codex/tau-placement-frontier-20260803

FILES_CHANGED:
- docs/research/m6_tasks/TASK_J07_TAU_WRITER_AUTHORITY_V2.json
- experiments/fcis_m6_j07_authority_switch_check.py
- experiments/fcis_m6_tau_j07_writer_authority_check.py
- formal/tau/m6_tau_placement_frontier_v1.json
- src/core/fcis_m6_j07_writer_admission_v2.py
- src/core/fcis_m6_j07_writer_token_v3.py
- tests/core/test_fcis_m6_j07_writer_admission_v2.py
- tests/integration/test_fcis_m6_tau_j07_writer_eligibility_v1.py
- tests/tools/test_fcis_m6_task_packet_validator.py
- tools/build_fcis_m6_j07_authority_switch.py

IMPLEMENTATION_HEAD_SHA: cd29859c3c8604279c80fec5956f8dc9595ab359
IMPLEMENTATION_TREE: 75165d79a31a9d69066eec7e7b6b2677b8a8db28
IMPLEMENTATION_PARENT: 23fae16a41744a0d709639fa85cc45bd5e46389b

CLAIM_IMPLEMENTED: J07 remains an isolated, unmounted authority-switch
relation. The repaired live path requires one verified post-switch authority
context, one independently verified writer-admission context, one Tau-derived
eligibility receipt, and one complete V3 token. Admission revalidates the exact
authority context after the external verifier returns. Expected verifier and
transport failures return authority-empty typed rejects. Admission and token
provenance registries each enforce an 8,192-live-value capacity and reclaim
mutation snapshots after their registered values become unreachable. The
canonical machine-readable Tau V2/V3 vector now covers the live relation.

COMMANDS_RUN:
- `PYTHONPATH=. python3 experiments/fcis_m6_j07_authority_switch_check.py`
- `PYTHONPATH=. python3 experiments/fcis_m6_tau_j07_writer_authority_check.py`
- `PYTHONPATH=. python3 tools/build_fcis_m6_j07_authority_switch.py --check`
- focused J07/Tau/eligibility pytest command recorded in the evidence JSON
- adjacent F05/F06/J05/J07/J08/Tau-profile/projection pytest command recorded
  in the evidence JSON
- targeted Python compilation, Ruff, Ruff formatting, and strict mypy commands
  recorded in the evidence JSON
- JSON parsing for the formal companion and both J07 vectors
- security trust-surface, red-flag, style-map, and design-metrics triage
- `git diff --check`
- `python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks J07 --expected-head "$(git rev-parse HEAD)"`
- `sha256sum --check --strict docs/research/m6_tasks/TASK_J07_SOURCE_MANIFEST.sha256`

RESULTS:
- The authority-switch checker passed with switch root
  `acdc6ceaa486f697f12d249b5c72af5c8290b0bdf6532059995c75ea54028686`.
- The Tau writer-authority checker passed with V3 token root
  `e52dcd85a16d3899f57124a1beec8f2c6e263b4b66b435af150676208538ebd0`.
- Both generated public vectors matched exact source regeneration.
- Focused J07, eligibility, and Tau refinement tests passed: 66 passed.
- The feasible adjacent regression passed: 130 passed, 2 skipped because the
  exact Tau binary was unavailable.
- Ruff, formatting, targeted strict mypy, Python compilation, JSON parsing,
  and the security red-flag scan passed.
- Two independent read-only review passes identified the stale packet,
  verifier-callback mutation, unbounded snapshot retention, stale formal
  companion, and absent live V2/V3 vector. Each finding now has a direct repair
  or permanent regression test.
- A verifier that mutates the authority context cannot mint an admission
  context and receives `authority_context_rejected/post_verifier`.
- Runtime verifier failure returns `external_verifier_rejected` with no token,
  accepted value, or effect.
- Capacity exhaustion returns typed admission/token rejection without minting.
- Admission and token snapshots are removed after their values become
  unreachable.
- The formal companion now records the live Tau binding consumer and the
  generated V2/V3 vector instead of the superseded no-consumer statement.
- Packet coverage requires every live writer-authority source, vector, formal
  companion, builder, and regression test.

MUTANTS_ADDED: Verifier-time authority-context mutation, verifier runtime
failure, admission-registry exhaustion, token-registry exhaustion, retained
snapshot leak, omitted live authority file, stale source hash, crossed
promotion subject, crossed source schema, crossed eligibility policy, crossed
verifier profile, mutated registered admission context, every mutated V3 token
coordinate, moved token/admission pairing, V1 token issue/use, and V1 Tau
eligibility refinement.

FORMAL_EVIDENCE: No new Lean, Tau, ESSO, or solver theorem is claimed. J07
supplies typed deterministic runtime relations, generated canonical vectors,
property and mutation tests, fail-closed packet validation, and a corrected
machine-readable formal companion. The exact Tau binary was unavailable, so no
new Tau execution receipt is claimed.

REMAINING_NONCLAIMS:
- J07 does not implement a production transaction, datastore lock, crash
  refinement, mounted publisher, deployment switch, or value movement.
- The external admission and eligibility verifiers remain shell premises; this
  slice does not establish their cryptographic authenticity, policy currentness,
  or selection from a mounted verifier registry.
- The bounded Python provenance registries are research mechanisms, not durable
  production authority.
- J07 does not prove store currentness, runtime reachability, no-bypass,
  rollback, accounting, backing, global economic safety, or zUSD safety.
- M6 remains research-only, unmounted, and non-promotable.

REVIEW_RISKS: A production refinement must replace in-process provenance with
authenticated verifier outputs, bind the selected verifier and policy to the
exact promotion subject and current state, and consume the complete relation
inside the unique linearized publication transaction. The 8,192-value bound
fails closed under resource pressure and does not establish production sizing.
The sparse worktree omitted several J01-J06 helper modules, so the full adjacent
migration regression could not collect; the strongest available 130-test
subset passed. The peer-review service was unavailable with an authentication
error, so the retained adversarial review evidence comes from two existing
read-only review agents rather than that service.
