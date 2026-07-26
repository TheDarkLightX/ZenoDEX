# Implement FCIS M5-P3: controlled commit bundle and pure reference port

**Status:** semantically approved

**Prompt kind:** build

**Intended use:** implementation agent working in an isolated ZenoDEX worktree

**Visibility:** repository-local

**Contract version:** `zenodex/fcis-m5-p3-commit-bundle/v1`

**Execution authorized:** local inspection, edits, tests, structural-checker
changes, documentation, and local commits on the dedicated P3 branch

## Intent mirror

### User's real job

Complete the next FCIS milestone without repeating the earlier architecture
failure where behavioral tests passed while generic freezing, mutable
inheritance, copy hooks, and parallel validation bypassed the closed authority
algebra.

### Desired result

Create one controlled immutable bundle from one controlled committable decision,
derive outbox records from that same decision, and model expected-root atomic
publication as one pure immutable store transition. Every invalid, stale, or
pre-linearization crash path must expose the unchanged reference store.

### Non-goals

- Do not mount the new path in `src/core/dex.py`.
- Do not delete or repair the legacy oracle path.
- Do not implement M5-P4, M5-P5, or M6.
- Do not claim a production datastore transaction or external-delivery proof.
- Do not add Python or Rust dependencies.
- Do not redesign support-root v5, the decision algebra, or canonical codecs.
- Do not implement Rust parity in this checkpoint.

## Semantic traceability

| ID | Requirement | Origin | Status | Consequence if wrong |
| --- | --- | --- | --- | --- |
| R1 | One candidate supplies state, plan, receipt, replay, and outbox | user-stated | approved | Swappable outputs regain authority |
| R2 | Reject has no bundle or committable output | user-stated | approved | Rejection atomicity fails |
| R3 | Reuse the closed grammar; decoded claims remain non-authoritative | context-derived | approved | A second admission system can drift |
| R4 | Reference commit has one immutable linearization result | user-stated | approved | Partial publication becomes observable |
| R5 | P3 stays unmounted and makes no datastore claim | source-derived | approved | Evidence is overstated |
| R6 | Structural tests enforce mechanisms as well as outcomes | user-stated | approved | Forbidden architecture can pass behavioral tests |

## Required reading

Read these files completely before editing:

1. Root `AGENTS.md` and closer overlays.
2. `.agents/coding-style.md` from the primary checkout if absent in the
   linked worktree.
3. `docs/research/prompts/FCIS_M5_ATOMIC_MOUNT_REVIEWED_HANDOFF_20260724.md`.
4. `docs/research/FCIS_M5_P0_CONSOLIDATION_PREFLIGHT_20260725.md`.
5. `docs/research/FCIS_M5_P2_DECISION_CHECKPOINT_20260726.md`.
6. `src/core/fcis_decision_derivation.py`.
7. `src/core/fcis_decision_values.py`.
8. `src/core/fcis_commit_bundle_values.py`.
9. `src/core/fcis_outbox_values.py`.
10. `src/core/fcis_transition_values.py`.
11. `src/core/fcis_authority_admission.py`.
12. `src/core/fcis_authority_schema.py`.
13. `src/core/fcis_authority_dispatch.py`.
14. `src/state/fcis_committed_state_values.py`.
15. `src/state/committed_dex_snapshot.py`.
16. `src/state/state_transitions.py` patch-application functions.
17. `tests/core/test_fcis_decision_derivation.py`.
18. `tests/core/test_fcis_m5_authority_admission.py`.
19. `tools/check_fcis_authority_snapshot_contract.py` and its test file.

Run the style classifier before source edits. Record the exact start SHA and
confirm `79e3ff11` is an ancestor.

## Frozen authority pipeline

```text
raw source
-> closed command/context/state/budget admission
-> exact immutable evaluated material
-> FCISStepEvaluationOkV1
-> AcceptV1 | RejectV1 | CommittedFailureV1
-> controlled CommitBundleV1 | existing RejectV1
-> pure reference expected-root commit
```

Only the existing closed schema compiler may admit or canonically encode the
P0 claim graph. A decoded `CommitBundleClaimV1` is replay/verifier data. It is
never accepted as commit authority.

## Forbidden mechanisms

Any one of these is an automatic no-go:

- generic `deep_freeze`, `copy`, `deepcopy`, pickle, or copy hooks;
- mutable-class inheritance or frozen subclasses of mutable classes;
- seal/freeze lifecycle flags;
- `MappingProxyType` over caller-owned storage;
- a mutable builder class or mutable reference store;
- `Any`, `Mapping`, reflection, dataclass-field discovery, or caller-selected
  callbacks/registries/resolvers on the new authority edge;
- hand-written duplicate admission parallel to the closed combinator;
- accepting caller-supplied outbox identities, idempotency keys, receipt roots,
  bundle roots, successor state, commit plan, or outbox plan;
- converting admitted exact values back to mutable legacy values;
- storing duplicate authoritative copies of state, plan, replay, or receipt in
  the controlled bundle;
- separate state/effect/receipt/replay/outbox publication steps;
- I/O, filesystem, network, clock, randomness, environment, locale, timezone,
  Python `hash()`, unordered protocol iteration, or broad `except Exception`;
- modifying tests or gates to accept a forbidden mechanism;
- mounting any P3 value in the DEX runtime.

Fresh local lists or tuples used inside one pure function are permitted only as
non-escaping scratch storage that is discarded on failure.

## P3-D01: close the P2 outbox-budget gap first

`_budget_violation_v1` currently checks effect count but does not separately
check `TransitionBudgetV1.max_outbox_records`. Before constructing a bundle,
add this exact observation:

```text
observed_outbox_records
  = 0                              when settlement.events is None
  = len(settlement.events)         otherwise
```

Require:

```text
observed_outbox_records <= budget.max_outbox_records
```

Add at-bound and one-over tests. Do not pass the budget into P3 again after it
has been admitted and receipt-bound. This closes substitution risk.

## P3-D02: correct the reserved committed-failure value

The current `CommittedFailureV1` uses `receipt: object` and raises even with the
private construction token. Correct it in a new commit, without amending P2:

```text
CommittedFailureV1 {
  next_state: FCISCommittedStateV1
  commit_plan: CommitPlanV1
  receipt: CommittedFailureReceiptClaimV1
  private construction capability
}
```

Its `__post_init__` must perform the same exact-type and private-capability
checks as `AcceptV1`. There must remain zero production constructor call sites
for the current spot profile. This makes the variant structurally sound while
keeping it unreachable under the current profile.

Do not add a current-profile failure rule, public factory, dummy value, or
reserved constructor call merely to exercise it.

## P3-D03: controlled authoritative bundle

Add `src/core/fcis_commit_bundle_derivation.py`. Reuse these existing decoded
values and schemas:

```text
CommitBundleClaimV1
CommitBundleSourceV1
OutboxPlanV1
OutboxPlanSourceV1
OutboxRecordSourceV1
FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1
FCIS_OUTBOX_PLAN_SCHEMA_ID_V1
```

Do not invent a second decoded bundle schema.

Define one final, frozen, slotted authoritative `CommitBundleV1` with a
module-private construction capability. It should retain one committable
controlled decision, the derived exact outbox plan, canonical bundle bytes or
their controlled byte witness, and derived receipt/bundle roots. It must not
duplicate authoritative `next_state`, `commit_plan`, `patch`, `effects`,
`replay`, or `receipt` fields. Read-only properties may expose values reached
through the one decision.

All stored hashes and bytes are derived inside the controlled builder. No
public constructor or parameter accepts them.

The builder result is:

```text
CommitBundleBuildResultV1 = CommitBundleV1 | RejectV1
```

Rules:

- `RejectV1` returns unchanged and never creates a bundle.
- `AcceptV1` derives one bundle.
- `CommittedFailureV1` is supported structurally for the exhaustive algebra,
  while remaining unreachable in the current profile.
- A derivation inconsistency becomes a stable canonical ordinary rejection
  with no bundle. Add one narrowly scoped module-private rejection helper to
  `fcis_decision_derivation.py` only if necessary. Restrict its call sites in
  the structural checker.
- Wrong external types are not silently coerced into a decision or bundle.

## P3-D04: same-decision outbox derivation

The current spot profile emits outbox records only for
`decision.commit_plan.effects.settlement.events`, preserving the settlement's
semantic tuple order. An absent or empty event tuple produces an empty plan.
Do not synthesize proof requests or index refreshes in P3.

Construct `OutboxPlanSourceV1` from the exact retained event values and admit it
through `admit_fcis_authority_claim_v1`. Do not construct `OwnedEnumV1` or
`OutboxPlanV1` through a second validation path.

For record index `i`, kind `canonical_event`, and exact canonical event payload
bytes `p`, derive identities using explicit domain separation and length
framing. Use raw 32-byte digest values after validating canonical lowercase
`0x` digests.

```text
effect_identity_preimage_v1 =
  domain_sep("zenodex/fcis/outbox-effect-identity", 1)
  || raw32(receipt_root)
  || u32_be(i)
  || u32_be(len(kind_utf8)) || kind_utf8
  || u64_be(len(p)) || p

effect_identity = sha256(effect_identity_preimage_v1)

idempotency_preimage_v1 =
  domain_sep("zenodex/fcis/outbox-idempotency", 1)
  || raw32(receipt_root)
  || u32_be(i)
  || raw32(effect_identity)

idempotency_key = sha256(idempotency_preimage_v1)
```

Use the repository's canonical JSON projection/encoder for the already-owned
event payload. Do not use `repr`, `str`, pickle, Python `hash()`, or incidental
map iteration. Document these preimages next to the code and bind golden
vectors in tests.

## P3-D05: canonical bundle claim and root

Internally project the controlled committable decision into the existing exact
`AcceptClaimV1` or `CommittedFailureClaimV1`, then build
`CommitBundleSourceV1` from:

```text
expected_pre_root = decision.receipt.binding.pre_state_root
decision          = exact projected claim
receipt_root      = canonical root of the exact receipt
outbox_plan       = same-decision derived plan
```

Admit and encode that source through the closed authority grammar. Require the
admitted result to be exact `CommitBundleClaimV1` and equal the controlled
decision projection. Derive:

```text
bundle_root = sha256(
  domain_sep(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, 1)
  || canonical_bundle_claim_bytes
)
```

The controlled wrapper may cache the derived bytes/root, but the reference
commit port must recompute and compare them before publication because Python's
`frozen=True` can be bypassed with `object.__setattr__`.

## P3-D06: pure immutable reference commit port

Add `src/core/fcis_commit_reference.py`. Do not add a mutable interpreter class.
Use final, frozen, slotted values and pure functions.

The minimal model is:

```text
ReferenceCommitStoreV1 {
  current_state: FCISCommittedStateV1
  publications: tuple[ReferencePublicationV1, ...]
}

ReferencePublicationV1 {
  bundle: CommitBundleV1
}
```

The complete state, plan, receipt, replay, and outbox publication must be
reachable from the one stored bundle. Do not duplicate them into independently
replaceable publication fields.

Define exact status values for at least:

```text
PUBLISHED
STALE
INVALID
ALREADY_COMMITTED
CRASHED_BEFORE_LINEARIZATION
CRASHED_AFTER_LINEARIZATION
```

An explicit test-only crash-point enum is allowed. It is data passed to a pure
simulation and must never read a clock, random source, environment, or process
state.

Reference algorithm:

1. Revalidate the exact store and entire nested controlled bundle.
2. Recompute receipt root, derived outbox, canonical bundle bytes, and bundle
   root.
3. Apply every compare-and-replace patch atom and replay nonce advance to the
   observed exact state using existing pure patch functions.
4. Require the applied result to equal the bundle successor across all eight
   state fields.
5. Recompute observed pre-root and successor root using the receipt snapshot
   version.
6. If an exact valid bundle root is already in `publications`, return
   `ALREADY_COMMITTED` with the unchanged store. This check occurs after full
   revalidation.
7. If observed root differs from expected pre-root, return `STALE` with the
   unchanged store.
8. A modeled crash before the linearization point returns the unchanged store.
9. Otherwise create one new immutable store containing the complete
   publication and successor state in one function result.
10. A modeled crash after the linearization point returns that complete new
    store with `CRASHED_AFTER_LINEARIZATION`; no partial form exists.

Any validation, patch, replay, root, receipt, plan, or outbox mismatch returns
`INVALID` and the unchanged exact store. No exception may escape for an exact
store plus an exact but post-construction-corrupted bundle.

This reference port is test evidence for the abstract atomicity law. It is not
a production database adapter, crash-recovery proof, or delivery worker.

## P3-D07: structural checker expansion

Add the two new source files to `authority-graph`, `exact-consumers`, and
transitive `final-mount` coverage. Extend the checker and mutation suite to
reject all of these mutants:

1. Either new source file omitted from a relevant profile.
2. Public construction capability or an undeclared constructor call site.
3. A decoded `CommitBundleClaimV1` accepted by the commit port as authority.
4. Caller-supplied outbox plan, identity, idempotency key, receipt root, or
   bundle root.
5. Outbox identities that omit receipt root, effect index, kind, or payload.
6. Direct `OutboxPlanV1` construction instead of closed admission.
7. Duplicate bundle copies of state, plan, replay, effects, or receipt.
8. A production `CommittedFailureV1` constructor site.
9. A missing `max_outbox_records` budget check.
10. Mutable reference store, mutable publication list, or mutation of the input
    store.
11. Stale or invalid paths that construct a new publication.
12. Crash-before path that changes store state.
13. Crash-after path that exposes a partial publication.
14. Commit-port revalidation omitted for receipt, outbox, bundle bytes/root,
    patch application, replay application, or pre/post roots.
15. Broad `except Exception`, I/O, clock, randomness, environment, filesystem,
    network, locale, timezone, or Python `hash()` in either new core module.

The checker must detect mechanisms. Passing behavioral tests alone is
insufficient.

## Required executable tests

Use these exact invariant IDs in test docstrings or test names so review can
trace them.
These are P3 checkpoint trace labels. Do not rewrite the frozen PR #477/#478
requirements or matrix merely to register them. Bind them in the P3 evidence
note and completion receipt. The existing normative packet checker must remain
green and its 103 established bindings must not be weakened.


### Bundle and outbox

- `M5-P3-BUNDLE-001`: only the controlled builder constructs
  `CommitBundleV1`.
- `M5-P3-BUNDLE-002`: `RejectV1` returns unchanged and creates no bundle.
- `M5-P3-BUNDLE-003`: no events produces an exact empty `OutboxPlanV1`.
- `M5-P3-BUNDLE-004`: multiple events preserve semantic order and contiguous
  indices.
- `M5-P3-BUNDLE-005`: repeated derivation is byte-identical with stable IDs.
- `M5-P3-BUNDLE-006`: changing receipt, index, kind, or payload changes the
  relevant identity/vector.
- `M5-P3-BUNDLE-007`: bundle claim round-trips through the closed grammar.
- `M5-P3-BUNDLE-008`: swapped state, plan, receipt, replay, or outbox fails
  revalidation.
- `M5-P3-BUNDLE-009`: hostile nested `object.__setattr__` corruption fails
  closed with no publication.
- `M5-P3-BUNDLE-010`: current profile has zero committed-failure construction
  sites.
- `M5-P3-BUDGET-001`: outbox count exactly at the budget is accepted.
- `M5-P3-BUDGET-002`: one record over the budget returns typed rejection before
  bundle construction.

### Reference commit law

- `M5-P3-COMMIT-001`: root match publishes successor and one complete bundle.
- `M5-P3-COMMIT-002`: stale root returns the identical store object/value and
  no publication.
- `M5-P3-COMMIT-003`: invalid bundle returns unchanged store.
- `M5-P3-COMMIT-004`: crash before linearization returns unchanged store.
- `M5-P3-COMMIT-005`: crash after linearization exposes one complete
  publication and successor, never a partial shape.
- `M5-P3-COMMIT-006`: retry of the exact published bundle is idempotent and
  returns `ALREADY_COMMITTED`.
- `M5-P3-COMMIT-007`: patch application must reproduce all non-replay successor
  fields.
- `M5-P3-COMMIT-008`: replay application must reproduce the successor nonce
  field exactly.
- `M5-P3-COMMIT-009`: expected-old mismatch rejects with unchanged store.
- `M5-P3-COMMIT-010`: publication reachability exposes state, plan, receipt,
  replay, and outbox from one bundle lineage.

### Property and metamorphic evidence

Add deterministic Hypothesis or exhaustive bounded properties for:

```text
derive(decision) == derive(decision)
commit(store, valid_bundle, NONE) is deterministic
stale/invalid/crash-before -> result.store == store
published -> apply(bundle.plan, store.state) == result.store.current_state
retry(published_store, same_bundle) == unchanged published_store
event payload mutation -> effect_identity and bundle_root change
```

Use fixed deterministic settings and bounded examples. No test may depend on
wall time, test order, hash seed, network, or unseeded randomness.

## Required gates

Run narrow gates first:

```bash
python3 -m py_compile \
  src/core/fcis_decision_derivation.py \
  src/core/fcis_commit_bundle_derivation.py \
  src/core/fcis_commit_reference.py \
  tools/check_fcis_authority_snapshot_contract.py
python3 -m ruff check \
  src/core/fcis_decision_derivation.py \
  src/core/fcis_commit_bundle_derivation.py \
  src/core/fcis_commit_reference.py \
  tests/core/test_fcis_decision_derivation.py \
  tests/core/test_fcis_commit_bundle_derivation.py \
  tests/core/test_fcis_commit_reference.py \
  tests/tools/test_check_fcis_authority_snapshot_contract.py \
  tools/check_fcis_authority_snapshot_contract.py
python3 -m ruff format --check \
  src/core/fcis_decision_derivation.py \
  src/core/fcis_commit_bundle_derivation.py \
  src/core/fcis_commit_reference.py \
  tests/core/test_fcis_decision_derivation.py \
  tests/core/test_fcis_commit_bundle_derivation.py \
  tests/core/test_fcis_commit_reference.py \
  tests/tools/test_check_fcis_authority_snapshot_contract.py \
  tools/check_fcis_authority_snapshot_contract.py
python3 -m mypy \
  src/core/fcis_decision_derivation.py \
  src/core/fcis_commit_bundle_derivation.py \
  src/core/fcis_commit_reference.py
python3 -m pytest -q \
  tests/core/test_fcis_decision_derivation.py \
  tests/core/test_fcis_commit_bundle_derivation.py \
  tests/core/test_fcis_commit_reference.py \
  tests/core/test_fcis_m5_authority_admission.py
python3 -m pytest -q tests/tools/test_check_fcis_authority_snapshot_contract.py
```

Then run:

```bash
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount --json
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py
git diff --check
git status --short
```

`final-mount` is expected to remain fail-closed on legacy/mount findings. Record
the exact count and categories. Do not weaken the profile or call it passed.

Run the style, security red-flag, and design-metrics tools on changed authority
paths. If a repository-wide gate is unaffordable, record it as unrun. Never
convert an unavailable formal, Rust, Tau, ESSO, RISC0, or datastore lane into a
pass.

## Terminal condition

Create one or more local checkpoint commits only after:

1. all P3 source and semantic tests pass;
2. every listed structural mutant is killed;
3. all four pre-mount profiles return `ok=true`;
4. the final-mount failure remains explicit;
5. the mounted runtime is unchanged;
6. `git diff --check` passes;
7. a P3 evidence note states exact commands, results, and nonclaims.

Stop and report a blocker if a frozen decision conflicts with current source,
if a new public type or schema seems required, or if atomicity would require a
mutable interpreter or partial publication model. Do not improvise around a
conflict.

## Required handoff format

```text
Result:
- Outcome: M5_P3_COMPLETE_UNMOUNTED | M5_P3_BLOCKED
- Exact start head:
- Exact end head:
- Branch and worktree:
- Local commits:

Changed:
- List every changed file and its purpose.

Invariant/authority impact:
- State each closed or still-open invariant.

Evidence:
- command -> exact result

Commands not run:
- List every required command omitted and why.

Residual risk:
- State concrete remaining risks and explicit nonclaims.

Next safest step:
- Return to reviewer; do not push or mount.
```
