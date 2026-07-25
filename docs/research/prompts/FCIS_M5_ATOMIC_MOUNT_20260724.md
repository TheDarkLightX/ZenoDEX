# Implement FCIS M5 Atomic Mount and M6 Mounted-Path Cleanup

> **SUPERSEDED — DO NOT EXECUTE.** This candidate prompt predates the reviewed
> M4 support-root version split and incorrectly combines M5 with M6. Use
> `FCIS_M5_ATOMIC_MOUNT_REVIEWED_HANDOFF_20260724.md`, which pins exact source
> head `a6e20097d74641784402fb2af5a9939beaf11a9d` and contains the current
> pre-state support-root, closed-admission, atomic-bundle, and Python/Rust
> refinement gates.

**Status:** candidate conditional execution prompt derived from the normative FCIS packet
**Prompt kind:** build
**Intended use:** a high-capability implementation agent after two independent dependency reviews
**Visibility:** repository-local
**Contract version:** `zenodex/fcis-m5-atomic-mount/v1`
**Source intent:** perform one reviewed authority switch only after state and authority graphs are complete
**Execution authorized:** conditional; the prerequisite gate below is mandatory

Read `FCIS_M4_M5_SHARED_CONTEXT_20260724.md` completely before this file.

## Hard prerequisite gate

Do not edit M5 code until all of these exact-head artifacts exist:

1. M3 exact replay implementation with
   `0763a39de9daad13a3e189fa8ab3a9f6a1e3589c` as an ancestor.
2. An M4 completion receipt whose independent review verdict is
   `PASS FOR STACK PROGRESSION`.
3. A reviewed owned authority-graph head containing exact owned command,
   settlement, event, effect, receipt, and three-way aggregate decision values.
4. Green `state-substrate`, `authority-graph`, `exact-replay`, and
   `exact-consumers` structural profiles at the combined starting head.
5. Canonical snapshot, state-root, support-root, settlement, effect, signing,
   and receipt parity evidence at that same combined head.
6. A clean worktree, correct stack ancestry, current packet receipt, and no
   unresolved drift-review violation.

If any artifact is absent, stop and return a prerequisite report. Do not fill
the gap inside the M5 commit. In particular, do not invent temporary mutable
effects or receipts so the mount can proceed.

## Intent mirror

### User's real job

Switch the mounted DEX authority path to the reviewed exact state and owned
authority graphs in one indivisible code-review unit, with one candidate
driving state, effects, receipt, replay changes, roots, and outbox records.

### Desired result

`DexState`, mounted settlement/nonce application, aggregate step results, and
all mounted readers use exact owned types. A late failure exposes no partial
state or effect. Legacy representations remain only at explicit decode or
differential edges and are removed from the mounted authority call graph in the
same review unit.

### Non-goals

- Do not claim database linearizability or crash recovery from an in-memory
  candidate type.
- Do not implement external outbox delivery as part of the pure core.
- Do not add parallel execution, persistent maps, Rust ownership, or a new
  parser.
- Do not alter economics, rounding, order, authorization, nonce policy, roots,
  or public rejection semantics.

## M5.1 Capture the last legacy baseline

Before deleting or disconnecting any mounted legacy path, record golden valid
and rejected fixtures for:

```text
canonical state snapshot bytes
state root and root preimage
support root
settlement bytes and hash
effect bytes, hash, order, and fee totals
receipt bytes and root
nonce/replay result
public accept/reject/error
```

The fixture must include every optional module, every perps market variant,
all five spot actions, route exact-in/out, CoW, fees and dust, quote bindings,
rejected intents, malformed settlement, retry, and replay.

Commit or artifact-hash this baseline before the mount change. Do not refresh a
golden result merely because the new implementation differs.

## M5.2 Construct all eight DexState fields atomically

Target: `src/core/dex.py::DexState` and its exact construction helper.

The committed field graph and fixed admission order are:

```text
1. balances        CommittedBalanceTableV1
2. pools           OwnedMapV1[str, CommittedPoolStateV1]
3. lp_balances     CommittedLPTableV1
4. nonces          CommittedNonceTableV1
5. vault           None | CommittedVaultStateV1
6. oracle          None | CommittedOracleStateV1
7. fee_accumulator CommittedFeeAccumulatorStateV1
8. perps           None | CommittedPerpsStateV1
```

Required construction algorithm:

1. validate exact source types or the declared one-way legacy ingress types;
2. construct all eight exact candidates into single-assignment locals in the
   fixed order;
3. validate aggregate invariants, cross-field relationships, canonical entry
   limits, and the 4,000,000-byte state limit;
4. only after every validation succeeds, assign every field to the new frozen
   aggregate;
5. return the complete `DexState` or raise/return the existing typed admission
   rejection; never expose a partially initialized aggregate.

No source getter, setter, normalizer hook, or caller behavior may run before
exact source-shape validation. Revalidate already-owned values.

### Narrow frozen-dataclass assignment rule

Explicit `object.__setattr__` is forbidden on admitted values and on consumer
paths. The existing reviewed, one-time construction internals in
`OwnedMapV1`, `OwnedEnumV1`, and the closed combinator remain separately
checker-pinned and do not authorize consumer mutation. If frozen `DexState`
construction requires explicit assignment, the only additional permitted
source shape is inside the exact DexState construction function, with:

```text
receiver = self under construction
field = one literal name from the eight-field inventory
value = the corresponding single-assignment exact candidate
position = after all eight admissions and all aggregate checks
cardinality = exactly eight assignments
```

Extend the structural checker so it rejects an assignment with a different
receiver, raw source value, dynamic field name, ninth field, duplicate field,
missing field, or placement before the final check. A factory or custom frozen
constructor that avoids explicit mutation is acceptable only if the public
constructor cannot retain raw source fields and all late-failure tests pass.

Required negative evidence:

- each field invalid while the seven others are valid, especially field eight;
- every source alias retained and mutated after failed and successful
  construction;
- corrupted already-owned value in each field;
- subclass/lookalike for every exact field;
- aggregate byte limit at bound and one over;
- forbidden `object.__setattr__` moved before final validation;
- assignment of one raw source instead of its exact candidate.

## M5.3 Mount exact readers and transitions together

Change every mounted caller and consumer in the same review unit:

```text
src/core/dex.py::_validate_and_apply_settlement
src/core/dex.py::step and step helpers
mounted nonce validation/application
mounted strong settlement validation/application
state and support-root readers
integration adapters that consume DexState fields
canonical snapshot/root/effect/receipt encoders
```

The mounted path must use the reviewed M4 exact command, nonce, settlement,
fee, route, and support-root consumers. It must not call:

```text
validate_settlement_strong legacy facade
apply_settlement_pure on the authority path
validate_and_apply_intent_nonce_batch legacy facade
freeze_* compatibility classes
deep_freeze or copy-based settlement application
committed-to-legacy projections
```

Change signatures and implementations together. Do not leave a structural
protocol or union that lets a mutable legacy builder satisfy an exact core
entry.

## M5.4 Mount the three-way aggregate decision

Use the reviewed authority-graph decision values:

```text
Accept(next_state, commit_plan, receipt)
Reject(reason, rejection_receipt)
CommittedFailure(reason, next_state, commit_plan, receipt)
```

Required laws:

```text
Reject
  -> no successor
  -> no authoritative effect
  -> no nonce/replay update
  -> no outbox record
  -> canonical rejection receipt only

Accept or CommittedFailure
  -> every output derives from one evaluated candidate
```

Do not create `CommittedFailure` for an ordinary validation rejection. Use it
only when the protocol intentionally changes authoritative state despite the
requested operation not completing, such as consuming a nonce, charging a
failure fee, advancing a breaker, or recording an authoritative failed
attempt. If the mounted command set has no such case, retain the type and prove
it is unreachable under the current profile rather than inventing one.

Add exhaustiveness tests and ensure adding a fourth decision variant breaks
the registry/checker until every parser, transition, encoder, adapter, and
evidence binding declares it.

## M5.5 Build one immutable commit bundle

The pure core returns one data value equivalent to:

```text
CommitBundleV1 {
  expected_pre_root
  execution_context_hash
  algorithm_version
  next_state or canonical aggregate patch
  next_root
  commit_plan
  effects_root
  receipt
  receipt_root
  nonce_or_replay_updates
  outbox_records
}
```

The exact field schema comes from the reviewed authority-graph contract. Do not
duplicate or invent a competing carrier in M5.

State, effects, fees, receipt, roots, nonce changes, and outbox records are
constructed from the same evaluated candidate. No field is recomputed from a
raw command, live database read, wall clock, environment value, or mutable
source after validation.

`OutboxPlan` contains immutable records committed as data. Network delivery,
proof generation, notifications, and index refresh happen later in the shell
under receipt-derived idempotency keys. A successful in-memory test does not
prove datastore compare-and-swap or exactly-once delivery.

## M5.6 Final-mount structural gate

Upgrade the existing `final-mount` profile to cover the complete mounted call
graph, including callers outside the edited directories. The profile fails on:

```text
legacy mutable state or command type in a mounted core signature
legacy freeze/copy/seal mechanisms
legacy nonce or settlement transition call
mutable Settlement/Intent/Effects retained by DexState or a result
raw command reuse after exact admission
independent effect or receipt reconstruction
partial field assignment before complete admission
forbidden object/type attribute mutation outside the narrow DexState rule
unregistered decision/effect/receipt/event variant
mutable projection or broad authority protocol
ambient nondeterminism
```

Add mutation tests for every rule. The checker must analyze exact paths and
calls, rather than pass because the forbidden code was renamed or aliased.

## M6. Remove obsolete mounted authority in the same review unit

After the baseline and new-path parity pass, remove mounted use of:

```text
FrozenBalanceTable
FrozenLPTable
FrozenNonceTable
FrozenPoolState
deep_freeze compatibility paths
copy-based pure settlement application on authority paths
legacy mutable strong-validator replay
seal flags and mutable FrozenIntent/FrozenSettlement patterns
```

Legacy mutable classes may remain only at an explicitly identified decode,
builder, or differential-oracle edge whose output is immediately admitted and
which is unreachable from exact core consumers. Delete unused imports,
wrappers, and compatibility branches. Do not delete the golden differential
fixtures or evidence receipt.

## Required end-to-end evidence

Retain and pass every M2, M3, M4, and authority-graph test. Add at least:

1. `FCIS-T-477-017`: invalid final field exposes no state and mutates no source.
2. `FCIS-T-477-018`: corrupt owned values are fully revalidated.
3. `FCIS-T-477-019`: full optional/perps fixture has byte/root/effect parity.
4. `FCIS-T-477-021`: stateful quote, settle, LP, nonce, perps, reject, retry.
5. `FCIS-T-477-024`: mounted item and byte bounds plus one.
6. `FCIS-T-478-022`: accepted state/effect/receipt/hashes use one candidate.
7. `FCIS-T-478-023`: final aggregate reject returns rejection receipt only.
8. `FCIS-T-478-024`: canonical full settlement/effect fixture parity.
9. `FCIS-T-478-025`: sign, queue, reorder, execute, retry/replay determinism.
10. recursive retained-source alias mutation over the complete mounted graph.
11. same-candidate mutation tests for state, effects, receipt, roots, nonce,
    fees, and outbox.
12. rejected-transition no-op and committed-failure state-change distinction.
13. proposer-output-is-not-authority negative evidence for batch clearing.

Run top-down user-story and bottom-up authority/dataflow passes. Inspect every
integration consumer, serializer, proof ABI, metadata/manifest entry, and
supported client touched by the mounted types.

## Required commands

Run the narrow suites first, then at minimum:

```bash
python3 -m ruff check <changed files and tests>
python3 -m mypy
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount --json
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
git diff --check
```

Run the full repository suite and release-integrity gate when available. If a
toolchain is missing, keep the corresponding claim open. Do not mark an unrun
gate as passed.

## Acceptance relation

M5/M6 is complete only if:

```text
one canonical typed command
-> one exact evaluated candidate
-> one three-way decision
-> one immutable root-bound commit bundle
```

and:

```text
late reject => no partial authority escapes
accept/committed failure => all outputs use the same candidate
legacy mounted authority paths => absent
canonical bytes/roots/effects/receipts => baseline-equivalent
all prerequisite and final-mount profiles => green
independent mounted-call-graph review => PASS FOR STACK PROGRESSION
```

GitHub mergeability and green unit tests are insufficient without the exact
structural, parity, and independent-review evidence.

## Deliverables

- one atomic-mount source commit series with no mixed mounted authority state;
- `docs/research/FCIS_M5_M6_COMPLETION_RECEIPT_V1.json`;
- before/after canonical and root parity artifacts with hashes;
- complete requirement classification;
- final-mount checker plus mutation evidence;
- independent top-down and bottom-up review reports;
- exact GitHub head and check results;
- explicit shell, cross-language, economic, and release nonclaims.

## Stop conditions

Stop without mounting if:

- M4 or owned authority-graph review evidence is absent or stale;
- an exact type, effect, receipt, or decision variant required by the mounted
  path is missing;
- any output cannot be derived from the same candidate;
- a canonical byte, root, fee, order, rounding, rejection, or authorization
  result differs without an approved migration decision;
- the only implementation route requires a forbidden mutable projection,
  generic copy, broad protocol, post-admission mutation, or partial commit;
- a generated adapter, proof ABI, or supported caller cannot consume the exact
  type without an unreviewed semantic change;
- any final-mount checker violation or independent-review issue remains.

Return exactly:

```text
Exact M5/M6 head:
M4 reviewed ancestor:
Authority-graph reviewed ancestor:
Base and merge base:
Packet receipt SHA-256:
Changed mounted files and consumers:
Requirements satisfied:
Requirements still open:
Baseline and new parity artifact hashes:
Three-way decision evidence:
Same-candidate evidence:
Late-failure/no-partial-state evidence:
Final-mount checker result:
Independent review verdicts:
GitHub checks at exact head:
Commands not run and why:
Production claim status:
Residual risks and nonclaims:
Design questions or deviations: none | exact list
```
