# Implement FCIS M5 Atomic Mount

**Prompt status:** reviewed implementation handoff

**Milestone:** M5 only

**Contract:** `zenodex/fcis-m5-atomic-mount/v2`

**Required M4 source ancestor:** `a6e20097d74641784402fb2af5a9939beaf11a9d`

**Starting branch:** `origin/agent/fcis-pr454-reviewed-port-20260723`

**Authority switch:** conditional on every gate in this prompt
**M6 cleanup:** out of scope except for disconnecting legacy code from the mounted call graph

## Assignment

Produce one reviewable M5 candidate in which the mounted Python FCIS path:

```text
canonical bytes
-> closed typed command admission
-> exact immutable pre-state admission
-> one deterministic transition
-> one three-way decision
-> one immutable root-bound CommitBundle
-> one expected-pre-root shell commit port
```

Every accepted output must derive from the same candidate. Ordinary rejection
must expose no successor, authoritative effect, replay change, or outbox
record. A committed failure may change state only when a named protocol rule
requires the change.

Do not report M5 complete if a prerequisite, migration, or parity gate remains
open. A correct blocker report and a reviewed prerequisite checkpoint are
acceptable outcomes. A partial authority switch is not.

## 1. Create an isolated worktree

Use a new worktree and branch. Do not edit another agent's checkout.

```bash
git fetch origin
git worktree add /tmp/zenodex-fcis-m5-20260724 \
  -b agent/fcis-m5-atomic-mount-20260724 \
  origin/agent/fcis-pr454-reviewed-port-20260723
cd /tmp/zenodex-fcis-m5-20260724
git merge-base --is-ancestor \
  a6e20097d74641784402fb2af5a9939beaf11a9d HEAD
git status --short
```

The ancestry command must succeed and the worktree must be clean. Record the
exact starting SHA before editing.

## 2. Read these files completely, in order

1. `AGENTS.md` and every closer overlay for each touched path.
2. `.agents/coding-style.md`. In a linked worktree this git-ignored file may
   exist only at the primary repository root; read that copy and record the
   location.
3. `docs/specs/fcis_authority_snapshot_v1/DECISIONS.md`.
4. `docs/specs/fcis_authority_snapshot_v1/ERRATA.md`.
5. `docs/specs/fcis_authority_snapshot_v1/COMBINATOR_CONTRACT.md`.
6. `docs/specs/fcis_authority_snapshot_v1/PR477_STATE_SCHEMA.md`.
7. `docs/specs/fcis_authority_snapshot_v1/PR478_AUTHORITY_EFFECT_SCHEMA.md`.
8. `docs/specs/fcis_authority_snapshot_v1/PR477_MOUNTED_MIGRATION.md`.
9. `docs/specs/fcis_authority_snapshot_v1/ASSURANCE_FACTORIZATION_ADDENDUM.md`.
10. `docs/specs/fcis_authority_snapshot_v1/CONTEXT_DRIFT_PROTOCOL.md`.
11. `docs/specs/fcis_authority_snapshot_v1/TEST_MATRIX_PR477_PR478.md`.
12. `docs/research/FCIS_M4_COMPLETION_RECEIPT_V1.json`.
13. `docs/research/FCIS_M4_IMPLEMENTOR_REVIEW_20260724.md`.

Run the style classifier and inspect the dirty tree before source edits:

```bash
python3 .claude/skills/zenodex-style-map/scripts/which_style.py \
  src/core/dex.py src/core/fcis_step_evaluator.py src/state src/integration
git status --short
```

## 3. Non-negotiable design decisions

These decisions are frozen for this implementation. If repository evidence
contradicts one, stop and report the exact conflict. Do not silently choose a
different architecture.

### M5-D01: one closed authority admission algebra

Every untrusted or compatibility value enters through the declared closed
schema and `admit(schema, value, path, context)`. After `AdmitOk(exact)`, all
downstream authoritative reads use `exact`.

Forbidden:

- generic `deep_freeze(Any)` or recursive `Any -> Any` conversion;
- `copy.copy`, `copy.deepcopy`, pickle, or caller-controlled copy hooks;
- frozen subclasses of mutable classes;
- mutable-base inheritance for committed values;
- `_sealed`, `_frozen`, `_snapshot_sealed`, or post-construction mutation flags;
- `MappingProxyType` over caller-owned storage;
- reflective dataclass, enum, mapping, sequence, or object admission;
- constructor registries, resolvers, encoders, or callbacks selected by input;
- hand-written field validation parallel to the schema interpreter;
- exact admission followed by reads from the original value;
- conversion of exact values back to mutable legacy values on the mounted path.

The M4 evaluator deliberately exposes private already-admitted sinks for nonce,
settlement, and support-root evaluation. Treat those names as restricted
capabilities:

- do not replace them with public wrappers that re-admit or reconstruct values;
- do not import them outside their declared defining module and the exact M4
  evaluator;
- preserve the structural import allowlist and its mutation tests;
- preserve the runtime identity law proving that nonce, settlement, fee, and
  support consumers receive the same admitted command objects.

Exact source types, schemas, record registries, and rejection precedence are
closed, versioned data controlled by trusted code.

### M5-D02: immutable values and local scratch work

Committed values are transitively owned and immutable. A private function may
use a fresh local `list`, `dict`, or `set` as scratch storage only when all of
these are true:

```text
created inside the function
no caller alias
no callback receives it
no authoritative object stores it
failure discards it
one exact immutable value is returned
```

Do not introduce a mutable builder class, lifecycle flags, or a builder that
escapes. Prefer existing canonical patch constructors and closed combinators.

### M5-D03: three-way decision

The normative result is exhaustive:

```text
DecisionV1
  = AcceptV1(next_state, commit_plan, receipt)
  | RejectV1(reason, rejection_receipt)
  | CommittedFailureV1(reason, next_state, commit_plan, receipt)
```

Required laws:

```text
RejectV1
  -> no next_state
  -> no CommitPlan
  -> no replay or nonce update
  -> no OutboxPlan
  -> canonical rejection receipt only

AcceptV1 | CommittedFailureV1
  -> next_state, plan, receipt, roots, replay updates, and outbox records
     derive from one candidate
```

Do not classify an ordinary validation error as `CommittedFailureV1`.
If the current mounted command profile contains no intentional committed
failure, retain the exact variant and prove it unreachable for that profile.

### M5-D04: canonical encoding and protocol order are separate

Do not use a single vague `CanonicalKey` abstraction. Encoding answers which
bytes represent a value. Protocol order answers which value precedes another.
One byte key may serve both only when a versioned law and cross-language vectors
prove:

```text
protocol_cmp(a, b) = lexicographic_cmp(order_key(a), order_key(b))
order_key(a) = order_key(b) iff a = b
```

Unordered domains are normalized by a declared total protocol order.
Semantically ordered domains preserve and validate their existing order.
Route hops, nonce order, price-time order, proof ancestry, and rejection
precedence must not be re-sorted by an unrelated byte order.

### M5-D05: one immutable CommitBundle

Use or implement one exact owned carrier equivalent to:

```text
CommitBundleV1 {
  expected_pre_root,
  execution_context_hash,
  command_or_batch_root,
  algorithm_id,
  algorithm_version,
  schema_version,
  codec_version,

  next_state,
  next_state_root,
  canonical_patch,

  commit_plan,
  commit_plan_root,
  receipt,
  receipt_root,
  replay_updates,
  outbox_plan
}
```

`CommitPlanV1` contains authoritative state, value, fee, mint/burn, and
replay/nullifier changes. `OutboxPlanV1` contains immutable records that are
committed atomically as data and delivered later. External delivery, proof
generation, notifications, cache refresh, and index refresh are not core
effects.

Every outbox record has a stable idempotency key derived from the canonical
receipt identity and effect index or effect identity.

Do not invent a second bundle if the reviewed authority graph already contains
one. Extend the closed schema and all bindings together if a field is missing.

### M5-D06: support root is a pre-state commitment

This decision is fixed by `src/state/support_root.py` and the FCIS migration
specification:

```text
support_root_v5
  = commitment(project(exact_pre_state, complete_support(command, context)))
```

It is not a post-state root. The full post-state already has its own state root.
M4 already repaired `_candidate_evidence_v1` to compute support-root v5 from
the exact admitted pre-state used by the transition. Preserve that call shape,
and bind the completed support profile version and support-set commitment in
evidence.

Mounted support-root v4 bytes and meaning remain frozen. Never rewrite v4
fixtures to match v5.

### M5-D07: v5 must bind the complete support set and absence

The M4 v5 prototype fixes route coverage but is not a mount-ready support
profile. Derive the complete read set for every mounted command and every
context value that can change acceptance, rejection, arithmetic, effects, or
receipts.

Audit at least this table against actual runtime reads:

| Intent | Required pre-state support |
| --- | --- |
| create pool | sender balances for both assets; derived pool key with explicit absence/presence; LP recipient state if minting; nonce; relevant limits/config |
| add liquidity | sender asset balances; pool; recipient LP balance and duration/risk metadata; nonce; fee/policy context |
| remove liquidity | owner's LP balance and duration/risk metadata; pool; actual recipient balances for both assets; nonce; fee/policy context |
| swap exact in/out | sender input balance; pool; actual recipient output balance; active protocol-fee recipient or accumulator; nonce; oracle/policy context if consulted |
| route exact in/out | sender input balance; actual recipient output balance; every leg pool; route fingerprints; active fee recipient/accumulator; nonce; oracle/policy context if consulted |

The table is a minimum audit checklist, not permission to omit another actual
read. Instrument or trace the exact sequential evaluator and require:

```text
ActualStateReads   subset DeclaredSupportState
ActualContextReads subset DeclaredSupportContext
```

Version 5 must encode the support keys themselves and explicit
present/absent/zero states where absence affects validity. Omitting missing or
zero cells from a section cannot serve as the sole proof of non-membership.
Use a versioned presence tag and canonical key bytes. Add distinct-key
non-membership counterexamples.

Before promotion, v5 requires:

- a normative preimage specification;
- a source-derived command/field coverage inventory;
- Python golden preimages and digests;
- Rust encoder/decoder parity where Rust is a promoted implementation;
- proof-guest and Tau adapter bindings where those profiles support the field;
- migration and replay vectors showing explicit v4/v5 distinction;
- source, toolchain, schema, algorithm, and artifact hashes.

If this migration is not completed in this branch, keep the exact evaluator
unmounted and return an M5 prerequisite checkpoint. Do not mount against v4 or
the incomplete v5 prototype.

### M5-D08: all eight DexState fields move together

The authoritative aggregate has exactly these fields in this admission order:

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

Admission algorithm:

1. shallow exact-type check before any caller behavior;
2. admit each field through its declared closed schema into a single-assignment
   local;
3. validate aggregate cross-field invariants and the declared resource budget;
4. construct one frozen exact aggregate after every field succeeds;
5. publish nothing from a failed construction.

No raw field may be assigned temporarily. No partially initialized `DexState`
may escape. Revalidate already-owned inputs.

### M5-D09: shell atomicity has one linearization point

The shell port is specified as:

```text
commit(expected_pre_root, observed_pre_root, bundle)

expected_pre_root != observed_pre_root
  -> STALE
  -> publish none

expected_pre_root == observed_pre_root and bundle valid
  -> publish next state, authoritative plan, receipt, replay updates,
     and outbox records in one transaction
```

An in-memory type and an ESSO bounded model do not prove the production store
linearizable. Keep that nonclaim until the datastore transaction, crash/retry
behavior, and idempotent outbox delivery have executable evidence.

### M5-D10: Python and Rust refine one relation

Python and Rust must consume the same versioned schemas, integer domains,
canonical bytes, protocol orders, error precedence, context, roots, and
receipt fields. Do not independently redesign the transition in Rust.

Required cross-language law:

```text
Encode(PythonStepP(S, C, X)) = Encode(RustStepP(S, C, X))
```

for every promoted profile input, including rejects and committed failures.

If the Rust implementation is incomplete, the Python M5 candidate may remain
shadow-only. It cannot be called a cross-language or production mount.

Do not add `pydash`, Stillwater, or another functional helper dependency in
M5. The existing closed combinator, owned values, and canonical patch laws are
the authority mechanism. Stillwater may be evaluated later in an isolated Rust
leaf after dependency, panic, serialization, FFI, and no-semantic-drift review.

## 4. Mandatory checkpoint sequence

Keep checkpoints in separate commits. Do not combine them into one large
unreviewable change.

### Checkpoint M5-P0: prerequisite and drift audit

Before implementing the mount:

1. Run all four structural profiles.
2. Inventory exact source types for command, state, settlement, event, effect,
   receipt, decision, commit plan, replay update, outbox record, and bundle.
3. Confirm every type is composition-owned, exact, frozen, slot-based where
   applicable, closed-schema admitted, and canonically encoded.
4. Search for forbidden mechanisms in the complete mounted transitive call
   graph.
5. Record missing types and stale or contradictory normative files.
6. Confirm that each M4 private already-admitted sink has only its declared
   defining-module and evaluator importers, and that no sink re-admits,
   reconstructs, or reads a raw companion value.

If the exact authority graph is missing, implement it as an unmounted
prerequisite commit from `PR478_AUTHORITY_EFFECT_SCHEMA.md`. Add its schemas,
stable errors, canonical encoders, semantic-law tests, and structural checker
bindings. Do not mount in the same commit. Request review of M5-P0 before
continuing.

### Checkpoint M5-P1: complete support-root v5

1. Write the normative v5 preimage and coverage table.
2. Add a source-derived intent/field inventory.
3. Add explicit presence/absence encodings.
4. Verify and preserve evaluator evidence derived from exact pre-state.
5. Add Python golden vectors and v4 non-regression vectors.
6. Add Rust parity vectors or retain the unmounted status.
7. Add actual-read containment instrumentation for the sequential reference.

Stop after this commit for review. Do not mount if any coverage row is unknown.

### Checkpoint M5-P2: exact aggregate and transition result

1. Construct all eight exact `DexState` fields atomically.
2. Re-admit the canonical command exactly once.
3. Evaluate from one immutable pre-state and explicit context.
4. Produce one exhaustive `DecisionV1`.
5. Derive canonical patch, effects, receipt, roots, and replay updates from the
   same candidate.
6. Prove ordinary reject has no successor or authoritative plan.

Keep the old mounted path unchanged in this checkpoint.

### Checkpoint M5-P3: immutable commit bundle and shell port

1. Construct and revalidate one `CommitBundleV1`.
2. Bind expected pre-root, context hash, command/batch root, and all versions.
3. Include the canonical receipt and immutable outbox records inside the
   atomic publication data.
4. Add an in-memory reference compare-and-swap interpreter for deterministic
   tests only.
5. Add crash-point and stale-root tests that expose no partial publication.

Do not claim production datastore evidence from the reference interpreter.

### Checkpoint M5-P4: one mounted switch

Only after P0 through P3 pass review:

1. Capture final legacy golden accepted and rejected fixtures.
2. Change mounted signatures and implementations together.
3. Disconnect legacy mutable values from the authority call graph.
4. Keep compatibility conversion only at explicit decode and differential
   edges.
5. Run exact-vs-legacy differential replay over every valid supported command.
6. Require identical existing public behavior except for separately versioned
   and reviewed v5 evidence fields.
7. Add a rollback flag only if it selects between two complete authority
   implementations before evaluation. It must not allow mixed state, effects,
   roots, or receipts.

No dual-write, partial-field, or per-consumer gradual mount is permitted.

### Checkpoint M5-P5: final-mount structural gate

Add or extend a `final-mount` checker profile. It must inspect the entire
mounted transitive call graph and reject at least:

- any forbidden freeze/copy/inheritance/seal mechanism;
- raw mutable state or command types at core entry;
- broad structural protocols or `Any` on authority edges;
- reads from raw values after admission;
- ignored admission results;
- committed-to-legacy projection;
- a legacy validator, nonce consumer, fee consumer, route consumer, support
  reader, effect builder, or receipt builder on the mounted path;
- separate construction/publication of state, effects, receipt, replay, or
  outbox;
- support-root computation from post-state;
- support-root v4 relabeling or v5 use without the complete profile marker;
- effect or receipt derivation from a different candidate;
- broad exception catches that erase stable rejection precedence;
- IO, wall clock, randomness, environment, filesystem, network, locale,
  timezone, unordered iteration, or Python `hash()` in the core;
- callbacks, registries, resolvers, or encoders selected by authority input.

Mutation-test the checker itself. Each forbidden source mutant must make the
profile fail.

## 5. Required semantic tests

Bind every new test ID in the normative matrix and packet checker. At minimum:

### Admission and immutability

- all eight fields valid;
- each field invalid while the other seven are valid, including late field 8;
- source alias mutation after success changes no committed bytes or root;
- source alias mutation after failure exposes no partial object;
- exact-type subclass and lookalike rejection for every field;
- corrupted already-owned value is re-rejected;
- duplicate key, noncanonical order, cycle, depth, node, item, integer, and byte
  budgets at bound and one over;
- hostile property, iterator, mapping, equality, comparison, copy, serialization,
  and destructor hooks are not invoked before rejection.

### Decision laws

- accept derives all outputs from one candidate;
- each rejection phase returns only a canonical rejection receipt;
- reject is exact no-op for state, nonce, effects, receipt authority, and
  outbox;
- committed failure changes only the explicitly declared fields;
- current-profile committed-failure reachability or unreachability is tested;
- adding an unknown fourth variant fails parser, encoder, registry, adapter,
  and checker tests.

### Support-root v5

- v4 golden preimages and digests remain exact;
- v5 digest differs under its version and preimage;
- v5 uses pre-state even when the same command changes the touched cells;
- sender differs from recipient for swap, route, add, and remove cases;
- all route leg pools are bound;
- missing pool versus present pool produces different v5 preimages;
- zero supported balance versus a different absent key cannot alias;
- LP balance and every LP duration/risk field are bound;
- fee recipient/accumulator is bound when fee policy activates it;
- changing an undeclared irrelevant cell leaves the support root unchanged;
- changing any declared support cell changes its preimage or explicit value;
- actual reads and contexts are contained by declared support for every intent.

### Commit bundle and shell

- root match publishes all bundle fields together;
- stale root publishes none;
- invalid bundle publishes none;
- failure at every modeled publication point exposes none;
- duplicate retry is idempotent;
- outbox IDs are stable and duplicate delivery is harmless in the test
  interpreter;
- receipt, plan, patch, and bundle roots reject byte mutation;
- state, effect, receipt, replay, or outbox swapping between candidates fails.

### Differential and cross-language

- valid Python exact path equals the pinned legacy oracle for all unchanged
  protocol observables;
- rejected-input precedence and public code parity;
- Python/Rust canonical encode/decode golden vectors;
- Python/Rust accept, reject, roots, patch, plan, receipt, replay, and outbox
  byte parity for every implemented command;
- widths, overflow, division, rounding, dust, fee, and residue boundaries;
- deterministic replay under different hash seeds and process restarts.

## 6. Resource determinism

Use a first-class exact `TransitionBudgetV1` or the already reviewed equivalent.
It must bind at least:

```text
max canonical input bytes
max depth and nodes
max commands/intents
max state reads and context reads
max patch writes
max effects and outbox records
max candidate count
max witness and receipt bytes
max integer magnitude/bit width
```

Admission should reject before expensive work where possible. Stable budget
rejections are part of the protocol profile.

## 7. Required commands

Use the repository virtual environment. Run narrow gates after each checkpoint
and the broad gates only after the source checkpoint is clean.

```bash
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount --json

python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py
python3 -m ruff check <changed Python files and tests>
python3 -m ruff format --check <changed Python files and tests>
python3 -m mypy
python3 -m pytest -q <focused M5 tests>

PYTHON=.venv/bin/python bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
git diff --check
git status --short
```

If `.venv/bin/python` is not relative to the worktree, use the repository's
known virtual-environment interpreter explicitly and record the path.

Run security and hotspot review on every changed authority surface:

```bash
python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py
python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py <changed paths>
python3 .claude/skills/zenodex-refactoring/scripts/design_metrics.py \
  <changed paths> --top 20 --coupling
```

For Rust changes, run the exact touched workspace or crate gates:

```bash
cargo fmt --check
cargo test --all
cargo clippy --all -- -D warnings
```

Do not mark unavailable ESSO, Tau, Lean, RISC0, or datastore lanes as passed.
Record them as unavailable or open with exact reasons.

## 8. Stop conditions

Stop without mounting and return a blocker report if any of these occurs:

- the exact M4 ancestor is missing;
- a normative file contradicts a frozen decision;
- the owned authority graph is absent and cannot be completed as a separately
  reviewed P0 commit;
- any structural profile has an unexplained violation;
- support-root v5 has an unknown read/context cell or lacks absence semantics;
- v4 bytes change;
- exact admission and legacy validation both remain authoritative;
- one result component derives from a different candidate;
- mounted Python would outrun a required promoted Rust/verifier profile without
  an explicit shadow-only status;
- a late failure can expose partial state, effect, receipt, replay, or outbox;
- a gate is weakened, skipped, xfailed, or rewritten to accept the patch;
- the branch contains unrelated user changes.

## 9. Commit discipline

Use separate commits for P0, P1, P2, P3, P4, and P5 when each exists. Each
commit message should name the invariant it closes. Do not amend an earlier
reviewed checkpoint after handing it off; add a corrective commit.

Push the branch after each reviewed checkpoint so evidence is durable. Do not
force-push over another agent's branch.

## 10. Required completion receipt

Create:

```text
docs/research/FCIS_M5_COMPLETION_RECEIPT_V1.json
docs/research/FCIS_M5_IMPLEMENTOR_NOTES_20260724.md
```

The receipt must contain:

- exact starting and ending SHAs;
- M4 ancestor;
- packet hash;
- checkpoint commit SHAs;
- changed authoritative paths;
- invariant and authority impact;
- every command and exact result;
- source/toolchain/schema/algorithm hashes;
- v4 and v5 golden roots;
- structural profile results and compatibility findings;
- Python/Rust parity status by command;
- datastore and outbox evidence status;
- all unavailable lanes;
- nonclaims and residual risk;
- one of these exact outcomes:

```text
M5_MOUNT_CANDIDATE_COMPLETE
M5_PREREQUISITE_CHECKPOINT_ONLY
M5_BLOCKED_NO_AUTHORITY_SWITCH
```

## 11. Final response format

Return exactly this structure:

```text
Result:
- Outcome:
- Exact start head:
- Exact end head:
- Branch and worktree:
- Checkpoint commits:

Changed:
- ...

Invariant/authority impact:
- ...

Evidence:
- command -> exact result

Commands not run:
- ...

Residual risk:
- ...

Next safest step:
- ...
```

Do not say `complete`, `ready`, `verified`, `atomic`, `cross-language`, or
`production` beyond the exact outcome supported by the receipt.

## 12. Reviewer grading rubric

The reviewer will grade:

| Category | Weight | Automatic no-go condition |
| --- | ---: | --- |
| Frozen-design fidelity | 20% | second admission mechanism or forbidden freezing machinery |
| Exact authority graph | 15% | mutable/legacy value reaches mounted core |
| Support-root correctness | 15% | post-state root, incomplete support, absence alias, or v4 drift |
| Same-candidate derivation | 15% | state/effect/receipt/replay/outbox split across candidates |
| Atomic bundle and rejection law | 15% | partial publication or ordinary reject changes authority |
| Structural and mutation gates | 10% | mechanism bypass survives checker mutants |
| Python/Rust refinement | 5% | parity claimed without byte-level evidence |
| Evidence and nonclaims | 5% | stale SHA, missing command, or inflated public claim |

A high test count cannot compensate for an automatic no-go condition.
