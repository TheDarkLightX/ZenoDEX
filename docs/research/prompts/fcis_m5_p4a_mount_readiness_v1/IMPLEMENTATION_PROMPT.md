# Implement FCIS M5-P4A: golden baseline and authority-switch readiness

**Status:** semantically approved

**Prompt kind:** build

**Intended use:** implementation agent in an isolated ZenoDEX worktree

**Visibility:** repository-local

**Contract version:** `zenodex/fcis-m5-p4a-mount-readiness/v1`

**Required reviewed ancestor:** `c669aa678f04498cb9c08f0c6f6489fd07d0b6f1`

**Execution authorized:** local inspection, deterministic artifact generation,
tests, readiness checker work, documentation, and one local checkpoint commit

## Intent mirror

### User's real job

Advance M5 toward one safe authority switch while preventing a lower-cost
implementation agent from making an unreviewed design choice or hiding a
mount blocker behind passing behavioral tests.

### Desired result

Produce a source-pinned final legacy baseline, a complete mounted authority
call-graph ledger, an exact-vs-legacy differential replay harness, and one
fail-closed readiness receipt. Preserve the reviewed P3 implementation and keep
the mounted runtime byte-for-byte unchanged.

### Decision enabled

The primary reviewer can decide whether a separately reviewed P4B authority
switch may begin, and can identify the exact blockers when it may not.

### Non-goals

- Do not change `src/core/dex.py` or any mounted production adapter.
- Do not select the new FCIS path in any deployment profile.
- Do not dual-write, shadow-publish, or partially migrate state/effects/receipts.
- Do not delete or rewrite legacy state or authority code.
- Do not implement P4B, P5, or M6.
- Do not add dependencies.
- Do not repair unrelated coverage or legacy findings.
- Do not claim Rust, Tau, ESSO, Lean, RISC0, datastore, crash-recovery, or
  external-delivery evidence unless an exact existing artifact is replayed.
- Do not push. The reviewer will inspect and publish an accepted checkpoint.

## Semantic traceability

| ID | Requirement | Origin | Status | Consequence if wrong |
| --- | --- | --- | --- | --- |
| R1 | Capture final legacy accepted and rejected fixtures before switching | source-derived | approved | parity cannot distinguish regression from intended change |
| R2 | Compare all authority-visible observables, not only state roots | user/context-derived | approved | split candidate outputs can pass superficial parity |
| R3 | Inventory the complete mounted transitive call graph | user/context-derived | approved | a legacy authority edge can survive the switch |
| R4 | Keep runtime authority unchanged in P4A | agent-proposed safety split implementing the reviewed P4 stop rule | approved | an unreviewed partial switch could move value |
| R5 | Unknown or missing evidence forces a blocked result | user/context-derived | approved | readiness could be inferred from absence of evidence |
| R6 | Rust/verifier parity is explicit by command/profile | source-derived | approved | Python could be promoted beyond its refinement evidence |

## Required reading

Read these files completely before editing:

1. Root `AGENTS.md` and every closer overlay for touched paths.
2. `.agents/coding-style.md` from the primary checkout if absent locally.
3. `docs/research/prompts/FCIS_M5_ATOMIC_MOUNT_REVIEWED_HANDOFF_20260724.md`.
4. `docs/research/prompts/FCIS_M4_M5_SHARED_CONTEXT_20260724.md`.
5. `docs/research/FCIS_M5_P3_IMPLEMENTOR_REVIEW_20260726.md`.
6. `docs/research/FCIS_M5_P2_DECISION_CHECKPOINT_20260726.md`.
7. `docs/research/FCIS_M4_COMPLETION_RECEIPT_V1.json`.
8. The full re-entry order in
   `docs/specs/fcis_authority_snapshot_v1/CONTEXT_DRIFT_PROTOCOL.md`.
9. `src/core/dex.py` and every direct caller of its mounted step entry.
10. `src/core/fcis_decision_derivation.py`.
11. `src/core/fcis_commit_bundle_derivation.py`.
12. `src/core/fcis_commit_reference.py`.
13. `src/core/fcis_step_evaluator.py`.
14. `src/integration/dex_engine.py` and mounted validation/operation callers.
15. The state, settlement, nonce, fee, route, support-root, effect, receipt,
    replay, and outbox modules reached by those entries.
16. Existing differential, parity, golden-vector, and canonical-codec tests.
17. `tools/check_fcis_authority_snapshot_contract.py` and its tests.

Record the exact start SHA, packet file hashes, Python version, and virtual
environment interpreter. Run the style classifier before source edits.

## Frozen design

The approved pipeline remains:

```text
canonical authority bytes
  -> closed typed admission
  -> exact immutable pre-state, command, and context
  -> one deterministic evaluation candidate
  -> AcceptV1 | RejectV1 | CommittedFailureV1
  -> controlled CommitBundleV1 | unchanged RejectV1
  -> expected-root shell commit
```

P4A observes and compares this pipeline. It does not alter the mounted edge.

### Authority comparison law

For every unchanged public protocol fixture `f`:

```text
ComparableObservables(LegacyMounted(f))
  = ComparableObservables(ExactFCIS(f))
```

`ComparableObservables` must include every available authority-visible item:

```text
accept / reject / committed-failure kind
stable public rejection code, path, and precedence
next state and canonical next-state root
canonical patch writes and order
value effects and order
fee, rounding, dust, and residue values
nonce and replay updates
receipt-bound input fields and receipt root
outbox records, identities, and order
algorithm, schema, codec, support-root, and context versions
```

When the legacy path lacks a new versioned field, record it as an explicit
version delta with its governing decision. Do not silently omit it from the
comparison and do not rewrite old bytes to match a new field.

### Rejection law

```text
LegacyReject(f) and ExactReject(f)
  -> same public classification and precedence
  -> no successor authority
  -> no state, effect, replay, receipt-authority, or outbox publication
```

### Readiness law

```text
READY
  iff inventory_complete
  and golden_fixture_coverage_complete
  and differential_parity_complete
  and no_unknown_or_unexplained_mounted_edge
  and required_cross_language_rows_pass
  and all P0-P3 prerequisite gates pass
  and every artifact hash is current

otherwise BLOCKED
```

## Forbidden mechanisms

Any one of these makes the checkpoint a `NO-GO`:

- editing a mounted runtime or deployment authority path;
- generating fixtures from the new exact path and labeling them legacy;
- updating a golden because the new implementation differs;
- comparing only state roots while ignoring rejection/effect/replay/receipt
  differences;
- hand-writing a supported-command inventory without checking it against the
  mounted dispatch/registry source;
- treating a test skip, missing tool, timeout, or absent implementation as
  parity;
- generic freezing, copying, mutable inheritance, seal flags, reflective
  admission, or mutable authoritative builders;
- converting exact FCIS values back into mutable legacy values inside the
  authoritative path;
- dual admission or reading raw companions after exact admission;
- caller-supplied roots, hashes, identities, encoders, registries, or callbacks;
- `Any` or broad structural protocols on a new authority edge;
- I/O, clock, randomness, environment, locale, timezone, Python `hash()`, or
  unordered iteration in the functional core;
- broad `except Exception` that erases stable rejection classification;
- weakening tests, coverage floors, structural profiles, or golden checks;
- `.orig`, `.rej`, generated scratch, local paths, or undeclared artifacts in
  the packet or commit.

Tooling under `tools/` may read/write declared artifacts. It must be
deterministic, fail closed, reject duplicate JSON keys, and report exact source
and artifact hashes.

## P4A-D01: source-derived mounted command inventory

Create a deterministic inventory from the mounted dispatch and exact command
registries. It must enumerate every supported mounted intent/command variant,
including route exact-in and exact-out forms and every value-moving batch form
that the mounted entry accepts.

The inventory must distinguish:

```text
supported and mounted
supported only in an unmounted exact profile
legacy compatibility-only
unsupported and rejected
unknown
```

`unknown` is allowed in the evidence artifact and forces `BLOCKED`. Adding a
new enum or dispatch variant must fail the coverage test until its fixture and
parity rows are declared.

## P4A-D02: final legacy golden baseline

Add a deterministic baseline builder and a checked JSON artifact. Suggested
paths:

```text
tools/build_fcis_m5_p4a_baseline.py
docs/research/FCIS_M5_P4A_LEGACY_BASELINE_V1.json
```

The builder must execute the currently mounted legacy path at the reviewed
source ancestor. It must never call the exact FCIS evaluator to populate the
legacy result.

For every mounted command variant, include at least:

- one smallest valid accepted fixture;
- one boundary-valid fixture where the command has a numeric/resource bound;
- one stable rejected fixture;
- nonce/replay, insufficient-value, expired/finality, fee/dust/rounding, and
  recipient-different-from-sender cases where relevant;
- route multi-leg and all supported exact-in/exact-out distinctions;
- create/add/remove/swap route coverage consistent with the source-derived
  inventory.

Each fixture record must bind:

```text
fixture_id
command kind and canonical command bytes/hash
canonical pre-state bytes/root or source-pinned state fixture hash
explicit execution-context bytes/hash
algorithm/schema/codec/support-root versions
legacy mounted result kind
stable public rejection fields when rejected
canonical next-state root when accepted
canonical comparable patch/effect/replay/receipt/outbox projections
all explicit version deltas or unavailable legacy fields
```

Use only existing canonical encoders or a typed projection reviewed in this
checkpoint. Never serialize with `repr`, pickle, Python object identity, or
incidental mapping order.

Run the builder twice from the same source and require byte-identical artifact
output. Bind the generator hash, input source-tree hash, artifact SHA-256,
Python version, and generation command.

## P4A-D03: exact-vs-legacy differential replay

Add a test-only differential edge that consumes the same immutable fixture
inputs and evaluates:

```text
legacy mounted oracle
exact unmounted FCIS decision and bundle derivation
```

The edge may adapt fixture inputs independently for each side. It must remain
outside both authority paths, must not feed a differential result back into
settlement, and must not construct authority wrappers directly.

For each fixture:

1. prove both sides bind the same canonical command, pre-state, and context;
2. compare the complete observable projection above;
3. compare stable rejection precedence for negative cases;
4. require exact ordinary rejection to expose no committable output;
5. record only reviewed v5/version deltas as expected differences;
6. emit a minimized field path on first divergence.

The harness must fail on deliberate mutations to state root, recipient,
command order, nonce, fee/dust, event order, rejection code, receipt field,
outbox identity, and algorithm/schema version.

## P4A-D04: mounted authority/effect call-graph ledger

Create:

```text
docs/research/FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json
```

Trace every mounted path from external ingress through decode, admission,
transition, validation, nonce, fee, support root, effects, receipts, replay,
publication, and external delivery. Search beyond the edited directories.

Each row must contain:

```text
entrypoint
path and symbol
authority/value type crossing the edge
read/write/effect role
mounted reachability evidence
current mechanism
P4B disposition
owner and verification evidence
status
```

Use this closed status set:

```text
EXACT_READY
MIGRATE_IN_P4B
LEGACY_DIFFERENTIAL_ONLY
P5_GATE_REQUIRED
BLOCKER
UNKNOWN
```

Map all 79 current `final-mount` violations to ledger rows. Counts and
categories must reproduce the checker output exactly. `UNKNOWN`, unmapped
violations, a raw mutable authority edge, or a mixed-output publication path
forces `BLOCKED`.

## P4A-D05: cross-language and verifier readiness matrix

Create a source-pinned matrix for each mounted command and authority value:

```text
Python canonical encode/decode
Rust canonical encode/decode
Python/Rust decision bytes
patch/effect/replay/receipt/outbox bytes
proof-guest public input
Tau/verifier adapter field binding
```

Allowed row statuses:

```text
PASS_EXACT_BYTES
UNPROMOTED_SHADOW_ONLY
MISSING_BLOCKER
NOT_APPLICABLE_WITH_REASON
```

Only exact replay evidence may use `PASS_EXACT_BYTES`. A source listing or
similar type name is not parity. Any `MISSING_BLOCKER` forces overall
`BLOCKED`. `UNPROMOTED_SHADOW_ONLY` cannot authorize a mounted value-moving
switch.

Do not implement missing Rust/Tau/proof code in P4A. Record the next required
work as a separate checkpoint.

## P4A-D06: fail-closed readiness checker

Add:

```text
tools/check_fcis_m5_p4a_readiness.py
tests/tools/test_check_fcis_m5_p4a_readiness.py
docs/research/FCIS_M5_P4A_READINESS_RECEIPT_V1.json
```

The checker must:

- reject duplicate JSON keys and unknown fields/statuses;
- verify the exact command inventory and fixture coverage;
- verify source, generator, and artifact hashes;
- verify the mounted runtime paths are byte-identical to the reviewed start;
- reproduce all four pre-mount profile results and the exact final-mount
  violation summary;
- require every differential fixture to pass;
- require every call-graph violation to be mapped;
- require cross-language rows according to the readiness law;
- reject stale, missing, undeclared, `.orig`, `.rej`, or extra artifacts;
- emit sorted deterministic JSON and a nonzero exit code when blocked only if
  invoked with `--require-ready`;
- distinguish a structurally valid honest `BLOCKED` receipt from a `READY`
  receipt.

Normal validation may return success for a well-formed, honest blocked receipt.
The promotion command must fail closed:

```bash
python3 tools/check_fcis_m5_p4a_readiness.py --require-ready
```

The checker mutation suite must kill at least:

1. omitted mounted command;
2. missing accepted or rejected fixture;
3. fixture produced by the wrong evaluator;
4. changed golden output;
5. stale source or generator hash;
6. duplicate JSON key;
7. unknown status accepted;
8. final-mount violation omitted or miscounted;
9. `UNKNOWN` or `MISSING_BLOCKER` treated as ready;
10. Rust source presence treated as byte parity;
11. mounted runtime file changed without detection;
12. expected-difference allowlist widened by input data;
13. comparison reduced to state root only;
14. a skipped/xfail/timeout lane treated as pass;
15. extra undeclared artifact ignored.

## Required executable evidence

Use invariant IDs in test names or docstrings:

```text
M5-P4A-INV-001 source-derived inventory is exhaustive
M5-P4A-INV-002 unknown variant fails coverage
M5-P4A-GOLDEN-001 builder is byte-deterministic
M5-P4A-GOLDEN-002 legacy provenance cannot be substituted
M5-P4A-GOLDEN-003 each mounted command has accepted/rejected coverage
M5-P4A-DIFF-001 exact and legacy inputs bind the same command/state/context
M5-P4A-DIFF-002 accepted observable projections are equal
M5-P4A-DIFF-003 rejection code/path/precedence are equal
M5-P4A-DIFF-004 ordinary reject has no committable output
M5-P4A-DIFF-005 each named observable mutation is detected
M5-P4A-GRAPH-001 every mounted edge has one closed status
M5-P4A-GRAPH-002 all final-mount violations are mapped exactly once
M5-P4A-PARITY-001 exact-byte evidence is required for PASS_EXACT_BYTES
M5-P4A-READY-001 blocked receipt validates honestly
M5-P4A-READY-002 --require-ready fails on any blocker or unknown
M5-P4A-READY-003 mounted runtime is byte-identical to start
M5-P4A-READY-004 undeclared artifacts fail closed
```

Use deterministic property, metamorphic, or mutation tests for artifact replay,
fixture ordering, comparator completeness, and hash substitution. Do not use
wall time, unseeded randomness, real network, or test-order coupling.

## Required gates

Use the repository virtual environment. Run narrow gates first:

```bash
python3 -m py_compile \
  tools/build_fcis_m5_p4a_baseline.py \
  tools/check_fcis_m5_p4a_readiness.py
python3 -m ruff check <all changed Python files and tests>
python3 -m ruff format --check <all changed Python files and tests>
python3 -m mypy <new tools and harness modules>
python3 -m pytest -q <all P4A tests>
python3 tools/build_fcis_m5_p4a_baseline.py --check
python3 tools/check_fcis_m5_p4a_readiness.py
python3 tools/check_fcis_m5_p4a_readiness.py --require-ready
```

`--require-ready` may fail when the honest result is `BLOCKED`. Record the exact
blockers. Never rewrite the receipt or checker to make it pass.

Then run:

```bash
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount --json
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py
test -x "${ZENO_REPO_PYTHON:?set ZENO_REPO_PYTHON to the repository virtual-environment interpreter}"
PYTHON="$ZENO_REPO_PYTHON" bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
python3 tools/permissionless_assurance.py status
git diff --check
git status --short
```

Run the style classifier, security red flags, trust-surface inventory, and
design metrics from the primary checkout when the linked worktree lacks
`.claude/`.

The current reviewed P3 broad critical gate has one inherited coverage failure:

```text
src/core/settlement_strong_validator.py branch coverage 77.1% < 78.0%
```

Record whether the exact failure reproduces. Do not change unrelated tests or
the floor in P4A.

## Deliverables

- deterministic source-derived command inventory;
- final legacy golden baseline JSON and builder;
- exact-vs-legacy differential replay harness and tests;
- mounted authority/effect call-graph ledger;
- cross-language/verifier readiness matrix;
- fail-closed readiness checker and at least 15 mechanism mutants;
- readiness receipt with exact outcome, commands, hashes, blockers, and
  nonclaims;
- one local checkpoint commit.

## Terminal condition

The checkpoint is complete only when:

1. the mounted runtime is byte-identical to the start;
2. every mounted command is covered by source-derived accepted/rejected
   fixtures;
3. artifact generation is byte-deterministic;
4. the differential harness compares every declared observable;
5. every current final-mount violation maps exactly once;
6. all 15 readiness-checker mutants are killed;
7. the receipt honestly evaluates to `READY` or `BLOCKED` under the fixed law;
8. all narrow gates pass;
9. no unsupported evidence is promoted;
10. one clean local commit exists.

Stop immediately after that commit and return to the reviewer. Do not begin the
authority switch.

## Required handoff format

```text
Result:
- Outcome: M5_P4A_READY_FOR_REVIEWED_SWITCH | M5_P4A_BLOCKED_NO_AUTHORITY_SWITCH
- Exact start head:
- Exact end head:
- Branch and worktree:
- Local commit:

Changed:
- every file and purpose

Invariant/authority impact:
- closed and open invariants

Evidence:
- command -> exact result

Commands not run:
- command and exact reason

Residual risk:
- concrete risk and nonclaim

Next safest step:
- return to reviewer; do not push, mount, or begin P4B
```
