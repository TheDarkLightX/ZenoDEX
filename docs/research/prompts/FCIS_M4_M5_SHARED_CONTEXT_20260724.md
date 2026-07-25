# FCIS M4 and M5 Shared Implementation Context

**Status:** candidate handoff derived from the normative FCIS packet
**Prompt kind:** build
**Intended use:** implementation and independent-review agents working on ZenoDEX FCIS
**Visibility:** repository-local
**Contract version:** `zenodex/fcis-m4-m5-handoff/v1`
**Execution authorized:** M4 is authorized; M5 is conditional on every prerequisite in this file

## Source identity

Repository: `TheDarkLightX/ZenoDEX`

Required M3 implementation ancestor:

```text
0763a39de9daad13a3e189fa8ab3a9f6a1e3589c
```

M3 implementation tree:

```text
6109b9a8c4bbfd8bef364449ffa5111e5522ad86
```

Merge base used by the M3 branch:

```text
44d7f0d2a36b2141b553af1df734926c9d559bca
```

Expected branch at handoff creation:

```text
agent/fcis-pr454-reviewed-port-20260723
```

Before editing, run:

```bash
git status --short
git rev-parse HEAD
git merge-base --is-ancestor \
  0763a39de9daad13a3e189fa8ab3a9f6a1e3589c HEAD
```

Stop if the worktree is dirty for unexplained reasons or the required M3
ancestor check fails. A documentation-only descendant is acceptable. Record
the exact starting head in the checkpoint.

## Milestone state

| Milestone | Status at this handoff | Evidence or blocker |
| --- | --- | --- |
| M0 contract freeze | complete | normative packet and fail-closed packet checker |
| M1 exact readers | complete as unmounted substrate | state-substrate profile and focused tests |
| M2 exact leaf transitions | complete as unmounted substrate | `docs/research/FCIS_M2_COMPLETION_RECEIPT_V1_20260724.json` |
| M3 exact strong settlement replay | implementation complete at required ancestor | exact replay, route/CoW/create/liquidity differential evidence; exact-replay checker |
| M4 authoritative consumer migration | open | legacy command, nonce-intent, fee, and support-root consumers remain |
| owned authority graph | partial | owned intents and settlements exist; complete effects, receipt, and three-way aggregate review remains required before M5 |
| M5 atomic mount candidate | blocked | requires reviewed M4 and reviewed owned authority graph |
| M6 obsolete mounted representation removal | blocked | occurs in the same atomic-mount review unit after M5 parity evidence |

The dependency relation is:

```text
reviewed M2 + reviewed M3
  -> M4 exact consumer migration

reviewed state substrate through M4
+ reviewed owned authority graph
  -> M5 atomic mount candidate
  -> M6 obsolete mounted-path removal in the same review unit
```

No implementation summary, passing test count, or branch name can substitute
for these dependency checks.

## Normative design lock

Read `docs/specs/fcis_authority_snapshot_v1/ERRATA.md` first. Then run the full
re-entry order from `CONTEXT_DRIFT_PROTOCOL.md`:

1. `README.md`
2. `DECISIONS.md`
3. `ASSURANCE_FACTORIZATION_ADDENDUM.md`
4. `AUDIT_FINDINGS.md`
5. `COMBINATOR_CONTRACT.md`
6. `PR477_STATE_SCHEMA.md`
7. `PR478_AUTHORITY_EFFECT_SCHEMA.md`
8. `MOUNTED_ENVELOPE_INVENTORY.md`
9. `PR477_MOUNTED_MIGRATION.md`
10. `TEST_MATRIX.md`
11. `TEST_MATRIX_PR477_PR478.md`
12. `IMPLEMENTATION_RUNBOOK.md`
13. `requirements.json`
14. `REVIEW_CHECKLIST.md`

Also read every applicable `AGENTS.md`. Run the packet checker before editing:

```bash
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py --json
```

The expected structural inventory is 39 requirements and 103 declared and
bound test IDs. Generate and record the current packet receipt as required by
`CONTEXT_DRIFT_PROTOCOL.md`; do not copy a historical packet hash.

## Normative transition

The aggregate functional-core relation is:

```text
Step(CommittedState, TypedCommand, ExplicitContext)
  -> Reject(RejectReason, RejectionReceipt)
   | Accept(NewCommittedState, CommitPlan, Receipt)
   | CommittedFailure(FailureReason, NewCommittedState,
                      CommitPlan, Receipt)
```

Only `Reject` has no successor or authoritative effect. A leaf transition that
has no protocol-defined committed failure may keep its narrower two-way typed
result.

All outputs of an accepted or committed-failure aggregate result derive from
one evaluated candidate:

```text
next state
state root
canonical effects and effect order
receipt and receipt root
nonce or replay changes
outbox records
fees, rounding, and residues
```

## Authority and ownership laws

1. Admission is one-way: legacy source or decoded carrier to exact owned value.
2. Core transitions consume exact owned values and return new exact owned
   values, typed rejection, or one aggregate decision.
3. Every accepted child is data-only and transitively owned.
4. Already-owned values are fully revalidated.
5. Canonical encoding and protocol ordering are separate contracts.
6. Exact command values are single-assignment after admission. They cannot be
   rebound, replaced, projected to legacy objects, or mutated before replay.
7. Private local mutable buffers are allowed only inside one pure function,
   cannot escape, and require differential parity with the return-new
   reference.
8. External delivery remains an imperative-shell action driven by committed,
   idempotent outbox records.

## Forbidden mechanisms

The following are hard failures on a promoted authority path:

```text
generic deep_freeze or deep_thaw
copy.copy, copy.deepcopy, pickle, or caller copy hooks
mutable-class inheritance for committed values
seal flags or post-construction mutable caches
hand-written parallel validation that bypasses the closed combinator/profile
Any-to-Any authority functions
broad Mapping, Sequence, Iterable, set, or frozenset admission
broad isinstance for a declared exact authority source
reflective arbitrary dataclass or Enum admission
caller-selected registry, resolver, constructor, or encoder behavior
public committed-to-mutable or to_scratch conversion
mutable domain builders at core entry points
legacy object construction inside admission resolvers
object.__new__ construction bypass
object.__setattr__, object.__delattr__, type.__setattr__, or type.__delattr__
  on admitted values
unbounded recursion or unbounded authority collections
wall clock, environment, filesystem, network, locale, random, Python hash,
  unordered iteration, or race-dependent behavior in the core
```

The final DexState construction may require a narrowly checked frozen-dataclass
assignment mechanism. M5 defines the only permitted shape. It does not create
a general exception for mutation of admitted values.

## Current M3 evidence

The M3 candidate at the required ancestor has established:

- exact `OwnedSettlementV1` plus exact tuple `OwnedIntentV1` admission and full
  revalidation;
- exact strong replay without owned-to-legacy command projection;
- exact successor candidate equality against the legacy differential oracle;
- route, CoW, create-pool, add/remove liquidity, fee, malformed, and rejection
  coverage;
- exact-value single-assignment and dataflow structural checks;
- mutation tests for raw-path coexistence, rebinding, and post-admission
  `object`/`type` mutation bypasses;
- Ruff and mypy success;
- acceptance-TCB coverage with the strong-validator branch floor unchanged;
- critical gate success before the final checker hardening and focused checker
  success after it. The receiving agent must rerun the critical gate at its
  exact starting head.

This evidence closes only the M3 implementation slice. It does not mount
production authority.

## Shared working method

For each slice:

```text
read exact requirement
-> add minimized failing evidence
-> implement one closed change
-> run narrow tests and structural checker
-> compare exact legacy/reference outputs
-> inspect callers and consumers
-> record exact-head evidence
-> independent read-only drift review
```

Keep M4 and M5 in separate commits and separate review checkpoints. Do not
combine a consumer migration with the final DexState mount.

## Shared evidence commands

Use the repository virtual environment if present. At minimum run:

```bash
python3 -m ruff check <changed files and tests>
python3 -m mypy
python3 docs/specs/fcis_authority_snapshot_v1/check_packet.py --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph --json
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay --json
bash tools/run_critical_quality_gate.sh
python3 tools/check_production_boundary.py --json
git diff --check
```

Run the milestone-specific commands in the corresponding prompt. Report any
unrun gate precisely.

## Claim boundary

Even after M5, do not claim datastore linearizability, crash recovery, exactly
once external delivery, Rust or proof-guest parity, deterministic parallelism,
footprint soundness, persistent-collection performance, economic terminal
closure, or production release readiness unless their separate contracts and
evidence are complete.

