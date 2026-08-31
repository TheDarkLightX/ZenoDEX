# GlobalSettlementABI V2 Delta and Compatibility Contract

Status: `RESEARCH_ONLY_V2_DESIGN_ADMITTED_FOR_IMPLEMENTATION`

Production authority: `NONE`

Settlement authority: `NONE`

Release authority: `NONE`

Value-movement authority: `NONE`

## Exact subject

- Plan: `c52c71d01a3edf3e298a840d41345abdc2d6d26d`
- Plan admission: `c0fb36c62b20293ebc54fc530f3dfe2e8046576d`
- FCIS-hardened implementation base: `8703d9676fefff67d3a8ab4d32aebe03892f2ab3`
- V1 route-command closure checkpoint: `281821e63e8af1ac3cd0c9dcbb207951aa653a0b`
- Frozen V1 golden fixture SHA-256:
  `9e2b233076a0724635dffb3d7f06f1cb26b7b4ac3c79b3ae4f02420e5877c9e4`
- Preserved late-August donor archive SHA-256:
  `476505123bd4b188828ccd014e961a9ef250553a5c4d60e6e9d8b070c97d1373`

The late-August donor introduced useful origin, occurrence, Oracle, terminal,
and global-refinement semantics by changing V1 canonical fields in place. The
V1 reference contract requires a new version or explicit compatibility
evidence for any field, width, order, or framing change. Existing V1 decoders
reject unknown fields, so an optional-field interpretation cannot preserve old
decoder compatibility. The donor therefore supplies V2 implementation input;
it is not a V1 patch.

## Typed V2 delta

`GlobalSettlementABI V2` is a breaking, separately tagged settlement ABI. It
adds these foundational invariants:

1. Asset identity binds `asset_class`, `asset_origin_root`, and
   `atom_decimals` before value movement.
2. A module context owns the complete authenticated command occurrence; an
   occurrence identifier alone carries no authority.
3. Terminal obligations bind an explicit `liability_domain` so claimant,
   asset, custody, and liability reconciliation use the same denomination key.
4. Oracle occurrence deltas form a bounded canonical plan whose root is bound
   by module, lane, and route journals.
5. Accepted effects bind the exact occurrence consumption and lane write.
6. Python and Rust use identical closed fields, numeric widths, canonical
   order, hash domains, rejection precedence, and unknown-field policy.

V2 uses independent schema tags and hash domains. A V2 encoder never emits the
V1 schema string, and a V1 encoder never emits V2 fields. The initial V2
implementation order is asset transfer, managed assets, terminal and Oracle
plans, global reconciliation, then the remaining lane transitions.

## Ownership and composition

| Contract | Single owner | Producer | Consumer | Required binding |
| --- | --- | --- | --- | --- |
| asset origin | governed V2 asset registry | profile admission | asset and managed-asset transitions | profile, asset, class, decimals, origin root |
| command occurrence | settlement authentication boundary | occurrence constructor | every V2 lane module | chain, deployment, height, indices, command body, route, subject, grant, nonce, profile, pre-root, consumed IDs |
| lane-local state | selected lane module | pure lane transition | lane coordinator | exact pre/post lane roots and release ID |
| global effects | V2 global composer | accepted lane output | route and epoch composition | full principal, asset, custody-domain key and occurrence consumption |
| terminal liability | originating lane | terminal plan | global composer and migration verifier | obligation, claimant, asset, liability domain, amount, status |
| Oracle occurrence | Oracle lane | Oracle plan | global composer and dependent lanes | feed ID, pre/post occurrence, plan root, command occurrence |
| canonical publication | verifier-gated publisher | verified V2 epoch | atomic commit shell | ABI version, pre-root, command, post-root, effects, replay, receipt, outbox |

Composition is transactional. The global composer verifies exact subreceipts,
aggregates one canonical effect plan, and returns one candidate. It does not
recompute lane economics. The publisher remains outside this delta and cannot
be mounted by V2 core evidence alone.

## Rejection contract

Expected protocol failures return a closed V2 rejection. A rejection preserves
the exact pre-state root, emits the empty V2 effect plan, consumes no occurrence
or nullifier, creates no terminal or Oracle delta, and produces no outbox row.
The ordered precedence for the first asset-transfer port is:

```text
malformed typed input
-> missing occurrence
-> occurrence/context mismatch
-> release mismatch
-> unknown command
-> occurrence/command mismatch
-> unknown or disabled asset
-> missing or mismatched origin
-> unsupported native-asset accounting
-> subject and transfer guards
-> arithmetic and conservation guards
```

Later lane ports must publish their own total precedence tables before their
V2 schemas are admitted.

## V1 and V2 compatibility

- V1 canonical bytes, hash domains, field sets, goldens, decoders, and replay
  behavior remain frozen.
- V1 and V2 values do not cross-decode and are never accepted through an
  implicit default or field inference.
- A profile selects exactly one settlement ABI major version.
- A route cannot mix V1 and V2 module or coordinator receipts. No mixed-version
  adapter is admitted.
- V1 remains replayable under its exact V1 verifier after V2 exists.
- V2 starts in `SHADOW` with `NONE` authority. Activation requires explicit
  migration, proof, publisher, no-bypass, and exact-subject release evidence.

## Migration and recovery

A V1 to V2 migration certificate must provide and verify:

- exact source and target profile, state, and writer-epoch roots;
- one governed asset-origin binding for every retained asset;
- one liability-domain witness for every open terminal obligation;
- unchanged per-asset supply and owned/custodied totals, except for separately
  authorized issue or burn rows;
- replay, nonce/nullifier, terminal, Oracle, history, and outbox continuity;
- complete object classification with no dropped liability atom;
- V1 verifier acceptance of the source and V2 verifier acceptance of the
  target.

Missing origin or liability-domain evidence rejects migration. The migrator
does not infer either value from names. Before V2 activation, rollback means
discarding the unmounted V2 candidate and continuing V1. After an authoritative
V2 commit, recovery is forward-only through a new governed migration; V1
cannot silently resume as publisher.

## Refactoring preflight record

### Artifact and authority

V1 canonical types, journals, codecs, goldens, and decoders remain unchanged.
V2 owns new typed schemas, roots, occurrence binding, origin binding, terminal
liability domains, and Oracle plans. All current work is pure core or verifier
input with research-only claims.

### Construction and ownership

V2 values use exact closed constructors and transitively immutable tuples.
Snapshot ingress rejects subclasses before behavior-bearing access. Returned
state, effects, journals, and receipts own their complete reachable graphs.
Required regression tests mutate constructor inputs where mutable decode-edge
containers exist and attempt hostile subclass dispatch at every snapshot.

### API and callers

V1 public methods and callers remain intact. V2 receives distinct module,
schema, type, and hash-domain names. No caller is migrated by import aliasing.
Python, Rust, Lean, RISC0, generated fixtures, and publisher consumers each
require explicit V2 adoption evidence.

### Semantics

Amounts remain unsigned integer atoms with eight decimal places in the first
V2 slice. Effect deltas use checked signed bounds. Canonical collections reject
duplicates and use explicit stable keys. Unknown, malformed-present, Boolean
integer aliases, noncanonical order, overflow, stale occurrence, missing
origin, and unsupported native accounting reject without effects. Economic
policy not fixed by the admitted plan remains unavailable rather than inferred.

### Encoding and proof binding

V2 has independent schema tags, field sets, hash domains, fixture, and Rust
decoder with unknown-field rejection. The public journal binds ABI version,
profile/release identity, occurrence, pre/post roots, effect root, terminal
root, Oracle root, and receipt. Lean statements remain abstract until an exact
V2 source projection and runtime refinement test exists.

### Commit and failure model

The core returns candidates only. O-009 owns compare-and-swap publication of
state, effects, replay, receipt, and outbox as one atomic set. Crash, retry,
lost acknowledgement, concurrent conflict, and redelivery remain release
blockers until the V2 candidate reaches that shell.

### Performance and representation

Canonical tuples preserve the current bounded reference shape. Local maps may
be used only as fresh private builders and must freeze into canonical tuples.
No hot runtime representation is replaced in this design step. Benchmarks are
required before mounting any O(n) tuple lookup on a production-sized state.

### Change separation

The V1 command-to-release guard is the only V1 semantic repair in this
checkpoint. V2 schema work is isolated. UI, public mounting, unrelated debt,
and unresolved economic policy are outside scope.

## Evidence plan

1. Lock the V1 golden bytes and assert the three V1 journal field sets.
2. Add V2 Python and Rust codec vectors with identical canonical bytes and
   roots.
3. Retain missing/mismatched occurrence and origin counterexamples.
4. Add reject-is-no-op, constructor-alias, unknown-field, bound-neighbor,
   conservation, replay, and stateful sequence properties.
5. Port one lane at a time and require producer/consumer compatibility tests.
6. Add source-pinned Lean refinement only after executable Python/Rust parity.
7. Keep V2 `SHADOW` and all authority `NONE` until O-009 and later release gates
   close on one exact subject.

## Nonclaims and residual risk

This contract does not implement V2, authenticate asset-origin evidence,
select unresolved economics, prove any lane, qualify a RISC0 image, mount a
runtime route, migrate state, or authorize value movement. The preserved donor
contains large, locally green lane prototypes, but their current names and
canonical projections are not admissible V2 evidence until ported and checked
against this contract.
