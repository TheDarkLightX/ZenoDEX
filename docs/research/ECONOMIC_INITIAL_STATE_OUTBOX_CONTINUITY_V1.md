# Economic Initial-State Outbox Continuity V1

Status: implemented candidate, unmounted, Rust targets uncompiled.

This contract owns one narrow initialization relation: a migration preserves
the complete registered external-effect outbox exactly. Genesis begins with no
pending or acknowledged external-effect rows. The contract does not prove
delivery, finality, destination behavior, or acknowledgment authenticity.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = exact external-outbox preservation
A     = pending-obligation loss and migration-time delivery-forgery axes
T     = eliminate arbitrary outbox_continuity_root declarations
V     = kind, predecessor outbox, target outbox and both state roots
O     = derive_economic_initial_state_outbox_continuity_root_v1
G     = GENESIS implies target.outbox = [];
        MIGRATION implies target.outbox = predecessor.outbox
Obs   = canonical continuity root or typed rejection before receipt verification
K     = canonical effect_id order, exact row equality and at most 4096 rows
E     = Python admission and BVA tests, shared Python/Rust golden vector,
        Rust ABI tests and RISC0 shared-core reuse
Gap   = source-head authority, delivery and acknowledgment refinement
N     = a mutated public root or changed migration outbox previously passed
Delta = derive the journal root from disclosed exact tables and reject changes
```

## Preserved relation

For genesis:

```text
predecessor_state = None
target.outbox = []
```

For migration:

```text
target.outbox = predecessor.outbox
```

Equality covers effect ID, registered destination ID, payload hash, originating
commit ID, status, row count and canonical order. Migration cannot enqueue a
new external effect, remove an obligation, change a payload or destination, or
convert `PENDING` to `ACKNOWLEDGED`. Each such action requires its own ordinary
authenticated transition and publication evidence outside the isolated
migration block.

The derived root commits:

```text
kind
source_state_root
target_state_root
complete source outbox
complete target outbox
```

Source and target outbox tables each have a 4,096-row ceiling. The bound is
checked before state validation, copying or hashing. A future release needing
compaction or a larger table requires a versioned continuity rule and evidence;
V1 intentionally chooses a smaller behavior space.

## Invariant ownership

This contract does not own:

- authentication of the predecessor as the finalized source head;
- derivation of outbox rows from authorized committed effects;
- external-chain finality or destination correctness;
- transport delivery, retry, ambiguous acknowledgment or idempotency;
- terminal obligations represented outside the outbox;
- private lane state, history, replay/nullifier or migration totality;
- migration release selection or proof-receipt authority.

## Test obligation

```text
Reach:     execute initialization admission with disclosed source and target
Infect:    delete, add or rewrite one outbox row, mutate its status, or mutate
           the public continuity root
Propagate: derive exact-table equality and the canonical continuity root
Reveal:    reject before receipt verification or publication
```

Named mutants are removal of genesis emptiness, exact-table equality, row-field
equality, the 4,096-row preflight, target-table commitment or journal-root
equality. Tests use AAA structure, BVA at 4,096/4,097, and the commit-port
observable that the receipt verifier has zero calls on rejection.

## Nonclaims

- No external delivery, finality, acknowledgment or idempotency proof.
- No permission to mutate or compact outbox rows during migration.
- No source-head finality or valid whole-migration theorem.
- No compiled changed Rust targets or real RISC0 receipt.
- No mount, writer rotation, production authority or value-moving authority.
