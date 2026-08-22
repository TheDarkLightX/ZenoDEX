# Economic Initial-State Replay Preservation V1

Status: implemented candidate, unmounted, Rust targets uncompiled, independent
review pending after one no-result GPT-5.6 Sol max attempt.

This contract owns one narrow migration relation: the isolated initialization
transition preserves the predecessor global replay table exactly. Rows cannot
be added, removed, reordered or changed.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = exact predecessor replay-table preservation
A     = replay deletion, rewrite and injection prevention axis
T     = eliminate arbitrary roots and unauthenticated target-only additions
V     = kind, predecessor replay table, target replay table and both state roots
O     = derive_economic_initial_state_replay_continuity_root_v1
G     = GENESIS implies an empty target replay table;
        MIGRATION implies target replay table equals predecessor replay table
Obs   = canonical continuity root or typed rejection before receipt verification
K     = canonical replay_id order with exact row equality
E     = Python publisher tests, shared Python/Rust golden vector, Rust ABI tests
        and RISC0 shared-core reuse
Gap   = private lane nullifiers and complete nonce continuity
N     = a target-only replay row previously passed and could pre-consume an ID
Delta = exact table equality plus a root derived from disclosed state
```

## Preserved relation

For genesis:

```text
predecessor_state = None
target.replay_state = []
```

For an isolated migration:

```text
target.replay_state = predecessor.replay_state
```

Both state validators already require canonical `replay_id` order, unique replay
IDs and unique occurrence IDs. Exact tuple/vector equality therefore binds every
row field, count and order. Addition, deletion, replay-ID rewriting and
occurrence-ID rewriting reject.

The derived root commits:

```text
kind
source_state_root
target_state_root
complete source replay table
complete target replay table
```

The initialization statement's existing `replay_continuity_root` must equal this
derived root.

The repository fixture generator emits the complete predecessor/target input
and expected continuity root as a shared Python/Rust golden vector. The Python
renderer currently replays that vector. Rust replay remains uncompiled on this
workstation and therefore remains pending evidence.

## Migration-generated replay rows

Global replay rows cannot originate inside this isolated migration transition.
A governed command that legitimately consumes a replay identifier belongs in a
separately authenticated command occurrence after activation, or in a future
versioned migration statement that proves the command and its authorization.
This fail-closed V1 relation prevents migration from pre-consuming an identifier
and denying a later command.

## Invariant ownership

This contract does not own:

- source-head finality;
- private lane nullifiers hidden behind lane roots;
- history-root continuity;
- terminal-obligation or outbox continuity;
- object migration totality or classification semantics;
- migration release selection or proof-receipt authority.

Those remain separate certificates and proof statements.

## Test obligation

```text
Reach:     execute initialization admission with disclosed source and target
Infect:    add, delete or rewrite one replay row, or mutate the public root
Propagate: derive exact table equality and the canonical continuity root
Reveal:    reject before receipt verification or publication
```

Named mutants are removal of genesis emptiness, source-row preservation, exact
table equality, target-table commitment or journal-root equality.

## Nonclaims

- No proof covering private lane replay/nullifier state.
- No complete nonce-continuity theorem across private lane roots.
- No source-head finality or valid whole-migration theorem.
- No compiled changed Rust targets or real RISC0 receipt.
- No mount, writer rotation, production authority or value-moving authority.
