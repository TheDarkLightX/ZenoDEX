# Economic Initial-State Replay Preservation V1

Status: implemented candidate, unmounted, Rust targets uncompiled.

This contract owns one narrow migration relation: replay rows already committed
by the predecessor cannot disappear or change during the isolated initialization
transition. It does not authorize target-only replay rows.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = predecessor replay-row preservation
A     = replay-resurrection prevention axis
T     = eliminate arbitrary replay_continuity_root declarations
V     = kind, predecessor replay table, target replay table and both state roots
O     = derive_economic_initial_state_replay_continuity_root_v1
G     = GENESIS implies an empty target replay table;
        MIGRATION implies every predecessor row occurs unchanged in target
Obs   = canonical continuity root or typed rejection before receipt verification
K     = canonical replay_id order with exact row equality
E     = Python publisher tests, shared Python/Rust golden vector, Rust ABI tests
        and RISC0 shared-core reuse
Gap   = authorization and purpose of target-only replay rows
N     = a deleted predecessor row and an arbitrary declared root previously pass
Delta = derive the journal root from disclosed state instead of trusting a root
```

## Preserved relation

For genesis:

```text
predecessor_state = None
target.replay_state = []
```

For migration:

```text
for every row in predecessor.replay_state:
    exists exactly one identical row in target.replay_state
```

Both state validators already require canonical `replay_id` order, unique replay
IDs and unique occurrence IDs. The preservation checker uses a deterministic
linear merge over those ordered tables. Deletion and occurrence-ID rewriting
reject.

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

## Target additions

The preservation relation permits target-only replay rows so a future migration
profile can represent an authenticated migration occurrence. This V1 slice does
not authenticate those additions. They remain visible in the target state and
continuity root, and a release cannot claim full nonce/nullifier continuity
until each addition is bound to a governed migration command occurrence and
authorization proof.

Target-only rows can deny a future command by pre-consuming an identifier. They
cannot erase a predecessor replay record under this relation. Authorization of
additions is therefore a release-blocking availability and authority obligation.

## Invariant ownership

This contract does not own:

- source-head finality;
- target-only replay-row authorization;
- private lane nullifiers hidden behind lane roots;
- history-root continuity;
- terminal-obligation or outbox continuity;
- object migration totality or classification semantics;
- migration release selection or proof-receipt authority.

Those remain separate certificates and proof statements.

## Test obligation

```text
Reach:     execute initialization admission with disclosed source and target
Infect:    delete or rewrite one predecessor replay row, or mutate the public root
Propagate: derive the ordered preservation relation and canonical root
Reveal:    reject before receipt verification or publication
```

Named mutants are removal of genesis emptiness, source-row preservation, exact
occurrence equality, target-table commitment or journal-root equality.

## Nonclaims

- No authorization for target-only replay rows.
- No proof covering private lane replay/nullifier state.
- No source-head finality or valid whole-migration theorem.
- No compiled changed Rust targets or real RISC0 receipt.
- No mount, writer rotation, production authority or value-moving authority.
