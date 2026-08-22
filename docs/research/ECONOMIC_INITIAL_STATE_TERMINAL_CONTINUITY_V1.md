# Economic Initial-State Terminal Continuity V1

Status: implemented candidate, unmounted, Rust targets uncompiled.

This contract owns one narrow initialization relation. At full admission,
genesis commits every terminal-obligation row that the separate initial-state
atom-coverage gate has classified. Migration preserves the complete predecessor
terminal-obligation table exactly. The contract does not establish whether an
obligation is valid, funded, payable, or controlled by the named claimant.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = exact terminal-obligation preservation
A     = migration-time terminal-table mutation
T     = eliminate arbitrary terminal_continuity_root declarations
V     = kind, complete predecessor and target terminal tables, state roots
O     = derive_economic_initial_state_terminal_continuity_root_v1
G     = GENESIS implies predecessor = None;
        MIGRATION implies target.terminals = predecessor.terminals
Obs   = canonical continuity root or rejection before receipt verification
K     = canonical obligation_id order and exact row equality
E     = executed Python admission, BVA, and golden-fixture checks;
        Rust ABI/vector test source and RISC0 shared-core wiring are uncompiled
Gap   = source-head authority, obligation validity, funding, claimant control,
        payable terminal routes, and complete migration classification
N     = a substituted terminal root previously reached receipt verification
Delta = derive the journal root from disclosed tables and reject every mutation
```

## Preserved relation

For genesis:

```text
predecessor_state = None
target.terminal_obligations = rows classified by the target atom manifest
```

For migration:

```text
target.terminal_obligations = predecessor.terminal_obligations
```

Equality covers obligation ID, lane ID, claimant, asset, amount atoms, status,
row count, and canonical order. Creation, deletion, draining, tombstoning, or
rewrite requires an ordinary authenticated transition outside the isolated
migration block. A later migration release may introduce a versioned proved
transformation rule; V1 deliberately exposes no such degree of freedom.

The derived root commits:

```text
kind
source_state_root
target_state_root
complete source terminal-obligation table
complete target terminal-obligation table
```

Terminal rows share the 4,096-row explicit-value ceiling with balances,
supplies, named-custody rows, liabilities, and reserves. Admission checks the
combined count before state validation, copying, or hashing. The
terminal-specific boundary evidence uses states whose 4,096 rows are all
terminal obligations and rejects 4,097 before a hostile first row is examined.

## Adversarial closure

Mallory is a migration proposer who attempts to remove Alice's open claim,
change its claimant or asset, reduce its amount, or mark it drained or
tombstoned. The deterministic core derives the root from both complete tables
and rejects any source-to-target inequality. The commit port observes the
rejection before invoking the receipt verifier, so no proof callback can convert
the invalid candidate into initialization authority.

This Pokayoke is a guarded-transition defense. It blocks migration-time table
mutation. It supplies no evidence that Alice controls a key, that the claim is
funded, or that a mounted terminal command can pay it.

## Test obligation

```text
Reach:     execute genesis or migration admission with disclosed states
Infect:    substitute the public root or mutate one table coordinate
Propagate: derive exact-table equality and the canonical continuity root
Reveal:    reject with zero receipt-verifier calls and no publication
```

Named mutants remove predecessor equality, omit one row field from equality or
hashing, accept a changed status, omit the combined row preflight, or trust the
caller-supplied root. Tests use AAA, direct decision tables for every field and
status, BVA at 4,096/4,097, and a shared Python/Rust canonical vector.

## Nonclaims

- No terminal-obligation validity, funding, claimant-key, or payable-path proof.
- No source-head finality or complete predecessor-object classification proof.
- No permission to create, drain, rewrite, or tombstone obligations in migration.
- No compiled changed Rust targets or real RISC0 receipt for this source.
- No completed independent-review result for this slice; three built-in max
  review attempts stalled without returning a report.
- No mount, writer rotation, production authority, or whole-value safety claim.
