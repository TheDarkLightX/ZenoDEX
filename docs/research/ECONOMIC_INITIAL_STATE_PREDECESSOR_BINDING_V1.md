# Economic Initial-State Predecessor Binding V1

Status: implemented candidate, unmounted, unproved by a real receipt.

This note fixes the semantic boundary for migration predecessor disclosure. It
does not promote production authority or whole-value-movement safety.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = exact predecessor-state binding for migration initialization
A     = source-state evidence axis only
T     = eliminate caller-declared, unrecomputed source_state_root values
V     = kind, target state, optional predecessor state, source root,
        source profile, writer epoch, height, chain and deployment
O     = validate_economic_initial_state_predecessor_binding_v1
G     = GENESIS implies predecessor absent;
        MIGRATION implies predecessor present and exact root/metadata binding
Obs   = typed accept/reject before receipt verification; public journal unchanged
K     = kind first, then fixed predecessor coordinates; no winner relation
E     = Python publisher tests, Rust ABI tests, RISC0 shared-contract tests,
        canonical state-root implementation and later real receipt replay
Gap   = source-head authority, migration totality and all continuity relations
N     = a migration statement with an arbitrary source root previously passed
Delta = the source state becomes an explicit proof witness checked by the same
        deterministic Rust core imported by the guest
```

## Selected invariant

For genesis:

```text
kind = GENESIS
  -> predecessor_state = None
  -> source_profile_root = source_state_root = ZERO_ROOT
  -> source_writer_epoch = source_height = 0
```

For migration:

```text
kind = MIGRATION
  -> predecessor_state = Some(P)
  -> state_root(P) = statement.source_state_root
  -> P.profile_root = statement.source_profile_root
  -> P.writer_epoch = statement.source_writer_epoch
  -> P.height = statement.source_height
  -> P.chain_id = target.chain_id
  -> P.deployment_root = target.deployment_root
```

The existing adjacent-lineage rule also requires target writer epoch and height
to be exactly one greater than the committed predecessor coordinates.

## Invariant ownership

The full predecessor state is disclosed so the guest can recompute its global
state root. This commits its Oracle occurrences, replay table, history root,
outbox rows, terminal obligations, lane roots and explicit accounting rows.
Commitment alone establishes no relation between source and target contents.

Separate certificates retain ownership of:

- private lane-object migration classification and totality;
- replay/nullifier continuity;
- terminal-obligation continuity;
- outbox continuity and acknowledgment state;
- history continuity;
- objective finality and authority of the predecessor head;
- source authorization behind target atom classifications;
- migration registry selection and release compatibility.

`ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1.md` now requires migration to
activate against the exact current state of an existing in-memory publisher.
That reference gate closes direct construction around a caller-selected
predecessor. Objective consensus finality and durable activation remain
separate obligations.

The public journal fields for those roots remain structural declarations until
their dedicated deterministic checkers and proof statements are implemented.

## Rejected shapes

1. Keeping only a declared predecessor root permits an arbitrary-root false
   pass and provides no witness from which the guest can recompute the root.
2. Folding Oracle, replay, history, outbox and lane objects into the existing
   target atom manifest blurs invariant ownership and would falsely imply
   continuity from target-row coverage.
3. Treating a full predecessor disclosure as source-head finality confuses
   content commitment with objective publication authority.

## Test obligation

```text
Reach:     execute migration admission through Python, Rust and guest contracts
Infect:    remove the predecessor or mutate content or one committed coordinate
Propagate: recompute or retain the source root according to the mutant
Reveal:    reject before receipt verification or publication
```

Named mutants include removal of predecessor presence checks, removal of source
root recomputation, and omission of chain, deployment, profile, writer-epoch or
height binding. The 4,097-explicit-row predecessor case must reject at the same
prevalidation ceiling as the target state.

## Version and release consequence

The initialization guest remains an unmounted V1 candidate. Adding the required
predecessor witness changes its canonical input bytes and therefore requires a
new ELF, measured image ID, release record, proof run and replay evidence before
any release-backed claim. Existing placeholder or prior candidate artifacts
carry no authority.

## Nonclaims

- No real ELF, measured image, Succinct proof or independent receipt replay.
- No proof that the disclosed predecessor is the finalized ledger head.
- No replay, history, terminal, outbox or private lane-object continuity proof.
- No migration totality, release-selection or coexistence theorem.
- No mount, writer rotation, production authority or value-moving authority.
