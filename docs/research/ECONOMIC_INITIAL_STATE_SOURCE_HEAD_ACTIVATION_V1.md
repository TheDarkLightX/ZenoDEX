# Economic Initial-State Source-Head Activation V1

Status: implemented in-memory reference candidate, unmounted.

This note defines the authority boundary between a valid migration proof and
the publisher head that the migration is allowed to replace. It grants no
production, consensus, durable-publication, or value-moving authority.

## ShapeForge contract

```text
Phi = <M,S,A,T,V,O,G,Obs,K,E,Gap,N,Delta>

M     = zenodex.global-economic-initialization.v1
S     = publisher-current source-head activation for proved migration
A     = migration publication authority axis
T     = remove direct publisher construction around caller-selected predecessor
V     = expected head, expected profile, publisher-owned state and profile,
        migration admission, retained verifier, publisher binding token
O     = activate_migration
G     = constructor accepts GENESIS only;
        admission predecessor = exact publisher-owned source state;
        expected head/profile = current head/profile before and after verification;
        retained verifier and publisher token remain unchanged;
        accepted target profile/state/certificate replace the tuple under one lock
Obs   = typed exception with unchanged publisher tuple, or exact activated tuple
K     = expected source binding before receipt verification, then receipt,
        then lock-protected freshness recheck and activation
E     = deterministic Python mutation killers and state/no-effect assertions
Gap   = durable transactionality, consensus finality, governed migration-release
        selection, real receipt replay, writer fencing and deployment mounting
N     = a fresh publisher could previously be constructed around any internally
        consistent migration predecessor
Delta = migration becomes a transition of an existing publisher-owned head
```

## Selected invariant

Let `P` be the exact state owned by the publisher when activation starts, `H(P)`
its canonical global state root, and `A.predecessor` the state disclosed by the
migration admission.

```text
construct_publisher(A) succeeds -> A.kind = GENESIS

activate_migration(expected_head, expected_profile, A) succeeds ->
    A.kind = MIGRATION
    canonical(A.predecessor) = canonical(P)
    expected_head = H(P)
    expected_profile = P.profile_root
    current_head_after_receipt = expected_head
    current_profile_after_receipt = expected_profile
    retained_verifier_after_receipt = retained_verifier_before_receipt
    publisher_token_after_receipt = publisher_token_before_receipt
```

On acceptance, the in-memory publisher changes its profile, state,
initialization-certificate root, and epoch-witness binding token in one locked
critical section. Rejection leaves that tuple unchanged unless another
authorized operation won the race first.

## Why the existing journal is sufficient for this slice

The migration journal already commits the source profile root, source state
root, source writer epoch, source height, chain, and deployment. The guest also
recomputes the complete disclosed predecessor state root. Activation compares
that exact disclosed state with the publisher-owned current state. A second
source-head field would duplicate the existing source-state commitment without
adding authority.

The source and toolchain manifest roots retain their provenance meanings. They
are never interpreted as ledger-head or finality evidence.

## Adversarial scenario

Mallory creates a migration admission whose predecessor has valid types,
canonical encoding, correct coordinates, and a self-consistent source root.
Mallory changes a committed field such as the history root and asks a new
publisher to accept the target.

The constructor rejects every migration admission before receipt verification.
An existing publisher snapshots its own source state and rejects Mallory's
predecessor because the two canonical states differ. Rebinding the migration
certificate to Mallory's source root cannot change the publisher-owned head.

## RIPR evidence obligation

```text
Reach:     submit migration through construction and locked activation
Infect:    substitute a self-consistent foreign predecessor or stale expectation
Propagate: preserve valid certificate and receipt-shaped inputs
Reveal:    reject before migration receipt verification and retain source tuple
```

Named mutation killers cover removal of the genesis-only constructor rule,
removal of exact predecessor equality, removal of either expected head/profile
check, and removal of post-verification freshness checks.

## Claim boundary

This slice establishes publisher-current source-head authority in the
in-memory conformance model. It closes the direct-construction counterexample
and provides the compare-and-swap shape required by a durable implementation.

It does not establish:

- objective consensus or validator finality for the source head;
- durable atomic migration, crash recovery, or writer fencing;
- selection of the target profile and migration release from committed
  governance state;
- real RISC0 proof construction or independent receipt replay;
- migration totality, history continuity, private lane-object continuity,
  source authorization, terminal validity, or shared-asset coexistence;
- mounting, production authority, settlement authority, or value-moving
  authority.
