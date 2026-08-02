# FCIS M6 E05 expected-root atomic CAS schema

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

E05 is the transaction boundary between the verifier-owned E04 retry
classifier and a datastore adapter. A request contains:

```text
verified E04 attempt
verified E04 predecessor state
verified E04 successor state
verified fresh-reopen receipt bound to the predecessor
```

The adapter executes this sequence:

```text
BEGIN IMMEDIATE
  E04 classify(predecessor, receipt, CONFIRMED)
  read complete E05 predecessor layout
  compare current state/snapshot/authority/profile/sequence roots
  SQL CAS on every expected head field
  insert complete publication row
  insert nullifier row
  insert all effect rows
  reopen all staged rows and compare exact successor layout
COMMIT
```

The first datastore statement in `publish` is `BEGIN IMMEDIATE`. A caller
preflight read is not used to authorize an unguarded write. The SQL `UPDATE`
contains the current state root, snapshot root, authority epoch/root,
deployment and verifier profiles, next sequence, and complete publication-set
root in its `WHERE` clause. A zero-row update rejects the operation.

## Durable tables

`e05_head` stores the singleton current head. `e05_publications` stores the
complete E04 attempt projection and its canonical attempt bytes. Its unique
constraints cover sequence, attempt root, commit ID, nullifier root, and the
complete fingerprint. `e05_nullifiers` retains the commit/fingerprint
projection. `e05_effects` retains every derived effect with a primary key on
effect ID and a unique `(commit_id, ordinal)` pair.

The reopen path checks:

- exact canonical attempt bytes and nested request/commit/effect fields;
- contiguous publication sequence and successor state root;
- exact nullifier projection equality;
- exact effect projection equality;
- publication-set root recomputation;
- head fields and row cardinalities.

Any failed check returns a typed rejection or raises the research storage
error. Transactional failures roll back the head and all identity/effect
rows.

## Authority boundary

The E04 attempt, state, and reopen receipt are verifier-owned model values.
Their private construction registries are provenance guards for this research
slice. The SQLite adapter does not establish cryptographic authentication or
an external datastore's receipt freshness. Production authentication,
canonical reopen, concurrent linearizability under deployment settings,
filesystem durability, crash recovery, runtime reachability, migration
authority, accounting, backing, zUSD safety, and value movement remain open.
