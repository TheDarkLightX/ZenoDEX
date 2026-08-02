# FCIS M6 E08 public finite-state schema

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

E08 is a public bounded model of commit, retry, quiescence, and authority
switch words. Commands A and B share the bounded sender/nonce nullifier and
compete for one predecessor head. A successful publication atomically adds
one commit ID and one nullifier while advancing the head. Exact retries are
stutters. Rejected lifecycle actions are stutters.

The explored action manifest is:

```text
commit_a
commit_b
retry_a
retry_b
quiesce
authority_switch
```

The model explores every word through depth 6 and checks:

- unique commit IDs;
- unique nullifiers;
- head/publication cardinality equality;
- head/nullifier cardinality equality;
- active/quiesced phase epoch shape;
- switched phase epoch shape.

Quiescence is a monotone barrier. Authority switch is accepted only from
quiescence and advances the epoch. Value transitions are rejected after the
barrier. The model also kills duplicate-nullifier, post-quiescence commit,
authority-switch skip, retry-head-increment, and split-publication mutants.

## Boundary

The explorer is a finite semantic model. It does not prove the E05 SQLite
transaction, production concurrent linearizability, real migration authority,
TLA/TLC execution, runtime no-bypass reachability, accounting, backing, zUSD
safety, or value movement.
