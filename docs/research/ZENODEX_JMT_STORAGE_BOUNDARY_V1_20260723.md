# ZenoDEX JMT Storage Boundary V1

Status: experimental, proof-neutral, shadow-only  
Date: 2026-07-23  
Scope: `zk/zrpf_protocol/protocol`

## 1. Decision

ZenoDEX already has authenticated state-transition machinery, but it does not
yet have a complete Jellyfish Merkle Tree storage engine.

The existing protocol contains:

- a fixed-depth 256-bit binary sparse-Merkle cell transition witness;
- exact pre-root and post-root derivation from one key, value hash, and sibling
  path;
- a bounded batch that chains 1..=64 cell transitions in canonical key order.

That is JMT-adjacent, but it is not a full JMT implementation. A complete JMT
also defines versioned node identities, a concrete node codec, a tree reader,
an atomic node-write batch, stale-node indices, pruning behavior, and
membership/non-membership proof APIs.

This change adds the missing **immutable storage-plan boundary** without
changing the existing root relation or promoting a storage backend.

## 2. Why this is an extension rather than a replacement

The current sparse-Merkle witness is already a useful proof relation:

```text
cell key
+ pre value hash
+ post value hash
+ 256 sibling commitments
-> exact pre root
+ exact post root
```

The bounded batch adds:

```text
strictly increasing keys
+ unique write identities
+ adjacent root continuity
-> one batch pre root
+ one batch post root
```

Replacing it with an off-the-shelf JMT root would change consensus-visible hash
semantics. The existing internal hash binds the root-indexed binary depth. A
typical JMT compresses four binary levels into a nibble-addressed internal node
and may collapse empty or single-leaf subtrees. Those structures can coexist,
but their roots are not assumed to be byte-identical.

V1 therefore keeps the existing ZenoDEX binary root authoritative inside the
proof-neutral transition and derives **nibble-boundary subtree commitments**
from it.

## 3. What this change adds

`ValidatedJmtStorageUpdatePlanV1` binds:

```text
plan version
storage profile
tree identity
base tree version
strict successor target version
base root
post root
validated sparse-Merkle batch
exact transition-derived new boundary-node records
canonical hash-bound stale-node indices
```

The plan has a bounded canonical Postcard codec and a domain-separated
commitment.

It deliberately carries no:

- proof receipt authority;
- economic validity;
- settlement authority;
- database authority;
- ledger admission;
- crash-atomic commit;
- pruning authorization;
- concrete JMT node payload;
- membership or non-membership proof.

Those remain separate obligations.

## 4. Nibble-boundary derivation

A 256-bit key has 64 nibbles. For each validated cell witness, V1 derives the
subtree commitment at:

```text
depth 0
depth 4
depth 8
...
depth 252
depth 256 leaf
```

The derivation uses the existing ZenoDEX binary leaf and internal hash
functions. It does not introduce another hash algorithm.

For a sequential batch:

- the first pre-commitment observed at a shared path is the base-state
  boundary commitment;
- the final post-commitment observed at a shared path is the target-state
  boundary commitment;
- the target node list is sorted by one explicit canonical nibble-path order;
- every supplied new-node record must exactly equal the derived list.

This prevents a caller from attaching an arbitrary storage node batch to a
valid transition.

## 5. Canonical paths

`JmtNibblePathV1` stores:

```text
nibble_count: 0..=64
packed_nibbles: 32 bytes
```

The high nibble is used first. Every unused low nibble and trailing byte must be
zero.

The canonical order is:

```text
packed nibble bytes
then nibble count
```

The nibble-count tie-break distinguishes a prefix from a longer path whose
remaining nibbles are zero:

```text
root < 0 < 00 < 000 < ...
```

This order is protocol data. It does not depend on `HashMap`, database row
order, insertion history, or worker completion timing.

## 6. Version discipline

V1 requires:

```text
target_version = base_version + 1
```

with checked arithmetic.

All new node keys use `target_version`. A stale node may reference only a node
version at or below `base_version`, and its `stale_since_version` must equal
`target_version`.

Tree version is an explicit protocol value. A future shell must not infer it
from wall-clock time or silently couple it to a block height without a
separately specified invariant.

## 7. Stale-node safety

A stale index contains:

```text
stale_since_version
historical node key
expected node hash
```

The path must have been touched by the transition, and the expected hash must
equal the first pre-state nibble-boundary commitment derived for that path.

This closes two easy failure modes:

- pruning a path unrelated to the transition;
- pruning a touched path whose content does not match the base transition.

V1 cannot prove that the supplied historical `NodeKey` was the uniquely live
physical node for that path. That fact belongs to the concrete tree reader and
its base-version lookup proof. Until that adapter exists, stale indices are
proof-neutral commit data, not pruning authority.

## 8. FCIS boundary

The intended flow is:

```text
pure transition core
    validated sparse-Merkle batch
        |
        v
pure JMT storage-plan derivation
    new boundary commitments
    checked stale candidates
    canonical plan hash
        |
        v
imperative storage adapter
    resolves concrete live node keys
    verifies concrete node payloads
    produces database write batch
        |
        v
atomic shell commit
    expected pre-root compare-and-swap
    semantic state updates
    concrete JMT node writes
    stale-node indices
    target root/version
    receipt
    replay/nullifier record
    transactional outbox
```

A failure before the atomic commit exposes no partial authoritative state.

## 9. Required shell invariant

A production adapter must eventually establish:

```text
plan_authenticated_commit(S_v, P)
    = (S_v+1, root_v+1, node_batch, stale_batch)

full_rebuild_root(apply(logical_state_v, writes(P)))
    = root_v+1

incremental_adapter_root(node_batch, root_v)
    = root_v+1
```

and the database transaction must atomically bind all of:

```text
tree_id
base_version
base_root
target_version
post_root
plan_hash
node payload batch
stale-index batch
transition receipt
replay identity
outbox records
```

## 10. Why no external JMT crate is promoted here

The maintained `jmt` crate is a serious implementation candidate, but adding it
directly to an authority path would also add:

- a new node hash and serialization contract;
- a new dependency graph in the trusted path;
- storage-reader assumptions;
- pruning assumptions;
- migration and rollback obligations;
- a root-format change.

Those decisions require an explicit dependency review, benchmark, dual-root
migration, and full-rebuild differential. This PR establishes the stable value
boundary first.

A later adapter may use the maintained Apache-2.0 Penumbra JMT implementation,
an independently audited internal implementation, or another authenticated
map. The adapter must refine this protocol contract rather than redefine it.

## 11. Promotion gates

No JMT-backed authority promotion should occur until all of the following hold:

1. Canonical state-key and value codecs are specified per ZenoDEX lane.
2. Full rebuild and incremental update roots agree for generated and adversarial
   states.
3. Membership and non-membership proofs have independent verification vectors.
4. Concrete node payloads recompute every supplied boundary commitment.
5. The live base-version node identity for each stale path is authenticated.
6. Node writes, stale indices, root/version, receipt, replay data, and outbox
   records commit atomically.
7. Crash injection proves no partial commit or root/database divergence.
8. Historical pruning respects challenge and proof-generation windows.
9. Python/reference and Rust implementations agree on keys, values, roots,
   rejection precedence, and canonical bytes.
10. A dual-root shadow period demonstrates migration and rollback.

## 12. Recommended first live experiment

Use a non-authoritative tree for:

```text
spot balances
replay nonces
```

These maps have simple keys and scalar values, frequent sparse updates, and
strong existing Python/Rust differential coverage.

During the shadow period retain both:

```text
legacy complete-snapshot state_root_v5
JMT candidate root/version
```

The candidate must not replace `state_root_v5` until the promotion gates close.

## 13. Test obligations in this PR

The protocol tests cover:

- exact derivation of 65 nibble boundaries for one key;
- canonical union and final-writer behavior for shared paths;
- nibble-path canonicalization;
- strict successor versions;
- tree and root binding;
- exact equality of supplied and transition-derived new nodes;
- stale-path uniqueness, age, touched-path, and hash checks;
- bounded vector admission before deeper validation;
- exact canonical Postcard round-trip;
- trailing, non-minimal, empty, and oversized input rejection;
- domain-separated plan commitment and tree-identity binding.

## 14. Nonclaims

This change does not claim that:

- ZenoDEX already used a full JMT;
- these records are Diem/Aptos/Penumbra wire-compatible nodes;
- the current ZenoDEX sparse root equals a standard JMT root;
- a validated plan grants database or ledger authority;
- stale metadata alone authorizes pruning;
- the node batch proves data availability;
- a Merkle root proves economic validity;
- a Merkle proof proves consensus finality.

## 15. Follow-up PR sequence

1. Add project-lane state-key and value codec specifications.
2. Build an in-memory concrete node-payload adapter behind a shadow-only feature.
3. Add full-rebuild versus incremental-root property tests.
4. Add membership and non-membership proof vectors.
5. Add a durable tree reader/writer with transactional crash tests.
6. Add a dual-root state commitment and migration receipt.
7. Promote one lane only after the shadow and rollback gates close.

## References

- Diem, “Jellyfish Merkle Tree”:
  https://developers.diem.com/docs/technical-papers/jellyfish-merkle-tree-paper/
- Diem Jellyfish Merkle implementation overview:
  https://diem.github.io/diem/diem_jellyfish_merkle/
- Penumbra `jmt` crate:
  https://docs.rs/jmt/latest/jmt/
- ZenoDEX FCIS values-as-boundaries tutorial:
  https://thedarklightx.github.io/Formal_Methods_Philosophy/tutorials/functional-core-imperative-shell-values-as-boundaries/
