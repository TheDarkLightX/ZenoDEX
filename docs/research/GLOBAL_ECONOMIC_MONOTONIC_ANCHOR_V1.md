# Global Economic Monotonic Anchor V1

Status: `IMPLEMENTED_TESTED_SHADOW_PORT`

Production authority: `NONE`

## Outcome

This slice defines a canonical checkpoint and a release-bound shadow port for
an independently durable, authenticated, monotonic source. It adds an optional
publisher-open profile that rejects restored authority or epoch history before
another economic commit.

The external observation `E` and validated local durable tip `L` have one
accepted normal relation and one accepted recovery relation:

```text
E = L                 -> normal publication may proceed
L = EpochSuccessor(E) -> exact already-committed epoch retry may repair E
otherwise             -> reject before another commit
```

The recovery profile cannot publish a second transition. The supplied source
must equal the anchored predecessor, receipt verification must reproduce the
already-stored epoch, and the journal must return `ALREADY_COMMITTED` before
the external compare-and-set advances.

## Canonical checkpoint

`GlobalEconomicMonotonicAnchorV1` commits:

- external anchor namespace, sequence, and previous-anchor root;
- authority root and generation;
- activation, chain, deployment, epoch-store, profile, and writer epoch;
- publication ID and sequence, height, state root, commit ID, and certificate
  root; and
- Global Settlement ABI version and a closed schema tag.

All counters are exact unsigned 64-bit integers. Boolean aliases, floats,
unknown or duplicate fields, noncanonical JSON, malformed roots, zero roots in
successor positions, publication skips, anchor skips, wrong predecessor roots,
and changed stable bindings reject. Ordinary epoch advancement requires:

```text
anchor_sequence'      = anchor_sequence + 1
previous_anchor_root' = anchor_root
publication_sequence' = publication_sequence + 1
height'               = height + 1
authority'            = authority
activation/profile/writer/deployment/store' = unchanged
```

## Port and authority boundary

`BoundGlobalEconomicMonotonicAnchorBackendV1` retains the exact callables from
one measured, content-derived `SHADOW` backend release. The backend protocol is:

```text
read_current_anchor(namespace_root) -> exact canonical bytes
compare_and_set_anchor(namespace_root, expected_root, successor_bytes)
  -> exact bool
```

Successful CAS is independently followed by a current read. The read may equal
the submitted successor or a later same-authority epoch tip when another valid
writer linearizes after this CAS. The publisher adopts a later observation only
when its complete authority and publication coordinates equal the validated
local durable heads. An unchanged predecessor after a true acknowledgment,
truthy integer, malformed bytes, wrong namespace, chain or deployment, backend
exception, or stale CAS fails closed. The backend release shape records that
authenticated source, current monotonic read, and linearizable CAS are
required. Those labels are requirements, not evidence that a supplied Python
object satisfies them.

A local file in the same filesystem, snapshot, backup, service account, or
rollback domain as the economic journals cannot satisfy this port's external
assumption. The older `M6MigrationExternalHeadAnchorV1` is such a local file and
does not provide coordinated-rollback resistance.

## Commit and crash protocol

For the optional anchored publisher profile:

1. read and decode the current external checkpoint;
2. validate authority, epoch tip, and direct predecessor in one attached-
   SQLite snapshot;
3. classify the local relation as exact, one-epoch recovery, or reject;
4. recheck the same relation before receipt verification;
5. verify and atomically commit the complete epoch through the existing
   authority-fenced SQLite transaction;
6. derive the external successor from the committed local head; and
7. compare-and-set the external source, then reread it before returning
   success.

If step 5 commits but its journal acknowledgment is lost, the publisher reads
the durable authority, tip, and direct predecessor. It arms recovery only when
those heads prove the exact one-epoch relation from the supplied source. If
steps 6 or 7 are unavailable or conflicting, the caller receives
`GlobalEconomicAnchorAdvanceIndeterminateV1`. `COMMITTED` and
`ALREADY_COMMITTED` outcomes arm recovery before any fallible projection. The
in-process publisher therefore retains the same one-epoch recovery state after
either result. Restart also recognizes only that direct predecessor relation.
Exact retry performs no second local insertion and advances the external
checkpoint. Any other command, source, skip, authority change, rollback, or
divergence rejects.

## Pattern and preflight record

- Invariant owner: the deterministic anchor value owns coordinate closure and
  adjacent epoch rules. The integration port owns external acquisition and CAS.
  The epoch journal remains the sole local publication linearization point.
- Authority: the anchor value grants none. The bound backend is shadow-only and
  caller-instantiated in current tests. Production selection is absent.
- Construction: canonical frozen values own exact primitive fields. No caller
  mapping or mutable nested object enters a checkpoint.
- Aliasing: bytes are decoded into new immutable values. Backend objects remain
  part of the untrusted shadow shell and can change behavior.
- Rejection: mismatch before commit changes no local history. Failure after the
  SQLite commit is an explicit indeterminate committed outcome, followed only
  by exact-retry recovery.
- Commit set: the existing SQLite transaction atomically owns epoch state,
  receipt, replay, outbox-containing bundle, and local head. External CAS is a
  second linearization point with a typed one-step recovery protocol.
- Migration: authority transition and migration activation are not admitted by
  this epoch-only successor rule.
- Rust, RISC0, Tau, and deployment enforcement: absent for this slice.

## Evidence

The focused portfolio includes:

- canonical roundtrip, exact-type and u64 BVA;
- stable-root mutation killers and skip/replay/previous-root negatives;
- wrong namespace, hostile return type, transport failure, stale CAS, and false
  CAS-acknowledgment tests;
- restored pre-revocation authority bytes rejected without mutation;
- sequence-zero epoch restore rejected without mutation;
- normal local commit followed by external CAS;
- backend outage after local commit followed by restart and exact retry; and
- stale external CAS followed by same-process exact retry, with one local row.
- lower-journal commit-before-ack followed by typed same-process exact retry;
- concurrent `ALREADY_COMMITTED` followed by a projection fault and exact
  retry; and
- a successful CAS whose confirmation read observes a later same-authority
  epoch, plus stable-binding and counter-delta mutation killers; and
- fail-closed rejection when that forward external tip lacks exact matching
  local durable authority and publication coordinates;
- positive adoption when a second valid writer advances both complete local and
  external histories before the first writer's confirmation read;
- same-process exact recovery arming after a post-commit process-control
  interruption while preserving the original exception; and
- original-error/no-effect behavior at all three tested pre-commit journal
  fault boundaries.

These are bounded Python tests. They do not prove the backend's external
currentness or the whole application.

## Nonclaims and next gate

- No concrete independent anchor service, Tau occurrence, quorum checkpoint,
  transparency log, TPM monotonic counter, HSM counter, or remote append-only
  service is implemented or authenticated here.
- No production release registry selects an anchor backend.
- No external service executable is measured, attested, independently
  replayed, or mounted.
- Genesis anchor initialization is outside this slice. A production design
  needs authenticated no-replace initialization and lost-ack recovery.
- Authority successor anchoring, governance authentication, migration
  activation, writer-epoch rotation, and old-writer retirement remain open.
- The existing unanchored `create` and `open` research APIs remain callable.
- External CAS and SQLite are not one atomic transaction. The implemented
  direct-successor recovery bounds one ordinary-epoch crash window; it does not
  solve arbitrary multi-store transactions.
- A malicious or stale backend can replay an old checkpoint. Production safety
  depends on an independently enforced currentness and monotonicity contract.
- Forward-observation adoption assumes all accepted external updates obey the
  same adjacent-CAS protocol and requires exact current local-head agreement.
  Arbitrary external forks and independently named stores remain rejected.
- If process-control recovery classification is itself unavailable, the current
  process receives the original exception and restart must reconstruct recovery
  from the durable one-step relation.
- No production readiness, settlement authority, finality, or whole-value-
  movement guarantee follows.

The next architectural gate is one authenticated authority-successor and
migration transaction that installs the new activation, profile, writer epoch,
external checkpoint, and old-writer retirement as one recoverable protocol.
