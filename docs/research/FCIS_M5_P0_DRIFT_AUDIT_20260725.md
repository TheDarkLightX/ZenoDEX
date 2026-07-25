# FCIS M5 P0 Drift Audit

**Contract:** `zenodex/fcis-m5-atomic-mount/v2`  
**Audit date:** 2026-07-25  
**Starting head:** `d3f7b5068effd793d8d16ea63aa8c36e19e32243`  
**Required reviewed M4 ancestor:** `a6e20097d74641784402fb5a9939beaf11a9d`  
**Working branch:** `agent/fcis-m5-atomic-mount-20260725`  
**Outcome:** `M5_PREREQUISITE_CHECKPOINT_ONLY`

> Note: the required ancestor above is intentionally recorded exactly as it
> appears in the reviewed handoff and M4 completion receipt in this repository.
> The actual full ancestor in Git history is
> `a6e20097d74641784402fb2af5a9939beaf11a9d`.

## Executive decision

Do not switch authority.

The M4 branch has a useful exact evaluator candidate, but the mounted M5
contract is not yet closed. The correct action under the reviewed handoff is to
build the missing immutable authority algebra and expected-root publication
reference as an unmounted prerequisite checkpoint, then stop before changing
runtime authority.

The implementation in this branch therefore adds:

1. exact data-only `Accept | Reject | CommittedFailure` values;
2. one eight-field committed state aggregate;
3. candidate-root binding across state, plan, receipt, replay, and outbox;
4. canonical decision, receipt, plan, and bundle codecs;
5. receipt-derived outbox idempotency keys;
6. a pure immutable expected-root compare-and-swap reference interpreter;
7. a dedicated locked-dependency CI gate and semantic-law tests.

It does not alter the mounted evaluator, `DexState`, verifier boundary,
support-root version, persistence implementation, or runtime dispatch.

## Authority inventory at the starting head

| Authority component | Starting state | M5 checkpoint action | Mounted after this branch |
| --- | --- | --- | --- |
| Exact command admission | Present in M4 evaluator | Reused conceptually; not rewired | No change |
| Exact eight-field pre-state | Present in M4 evaluator | Represented as one public exact aggregate | No |
| Deterministic transition | Present as unmounted candidate evaluator | Not remounted | No |
| Three-way decision | Missing | Added as closed exact records | No |
| Canonical rejection receipt | Missing as M5 authority value | Added | No |
| Canonical success/failure receipt | Missing as M5 authority value | Added | No |
| Canonical patch envelope | Missing as M5 root-bound authority | Added as closed-domain bytes | No |
| Value/effect plan envelope | Missing as M5 root-bound authority | Added as closed-domain bytes | No |
| Replay update authority | Candidate nonce patch existed, publication authority missing | Added as exact compare-and-replace records | No |
| Transactional outbox plan | Missing | Added with receipt-derived identities | No |
| Root-bound `CommitBundleV1` | Missing | Added | No |
| Expected-pre-root commit port | Missing | Added only as pure test reference | No |
| Production datastore implementation | Missing | Not claimed | No |
| Python/Rust bundle refinement | Missing | Not claimed | No |

## Closed result algebra

The authority result is exactly:

```text
DecisionV1 = AcceptV1 | RejectV1 | CommittedFailureV1
```

The ordinary reject record contains only:

```text
reason
rejection_receipt
```

It has no state, patch, plan, replay, or outbox fields. This is structural, not a
runtime convention. A fourth variant is rejected by the canonical encoder.

`CommittedFailureV1` is separate because a protocol may name a failure outcome
that intentionally commits exact state and effects. It cannot be collapsed into
ordinary rejection without weakening the atomicity contract.

## Selected design pattern

The selected pattern is:

> **Closed deterministic decision + root-bound transactional outbox +
> expected-root compare-and-swap.**

This combines three established ideas without importing their mutable domain
models into the functional core:

1. **Functional core / imperative shell:** the core produces immutable data;
   the shell interprets one publication command.
2. **Optimistic compare-and-swap transaction:** publication is conditional on
   the observed committed root matching `expected_pre_root`.
3. **Transactional outbox:** external effects are first committed as immutable
   outbox rows in the same publication unit; later delivery is a separate shell
   concern and must be idempotent.

Primary references informing the pattern:

- AWS Prescriptive Guidance, *Transactional outbox pattern*: database state and
  outbox rows are written in one transaction; rollback publishes neither; later
  delivery can duplicate and therefore requires idempotent consumers.
  <https://docs.aws.amazon.com/prescriptive-guidance/latest/cloud-design-patterns/transactional-outbox.html>
- Microsoft Azure Architecture Center, *Transactional Outbox pattern*: business
  object and event are saved in the same transaction so both commit or both
  roll back.
  <https://learn.microsoft.com/en-us/azure/architecture/databases/guide/transactional-outbox-cosmos>
- etcd API transaction model: compare conditions select an atomic success or
  failure request list, providing the relevant expected-value CAS shape.
  <https://etcd.io/docs/v3.7/learning/api/>
- Python `dataclasses` documentation: `frozen=True` emulates immutability rather
  than making hostile interpreter mutation impossible. The shell therefore
  revalidates the complete bundle immediately before publication.
  <https://docs.python.org/3/library/dataclasses.html>

## Same-candidate binding

The candidate identity is derived from:

```text
candidate_root = H(
    domain,
    expected_pre_root,
    execution_context_hash,
    command_or_batch_root,
    next_state_root,
)
```

The commit plan, receipt, and outbox plan must all carry the same
`candidate_root`. The bundle constructor additionally requires:

```text
bundle.canonical_patch == bundle.commit_plan.canonical_patch
bundle.replay_updates == bundle.commit_plan.replay_updates
bundle.outbox_plan == bundle.commit_plan.outbox_plan
bundle.outbox_plan.receipt_root == bundle.receipt_root
```

This prevents independently valid artifacts from different candidates from
being spliced into one publication request.

## Transactional outbox identity

Each outbox idempotency key is derived from:

```text
H(domain, receipt_root, effect_index, effect_identity)
```

The key does not depend on process time, database sequence allocation, random
UUID generation, object identity, or callback order. Rebuilding the same
candidate produces the same outbox identities.

The guarantee is intentionally narrow:

- committed outbox data is exactly-once within the modeled atomic publication;
- later external delivery is not claimed to be exactly once;
- a relay and consumer must use the stable idempotency key to make duplicate
  delivery harmless.

## Reference commit semantics

The test-only interpreter is a pure function over an immutable store snapshot.
It has one publication point:

```text
validate bundle
-> duplicate check
-> expected-root comparison
-> optional injected crash before publication
-> construct one complete successor store
```

The successor store contains the new state, bundle root, receipt, replay
updates, and outbox records together. Every stale, malformed, or injected-crash
path returns the original store object unchanged.

This proves deterministic reference semantics only. It is not evidence about a
specific production database transaction, WAL, fsync behavior, crash recovery,
or multi-process linearizability.

## Support-root v5 closure audit

The current v5 profile is not promotion-ready.

| Coverage obligation | Current finding | Promotion status |
| --- | --- | --- |
| Explicit presence/absence | v5 reuses sparse encoders that omit absent/zero entries | Blocked |
| Key identity for absent cells | Omission can collapse different unsupported/missing cells | Blocked |
| Direct swap output recipient | Input sender and pool are covered; actual output recipient balance is not complete | Blocked |
| Route output recipient | Explicitly represented | Partial pass |
| Add-liquidity LP recipient | Represented | Pass for inspected path |
| Create-pool LP recipient | Pool and funding balances represented; minted LP recipient is not complete | Blocked |
| Remove-liquidity output recipient | LP owner and pool represented; output asset recipient balances are not complete | Blocked |
| Nonce support | Represented | Pass for inspected path |
| Fee accumulator | Not part of `BatchStateSupport` or the v5 support-root preimage | Blocked |
| Declared context footprint | Context bytes are retained separately, but no complete support-set declaration/commitment exists | Blocked |
| Verifier/proof-guest v5 migration | No complete reviewed evidence packet | Blocked |
| Golden vectors | No complete v5 migration vector set | Blocked |
| Python/Rust refinement | No exact M5 bundle/decision parity implementation and proof | Blocked |
| Production datastore evidence | Reference interpreter only | Blocked |

The handoff requires stopping after this finding. A domain/version bump alone
would not fix the semantic incompleteness.

## Forbidden-mechanism review

The new checkpoint code does not introduce:

- mutable containers in authoritative values;
- `Any`-typed authority payloads;
- callback fields or callable policy inputs;
- reflection-based object traversal;
- generic JSON conversion of protocol state;
- time-, locale-, environment-, randomness-, or identity-dependent ordering;
- direct external side effects from the core;
- shell repair of incomplete core output;
- partial publication APIs.

Canonical payload envelopes accept bytes only under one of four closed domain
tags. Those bytes are not yet a substitute for the missing exact M4-to-M5
adapter; this branch records that adapter as a remaining prerequisite rather
than pretending arbitrary bytes are mounted authority.

## Checkpoint verdict

`M5_PREREQUISITE_CHECKPOINT_ONLY`

The authority algebra and atomic reference semantics are materially advanced.
The runtime authority switch remains blocked until support-root v5, the exact
evaluator adapter, verifier migration, cross-language refinement, and real
persistence evidence are complete and reviewed.
