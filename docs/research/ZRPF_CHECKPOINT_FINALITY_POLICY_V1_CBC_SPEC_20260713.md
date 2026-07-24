# ZRPF Checkpoint Finality Policy V1 CBC Specification

Status: implemented proof-neutral protocol primitive; external finality and
production authority remain unestablished.

## Scope

`checkpoint_finality_v1` gives the bounded ordinary Spot settlement path one
canonical way to bind its exact proof journal and post-state root to one
externally finalized checkpoint projection.

The trusted progression is:

```text
external checkpoint and finality evidence
  -> protocol-specific governed verifier
  -> authenticated finalized-checkpoint facts
  -> ExpectedFinalizedCheckpointBindingV1
  -> exact CheckpointFinalityCertificateV1 comparison
  -> local policy-satisfaction result
  -> no settlement or production authority
```

The protocol-specific verifier remains outside this crate. Existing candidate
adapters include:

- `zeno_ledger_live_quorum_v0`, which verifies BLS checkpoint-signature quorum;
- `zeno_ledger_tau_export`, which produces an adapter-neutral Tau handoff and
  explicitly does not claim Tau acceptance.

The proof-neutral certificate and policy cannot replace either adapter.

## Certificate

`CheckpointFinalityCertificateV1` contains only fixed-width typed values and
two bounded integers:

| Field | Meaning |
| --- | --- |
| `certificate_version` | Exact schema version. |
| `application_id` | Application whose transition is checkpointed. |
| `chain_or_domain_id` | Application execution domain. |
| `epoch_id` | ZRPF epoch represented by the proof journal. |
| `proof_journal_hash` | Exact state-bound ZRPF admission journal committed by the checkpoint. |
| `post_state_root` | Exact post-state root committed by the checkpoint. |
| `checkpoint_height` | Height assigned by the external finality domain. |
| `checkpoint_hash` | Canonical finalized checkpoint identity. |
| `finality_network_id` | Hash identity of the external network/domain. |
| `finality_protocol_id` | Hash identity of the governed finality protocol and adapter version. |
| `external_finality_policy_hash` | External fork-choice/quorum/finality policy commitment. |
| `finality_verifier_set_root` | Exact verifier or signer-set commitment. |
| `finality_evidence_root` | Commitment to the protocol-specific authenticated evidence. |
| `finality_policy_root` | Root of the local ZRPF acceptance policy. |
| `certificate_root` | Domain-separated root of every preceding field. |

There is no `finalized`, `verified`, `ok`, `settlement_authority`, or
`production_authority` field. Caller-supplied verdicts cannot become authority.

## Policy

`CheckpointFinalityPolicyV1` binds:

```text
policy version
application ID
chain/domain ID
external finality network ID
finality protocol ID
external finality policy hash
finality verifier-set root
minimum checkpoint height
```

The domain-separated policy root covers every field. A certificate must commit
that exact root. Changing any acceptance parameter therefore changes both the
governed policy identity and the certificate expected by a consumer.

## Expected finalized-checkpoint binding

`ExpectedFinalizedCheckpointBindingV1` contains the per-checkpoint facts that
must come from a separately authenticated adapter:

```text
application ID
chain/domain ID
epoch ID
proof journal hash
post-state root
checkpoint height
checkpoint hash
finality network ID
finality protocol ID
external finality policy hash
finality verifier-set root
finality evidence root
```

The Rust type is deliberately a data value rather than an unforgeable
capability. A caller can construct it. The integration layer must keep the
protocol-specific authenticated result sealed and create this value only after
cryptographic quorum/finality verification. Supplying the same attacker-chosen
fields to both the certificate and expected binding establishes nothing about
external consensus. Carrying the complete scope prevents an authenticated
checkpoint from one application, domain, network, protocol, policy, or
verifier set from being relabeled under another governed local policy.

## Monotonic checkpoint cursor

The policy check also requires the last checkpoint height atomically accepted
for the exact governed scope. A new certificate must have a strictly greater
height. `None` is valid only for an empty admission cursor. Replaying the same
height or presenting a lower height rejects.

This cursor is a data input in the proof-neutral crate. Production integration
must obtain it from the same rollback-resistant transaction that commits the
new checkpoint, proof admission, replay indexes, and value state. A caller can
lie about the cursor when invoking this isolated checker, so successful local
checking alone remains non-authoritative.

## Exact codec and roots

The certificate uses exact Postcard encoding with a 512-byte input ceiling.
The decoder rejects:

- empty input;
- input over the ceiling;
- malformed Postcard;
- trailing bytes;
- noncanonical re-encoding;
- unknown JSON fields when the typed Serde boundary is used;
- a stale version;
- a certificate root inconsistent with the decoded fields.

Certificate-root domain:

```text
zenodex.zrpf.checkpoint_finality.certificate_root.v1
```

Policy-root domain:

```text
zenodex.zrpf.checkpoint_finality.policy_root.v1
```

Both preimages begin with a big-endian `u16` domain length. Integers are hashed
big-endian. All IDs and commitments use existing nonzero 32-byte ZRPF value
types.

## Fail-closed policy checks

The checker validates certificate self-consistency, then rejects independently
for:

- application or domain substitution;
- finality network or protocol substitution;
- external policy or verifier-set substitution;
- checkpoint height below the governed floor;
- local finality policy-root substitution;
- epoch, proof journal, post-state, height, checkpoint hash, or evidence-root
  mismatch against the authenticated expected binding.
- authenticated application, domain, network, protocol, external-policy, or
  verifier-set scope relabeling;
- checkpoint height that does not strictly advance the supplied admission
  cursor.

The checker returns `Result<(), CheckpointFinalityPolicyErrorV1>`. Success is a
local equality and policy result for the supplied objects. It is not an
authority-bearing certificate.

## Ordinary Spot integration seam

The bounded ordinary Spot production slice still needs an adapter that performs
this exact sequence in one authority path:

1. verify the governed finalized checkpoint, including signature quorum or Tau
   finality semantics;
2. derive the external policy, verifier-set, checkpoint, and evidence roots
   from authenticated bytes;
3. derive the last accepted height from the durable, scope-keyed checkpoint
   cursor;
4. bind the checkpoint `proof_journal_hash` to the exact receipt-authenticated
   ZRPF admission journal;
5. bind the checkpoint `post_state_root` to the exact state-bound settlement
   result;
6. run `check_checkpoint_finality_policy_satisfied_v1` with the durable prior
   height;
7. atomically persist the advanced checkpoint cursor, finality certificate,
   governed policy root, external
   evidence, proof admission, replay indexes, and value-state transition.

The current `SettlementAdmissionJournalV1` has no checkpoint-finality root.
Integration therefore requires a versioned admission envelope or atomic store
record that commits both `certificate_root` and `finality_policy_root`. This V1
module does not silently alter the existing settlement journal ABI.

## Evidence

Focused tests cover:

- independent recomputation of policy and certificate roots;
- exact codec round-trip;
- every truncated prefix, trailing bytes, and oversized input;
- unknown fields, stale version, and forged derived root;
- absence of caller verdict fields;
- root separation for every certificate and policy field;
- typed rejection for every policy and expected-checkpoint substitution;
- cross-scope authenticated-checkpoint relabeling rejection;
- empty-cursor acceptance, strict height advancement, same-height replay, and
  lower-height rollback rejection;
- a deterministic depth-two structure-preserving mutation atlas across all
  certificate fields;
- every single-bit mutation of the canonical certificate encoding.

The mutation atlas is offline bug-discovery and regression evidence. It is not
a correctness proof.

Replay commands:

```bash
cargo +1.94.1 fmt \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --all -- --check

cargo +1.94.1 test \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --test checkpoint_finality_v1 --locked

cargo +1.94.1 clippy \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --test checkpoint_finality_v1 --locked -- -D warnings
```

## Explicit nonclaims

This implementation does not establish:

- external consensus truth or fork-choice correctness;
- Tau checkpoint acceptance or Tau state assignment;
- liveness, validator rotation, slashing, or adversarial network finality;
- that the supplied expected binding came from an authenticated adapter;
- that the supplied prior checkpoint height came from rollback-resistant
  durable state;
- state replay, proof-receipt authentication, or data availability;
- atomic value-state admission;
- release, settlement, bridge, or production authority.

These claims remain false until the protocol-specific governed finality
verifier and atomic consuming boundary are implemented and evidenced.
