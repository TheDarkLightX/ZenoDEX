# ZRPF Checkpoint Finality Policy V2 CBC Specification

Status: implemented proof-neutral protocol primitive. External finality,
settlement authority, and production authority remain unestablished.

## Purpose and scope

`checkpoint_finality_v2` defines a canonical linear checkpoint-chain contract
for the bounded ZRPF settlement path. It binds one proof journal and post-state
root to one caller-supplied checkpoint-finality projection, the application
checkpoint's parent hash, a governed application genesis anchor, and an
explicit prior-cursor proposal intended to come from durable state.

The sequence, hash, and parent fields define the ZRPF application checkpoint
chain. They are not external block heights, external block hashes, Tau heights,
or consensus-layer parent hashes. A protocol-specific verifier must commit all
external anchor details inside `finality_evidence_root`.

V2 is additive. It does not alter the V1 certificate, policy, hash domains, or
codec.

The intended authority progression is:

```text
external checkpoint bytes and finality evidence
  -> future protocol-specific governed verifier
  -> supplied application-checkpoint/finality projection
  -> SuppliedCheckpointFinalityBindingV2
  -> exact CheckpointFinalityCertificateV2 equality
  -> governed policy and cursor-proposal continuity check
  -> opaque CheckedCheckpointFinalityTransitionV2
  -> no settlement or production authority
```

The protocol-specific signature, quorum, fork-choice, or Tau verifier remains
outside this crate. Every V2 binding and cursor input is forgeable caller data
until that future governed verifier and durable consuming boundary supply it.

## Correct-by-construction chain rule

The policy governs one genesis anchor:

```text
(genesis_application_checkpoint_sequence, genesis_application_checkpoint_hash)
```

The caller supplies one explicit cursor proposal:

```text
CheckpointCursorProposalV2::empty()

or

CheckpointCursorProposalV2::from_prior_record(
  full governed scope,
  finality policy root,
  prior application checkpoint sequence,
  prior application checkpoint hash
)
```

For an empty proposal, the policy's application genesis anchor is the prior
checkpoint. For a nonempty proposal, the proposed record's `(sequence, hash)`
is used only after the checker verifies its complete scope and local policy
root. A proposed record below the governed genesis sequence rejects. A proposed
record at the genesis sequence must carry the exact governed genesis hash.

Let `(s_p, H_p)` be that prior application checkpoint and `(s_c, H_parent)` be
the candidate sequence and parent hash. V2 accepts continuity only when:

```text
s_c = checked_add(s_p, 1)
H_parent = H_p
```

An overflow, skipped sequence, repeated sequence, lower sequence, wrong parent,
wrong proposal scope, pre-genesis record, replaced genesis hash, or wrong local
policy root rejects with a typed error. This narrow rule produces one linear
application-checkpoint successor relation. It does not implement external fork
choice or prove that the supplied proposal came from durable state.

An empty proposal cannot admit an arbitrary later checkpoint. It can admit only
the exact successor of the policy-governed application genesis anchor. A
consuming store must prevent rollback from a committed cursor to an empty
proposal.

## Certificate V2

`CheckpointFinalityCertificateV2` contains:

| Field | Binding |
| --- | --- |
| `certificate_version` | Exact V2 schema version. |
| `application_id` | Application whose transition is checkpointed. |
| `chain_or_domain_id` | Application execution domain. |
| `epoch_id` | ZRPF epoch represented by the proof journal. |
| `proof_journal_hash` | Exact state-bound ZRPF journal committed by the checkpoint. |
| `post_state_root` | Exact application post-state root. |
| `application_checkpoint_sequence` | ZRPF application checkpoint sequence. |
| `application_checkpoint_hash` | ZRPF application checkpoint identity. |
| `parent_application_checkpoint_hash` | Explicit parent in the ZRPF application checkpoint chain. |
| `finality_network_id` | External finality network identity. |
| `finality_protocol_id` | Governed protocol and adapter identity. |
| `external_finality_policy_hash` | External quorum, fork-choice, and finality policy commitment. |
| `finality_verifier_set_root` | Exact signer or verifier-set commitment. |
| `finality_evidence_root` | Commitment to all supplied protocol-specific evidence, including external height/hash/parent anchors where applicable. |
| `finality_policy_root` | Root of the local V2 acceptance policy. |
| `certificate_root` | Domain-separated root of every preceding field. |

There is no caller verdict field. The schema contains no `ok`, `verified`,
`finalized`, `settlement_authority`, or `production_authority` Boolean.

## Full scope binding

The local policy binds:

```text
policy version
application ID
chain/domain ID
finality network ID
finality protocol ID
expected external finality policy hash
expected finality verifier-set root
genesis application checkpoint sequence
genesis application checkpoint hash
```

The supplied checkpoint-finality projection independently carries:

```text
application ID
chain/domain ID
epoch ID
proof journal hash
post-state root
application checkpoint sequence
application checkpoint hash
parent application checkpoint hash
finality network ID
finality protocol ID
external finality policy hash
finality verifier-set root
finality evidence root
```

A proposed nonempty prior record carries the complete stable policy scope, the
local policy root, and the prior application checkpoint sequence and hash. The
checker compares the certificate, supplied projection, proposal, and policy
rather than assuming that matching checkpoint hashes imply matching scope.

This prevents local relabeling across applications, domains, networks,
protocols, external policies, verifier sets, or local V2 policies. It does not
authenticate the supplied projection or proposed prior record; those are
deliberately ordinary data values at this proof-neutral layer.

## Opaque checked transition

Successful checking returns `CheckedCheckpointFinalityTransitionV2`. It has no
public constructor and retains exactly:

```text
policy root
certificate root
supplied checkpoint-finality binding
prior cursor proposal
derived next cursor
```

The derived next cursor has private construction and carries the complete
governed scope, exact policy root, and candidate application checkpoint
sequence/hash. Safe getters let a future atomic store consume those checked
values without reconstructing them from caller fields. This opaque local value
does not authenticate external finality and does not create persistence or
settlement authority.

## Exact roots and codec

Certificate-root domain:

```text
zenodex.zrpf.checkpoint_finality.certificate_root.v2
```

Policy-root domain:

```text
zenodex.zrpf.checkpoint_finality.policy_root.v2
```

Each hash preimage starts with a big-endian `u16` domain length. Version and
application-checkpoint sequence fields are big-endian. Existing ZRPF
application, domain, and commitment types enforce nonzero 32-byte values.
The governed genesis checkpoint hash and every candidate checkpoint identity
remain nonzero `CommitmentV3` values. The checker's fixed-width request ABI
encodes an absent proposed prior cursor with tag zero followed by a reserved,
zero-filled record slot. Those reserved bytes are framing and never decode as a
typed checkpoint hash. A present record uses tag one and every typed hash must
be nonzero. The certificate root is derived directly from its typed input fields
before the certificate object is constructed; there is no placeholder-root
state.

The certificate uses exact Postcard encoding with a 576-byte ceiling. Decoding
rejects:

- empty input;
- input above the ceiling;
- malformed or nonminimal Postcard;
- truncated values;
- trailing bytes;
- noncanonical re-encoding;
- a stale certificate version;
- a certificate root inconsistent with decoded fields;
- unknown fields at the typed Serde boundary.

Policy and certificate roots change when any bound field changes. The cursor
proposal is a typed local input. Durable integration must define and enforce its
own versioned storage codec, stable scope key, rollback protection, and atomic
compare-and-swap before it can supply authority.

## Standalone exact checker process

`zk/zrpf_checkpoint_finality_checker` exposes the proof-neutral V2 check through
one bounded native process ABI. Its request consists of an 885-byte fixed
header followed by exactly one canonical certificate of at most 576 bytes. The
header carries:

```text
16-byte request magic
u16 checker protocol version
complete governed V2 policy
complete supplied V2 binding
u8 prior-cursor tag
264-byte fixed prior-record slot
u16 certificate length
```

An empty prior-cursor tag requires every byte in the prior-record slot to be
zero. A record tag requires the complete application, domain, finality scope,
local policy root, sequence, and checkpoint hash. Unknown tags, noncanonical
empty slots, zero values in nonzero typed fields, truncated input, trailing
input, or an inconsistent declared length reject before the protocol check.

On success the checker emits exactly 330 bytes containing the application and
domain, epoch, policy root, certificate root, effective prior cursor, derived
successor cursor, certificate SHA-256, request SHA-256, and a domain-separated
response commitment. It emits no caller verdict, release flag, settlement
flag, or production flag. Invalid input produces no success bytes and a
nonzero process exit. The response commitment provides framing integrity; it
is not a signature or execution attestation.

The current Spot V7 adapter supplies that bounded process boundary. It accepts
only the exact private V3 operational-policy capability and exact sealed
BLS-authenticated finality transition, reconstructs the 885-byte request
independently, executes the manifest-pinned static checker exactly once through
the pre-exec verifier shell, and compares all 330 response bytes with the local
expected response. It retains exact request/response bytes plus their hashes
inside a private nontransferable cross-checked value. The operational V3 join
accepts raw BLS-authenticated finality only with the exact checker and performs
the cross-check itself. It rejects a caller-supplied preconstructed
cross-checked value and carries the exact manifest, request, response, and
digest evidence in the live operational packet.

The authority manifest and executable digest remain caller-pinned and are not
selected by a release-governance capability. The V4 atomic record does not yet
persist the checker invocation evidence even though the live packet retains it.
This closes the normal local typed cross-check path while preserving release,
settlement, and production authority as false. Hostile code already executing
inside the same Python interpreter remains outside this capability claim.

## Fail-closed check order

The checker performs five stages:

1. validate certificate version and root consistency;
2. compare certificate scope and local policy root with the governed policy;
3. compare the complete supplied adapter projection with the policy and
   certificate;
4. derive the exact prior `(sequence, hash)` from the governed application
   genesis anchor or scope-checked proposal, including the genesis floor/hash
   constraints, then require exact successor sequence and parent-hash equality;
5. derive the opaque next cursor and checked transition from already validated
   values.

Every reject is a typed `CheckpointFinalityPolicyErrorV2` or nested certificate
error. Arithmetic uses `checked_add`. Unknown, stale, malformed, mismatched, or
overflowing inputs fail closed.

## Durable integration obligation

The proposal types deliberately make no durability claim. A production adapter
and ledger transaction must:

1. authenticate the external finality evidence under the governed network,
   protocol, external policy, and verifier set;
2. derive the supplied V2 binding from those authenticated bytes, committing
   external block/consensus anchors inside `finality_evidence_root`;
3. load the exact scope-keyed prior record from rollback-resistant state and
   create the cursor proposal;
4. bind `proof_journal_hash` to the receipt-authenticated ZRPF admission journal;
5. bind `post_state_root` to the executed economic transition;
6. run the V2 checker;
7. atomically consume the opaque checked transition, compare-and-swap the prior
   cursor, and persist the derived application checkpoint sequence/hash,
   certificate root, policy root, finality evidence, proof admission,
   replay/nullifier rows, and value state;
8. reject a stale, missing, reset, conflicting, or concurrently advanced cursor
   without applying any state effect.

The isolated V2 primitive cannot detect a caller that lies about durable state.

## Evidence

Focused tests cover:

- independent policy-root and certificate-root recomputation;
- exact Postcard round-trip, every truncated prefix, trailing bytes, empty
  input, and oversized input;
- unknown caller verdict fields, stale version, and forged certificate root;
- absence of caller authority Booleans;
- empty-proposal genesis-anchor acceptance;
- canonical tag-zero absent-prior encoding with a completely zero-filled
  reserved record slot;
- rejection of zero values in every typed checkpoint-hash position;
- empty-proposal arbitrary-sequence and wrong-parent rejection;
- proposed prior-record exact next-sequence and parent-hash acceptance;
- proposed records below genesis and at-genesis wrong-hash rejection;
- skipped, repeated, lower, and unrelated sequences;
- full certificate, supplied-projection, and prior-record scope substitutions;
- opaque checked-transition retention and derived-next-cursor binding;
- overflow from both genesis and proposed prior records at `u64::MAX`;
- root separation and rejection for every certificate field, plus the bounded
  depth-two structure-preserving mutation frontier;
- policy-root separation for every policy field;
- every single-bit mutation of the canonical certificate bytes.

The mutation and bit-flip corpus is bounded regression evidence. It is not a
mathematical proof of external finality or complete implementation correctness.

Replay commands:

```bash
cargo +1.94.1 fmt \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --all -- --check

cargo +1.94.1 test \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --test checkpoint_finality_v2 --locked

cargo +1.94.1 clippy \
  --manifest-path zk/zrpf_protocol/protocol/Cargo.toml \
  --test checkpoint_finality_v2 --locked -- -D warnings

cargo +1.94.1 fmt \
  --manifest-path zk/zrpf_checkpoint_finality_checker/Cargo.toml \
  --all -- --check

cargo +1.94.1 test \
  --manifest-path zk/zrpf_checkpoint_finality_checker/Cargo.toml \
  --locked --all-targets

cargo +1.94.1 clippy \
  --manifest-path zk/zrpf_checkpoint_finality_checker/Cargo.toml \
  --locked --all-targets -- -D warnings
```

## Explicit nonclaims

This V2 primitive does not establish:

- external consensus truth, quorum validity, or fork-choice correctness;
- Tau checkpoint acceptance or Tau state assignment;
- validator rotation, liveness, slashing, or adversarial network finality;
- that the supplied binding came from an authenticated finality adapter;
- that the standalone checker identity was selected by release governance;
- durable persistence of the checker request, response, manifest, and
  executable identity in the atomic operational record;
- hostile same-interpreter resistance for Python private capability objects;
- that the cursor proposal came from rollback-resistant durable state;
- protection against resetting a persisted cursor to an empty proposal;
- ancestry of a proposed prior record above the governed genesis anchor;
- a canonical derivation of the application checkpoint hash from application
  state, proof, or external-finality evidence;
- epoch continuity or epoch-to-checkpoint-sequence correspondence;
- application pre-state/post-state continuity or deterministic state replay;
- proof-receipt authentication or data availability;
- atomic proof, replay/nullifier, checkpoint, and economic-state admission;
- bridge authority, settlement authority, release authority, or production
  authority;
- privacy, covert-channel resistance, or side-channel resistance.

Every listed authority remains false until its protocol-specific verifier,
durable atomic consuming boundary, release evidence, and independent review are
implemented and evidenced.
