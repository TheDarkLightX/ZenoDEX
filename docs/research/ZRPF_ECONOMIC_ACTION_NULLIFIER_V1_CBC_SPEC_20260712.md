# ZRPF Economic Action And Authorization Nullifier V1 CBC Specification

Date: 2026-07-12

Status: implemented protocol nucleus; deterministic local tests only

## Scoped claim

`zk/zrpf_protocol` now defines two proof-system-neutral data objects:

- `EconomicActionRecordV1`, a bounded semantic action record with private
  fields and a validated constructor;
- `AuthorizationConsumptionNullifierV1`, a nonzero 32-byte identifier derived
  from one canonical action and one canonical authorization grant identity.

The action ID and authorization-consumption nullifier exclude proof program or
image identity, receipt bytes or codec, intent salt, and signature bytes or
encoding. Changing only those envelope representations therefore cannot create
a new action identity or authorization-consumption identity.

This result supplies a deterministic identity nucleus. It does not authenticate
an action, authorize settlement, or persist a nullifier.

## Economic action record

The record contains:

```text
EconomicActionRecordV1 {
  record_version: u16
  application_id: bytes32
  chain_or_domain_id: bytes32
  action_type_id: bytes32
  authorization_subject_id: bytes32
  authorization_scope_id: bytes32
  authorization_nonce: u64
  valid_from_epoch: u64
  valid_through_epoch: u64
  pre_state_root: bytes32
  action_semantics_hash: bytes32
  effect_commitment: bytes32
  consumed_object_ids: sorted_unique bytes32[0..128]
}
```

All identifiers and commitments are nonzero. Epochs and the authorization nonce
use their complete unsigned 64-bit domains. The validity interval is inclusive
and must satisfy `valid_from_epoch <= valid_through_epoch`.

The constructor sorts `consumed_object_ids` by their exact 32-byte value. A
duplicate rejects. Input order is therefore representation detail, while
duplicate consumption remains an invalid semantic record.

The exact Postcard codec is bounded to 8,192 bytes. Exact decoding rejects an
empty input, an oversized input, trailing bytes, invalid fields, duplicate
consumed objects, and any byte sequence whose validated canonical re-encoding
differs from the input.

## Economic action ID

The action ID is SHA-256 over this exact preimage:

```text
u16be(len("zenodex.zrpf.economic_action_id.v1"))
|| "zenodex.zrpf.economic_action_id.v1"
|| u16be(record_version)
|| application_id
|| chain_or_domain_id
|| action_type_id
|| authorization_subject_id
|| authorization_scope_id
|| u64be(authorization_nonce)
|| u64be(valid_from_epoch)
|| u64be(valid_through_epoch)
|| pre_state_root
|| action_semantics_hash
|| effect_commitment
|| u32be(consumed_object_count)
|| concat(consumed_object_ids)
```

The fixed field order, explicit widths, domain framing, and sorted collection
avoid concatenation ambiguity and host iteration dependence.

## Authorization-consumption nullifier

The nullifier is SHA-256 over:

```text
u16be(len("zenodex.zrpf.authorization_consumption_nullifier.v1"))
|| "zenodex.zrpf.authorization_consumption_nullifier.v1"
|| u16be(1)
|| application_id
|| chain_or_domain_id
|| economic_action_id
|| authorization_subject_id
|| authorization_grant_id
|| authorization_scope_id
|| u64be(authorization_nonce)
|| pre_state_root
```

`authorization_grant_id` names the canonical grant or capability being
consumed. It must remain stable across signature schemes and signature
encodings when governance considers those representations equivalent.

The derivation accepts an `EconomicActionRecordV1` and an
`AuthorizationGrantIdV1`. It reads the other nullifier fields directly from the
validated record, removing caller-controlled duplicate projections.

## Disaster-state closures

| Disaster state | Construction rule | Evidence |
| --- | --- | --- |
| same action replayed under another proof backend | proof program and receipt representation have no record or nullifier field | representation-independence test |
| same action replayed with another intent salt or signature encoding | salt and signature bytes have no record or nullifier field | representation-independence test |
| consumed objects reordered to obtain another ID | constructor sorts exact object IDs | permutation test |
| one consumed object repeated | duplicates reject before construction | duplicate negative test |
| action fields concatenate ambiguously | fixed widths, collection count, and domain length prefix | independent preimage replay test |
| one semantic field changes without changing the action ID | every record field enters the preimage | field-separation test |
| different grant or action produces the same nullifier | grant ID and canonical action ID enter the nullifier preimage | nullifier-separation test |
| malformed or noncanonical bytes enter a trusted record | validated private fields plus exact bounded codec | codec negative tests |
| claimed consumed-object count forces unbounded allocation | sequence length rejects before allocation above 128 | claimed-count negative test |

## Evidence

Run from the repository root:

```bash
cargo fmt --manifest-path zk/zrpf_protocol/Cargo.toml --all -- --check
cargo test --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets
cargo clippy --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets -- -D warnings
```

The focused test independently reconstructs both SHA-256 preimages rather than
calling the production hash helper as its oracle. It also freezes one shared
action-ID and nullifier vector for cross-language replay.

## Explicit non-claims

This nucleus does not establish:

- correct derivation of `action_type_id`, `action_semantics_hash`, or
  `effect_commitment` from a ZenoDEX transition;
- validity, ownership, signature verification, revocation, expiry at admission
  time, quorum, or scope sufficiency of an authorization grant;
- uniqueness of an authorization grant identifier across a governed registry;
- receipt authentication or binding to a Semantic V2 verified receipt;
- Python, Tau, ZenoLedger, or another-language hash parity;
- a durable nullifier index or nullifier consumption policy for rejected
  actions;
- atomic commitment with balances, collateral, fees, rewards, carry, messages,
  application state, or settlement effects;
- release, settlement, privacy, throughput, public replay, or production
  authority.

## Next integration step

A sealed Semantic V2 verifier must derive the complete action record from the
receipt-authenticated semantic statement. ZenoLedger must independently
recompute both identifiers from governed action and grant data, enforce the
nullifier through a unique index, and commit that index in the same transaction
as the corresponding value and application-state effects.
