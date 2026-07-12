# ZRPF State-Bound Ordinary Spot Settlement Guest Specification

Date: 2026-07-12

Status: implemented with the rebuilt L2 image identity pinned; settlement guest
image identity, receipt evidence, sealed host verifier, and admission pending

## Claim Scope

This specification defines one RISC0 guest that authenticates an exact Value
Aggregate V5 level-two proposal before constructing the T17 state-bound
ordinary Spot settlement certificate.

The guest establishes this bounded statement:

```text
verify_assumption(governed_l2_image_id, exact_v5_proposal_bytes)
&& exact_decode_v5_proposal(exact_v5_proposal_bytes)
&& validate_exact_authorization_and_sparse_witness
&& validate_exact_full_blob_da_certificate_over_v2_replay
&& derive_claim_binding(governed_l2_image_id, exact_v5_proposal_bytes)
&& compose_state_bound_ordinary_spot_certificate_v2
-> canonical SettlementEpochCertificateV1 bytes
```

The implementation provides source-level and deterministic host evidence plus
the rebuilt L2 image identity. It does not provide the settlement guest image
identity or a verified settlement receipt in this slice.

## Receipt-First Input Boundary

The existing `OrdinarySpotSettlementGuestInputV2` wire remains unchanged:

```text
version
exact V5 proposal bytes
authorization
exact sparse-Merkle cell witness
exact full-blob DA certificate
```

`OrdinarySpotSettlementGuestEnvelopeV2` is the proposal-opaque decode stage. It
bounds the complete input and each component, validates exact authorization,
witness, and DA-certificate encoding, and preserves the V5 proposal bytes
without decoding or interpreting them. Its fields are private. The only public
data accessor exposes the exact proposal byte slice needed by RISC0 assumption
verification.

After the guest verifies this exact byte slice under the governed L2 image,
`bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2`
consumes the envelope and constructs the existing validated guest input. This
step exact-decodes the proposal. The function name records a caller
precondition; the shared function carries no receipt and grants no authority.

The pre-verification envelope decoder must accept a bounded malformed proposal
payload as opaque bytes. The post-verification binding step must reject that
payload. This test pair guards verification-before-interpretation ordering.

## Guest-Local Typestate

The guest owns a private `ReceiptVerifiedSpotSettlementInputV2` value. Its
constructor performs these operations in order:

1. call `env::verify` with the compile-time governed L2 image and the exact
   opaque proposal bytes;
2. derive the RISC0 verified-claim binding from that same image and byte slice;
3. consume the opaque envelope through the post-verification binding function.

Proposal decoding and settlement composition are absent from the constructor
before `env::verify`. The private typestate then calls the proof-neutral shared
composition boundary.

The guest input contains no receipt-valid Boolean, expected settlement image,
host self-image, semantic claim binding, receipt bytes, verifier metadata, or
authority flag.

## Root-Policy Ownership

The guest-safe `value_aggregate_root_policy` crate is the sole compiler-visible
owner of the L2 image used by the settlement guest. The Value Aggregate L2
guest, its shared composition crate, and its L2-only child policy must exclude
this root policy from their normal, build, and development dependency closure.

The policy uses the explicit symbol:

```text
PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5
```

Its bytes are:

```text
49c94dc5618c5e82372265cc75ee77d0985d9ab1b7b223f036e513870d6742f8
```

The image was rebuilt from source commit
`4ef41cdf2f30d02615f0df9b34882c98accb3c61`, tree
`3e8e5679ba8c5e8eaf2c8f800276cf301819bc63`. The identity remains in the
separate root-policy crate so the L2 guest cannot acquire a compiler-visible
self-identity dependency.

## Shared Composition Boundary

`compose_ordinary_spot_settlement_guest_output_after_l2_verification_v2` is a
pure, proof-neutral host/guest function. Given the validated existing guest
input and a caller-derived claim binding, it:

1. exact-decodes the canonical V5 proposal bytes;
2. invokes
   `compose_ordinary_spot_settlement_certificate_with_state_and_full_blob_da_v2`;
3. encodes and returns only canonical `SettlementEpochCertificateV1` bytes.

The shared function has no image policy, receipt, environment, I/O, Boolean
verdict, or persistence dependency. Executable host tests compare its output
with direct strict T17 composition and exact certificate decoding.

## Method Registration And Output

The method is registered as `ordinary_spot_settlement`. Its guest entry point:

```text
read bounded bytes
-> decode proposal-opaque envelope
-> verify exact L2 assumption
-> derive exact claim binding
-> bind and compose
-> commit canonical certificate bytes
```

The guest commits no wrapper, image identity, receipt metadata, or host label.
The canonical certificate is at most the protocol's 1,024-byte bound.

## Required Evidence

- source-contract ordering for verify, claim derivation, proposal binding,
  composition, canonical encoding, and commit;
- root-policy dependency-closure tests preventing L2 self-identity cycles;
- independent rebuilt image-word fixture and source/tree provenance;
- executable host parity between the shared guest boundary and direct T17
  composition;
- malformed opaque proposal acceptance followed by post-verification decode
  rejection;
- wrong image and exact proposal mutations changing the derived claim binding;
- existing T17 truncation, trailing-data, bound, field-mutation, and V1
  compatibility tests;
- full ZRPF workspace tests, doc tests, format, clippy, source scans, and claims
  registry checks.

## Explicit Non-Claims

This slice provides no settlement guest image identity, generated settlement
guest ELF, settlement receipt, proof replay, sealed host verifier,
receipt-profile admission, malformed-seal evidence, DA persistence or
retrievability proof, source finality, authorization-grant existence, durable
replay protection, atomic ledger update, settlement authority, release
authority, privacy, throughput, or production authority.

The future sealed verifier must authenticate the settlement receipt under the
rebuilt settlement image, require exact canonical certificate bytes, and bind
independent expected scope before any admission decision. Durable value
movement additionally requires atomic application of independently checked
effects and replay protections.
