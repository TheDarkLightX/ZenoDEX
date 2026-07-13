# Spot settlement V7 RISC0 lane

This standalone workspace closes one bounded relation:

```text
final V6 settlement receipt
  -> exact child journal verification inside RISC0
  -> child-bound full-blob DA replay
  -> source transition re-execution
  -> exact V7 pre/post state-root opening
  -> internally derived typed settlement Plan B
  -> bounded V7 receipt journal
  -> one sealed host receipt verification
  -> byte-for-byte host recomposition
  -> private pre/post/Plan B capability
```

The lane is intentionally fail closed while
`FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1` is all zero. C1 must
materialize the final V6 source closure and image ID before the guest, harness,
or verifier can advance past that gate. A source-built V7 method ID must also
be nonzero.

## Authority boundary

The raw guest envelope is a proposal. The guest may use only the exact child
journal bytes as the input to `env::verify` before interpreting any child
journal, DA certificate, replay, source transition, or host state-opening
bytes. A guest-local typestate performs the remaining composition after that
verification. The evidence harness additionally sends the child receipt
through the existing sealed V6 canonical-Succinct verifier before registering
it as an assumption. The V7 journal binds the governed V6 child program and
required receipt-security-profile identities. The raw journal records that
policy requirement; it does not by itself authenticate which receipt artifact
resolved the recursive claim.

The host verifier accepts canonical V7 Succinct receipt bytes, canonical V6
child receipt bytes, and the exact guest input bytes. It sends the V6 artifact
through the existing sealed V6 verifier, matches its exact program, receipt
profile, and child journal, then retains ownership of that authenticated child
capability. It pins the V7 RISC0 3.0.5 Poseidon2 receipt profile, verifies the
V7 receipt once, strictly decodes the V7 journal, and recomposes the complete
journal from the retained input. Its private result retains:

- the complete pre-state snapshot;
- the complete post-state snapshot;
- the internally derived Plan B;
- the exact guest input bytes;
- the authenticated canonical V6 child receipt capability;
- the verified V7 program, profile, manifest, receipt, and journal.

The private result is non-serializable and has no public constructor. A future
atomic settlement store must consume it directly. A commitment by itself is
insufficient to update balances.

All settlement and production authority constants remain `false`.

## Firecracker output

Containers are limited to the hermetic, networkless build and CI layer. Native
replay and verifier execution belong in the existing one-shot Firecracker
microVM layer. Signing remains outside both environments.

`SpotSettlementV7VerifierOutputV1` is the bounded, data-only record carried by
the Firecracker payload. Its exact binary framing is:

```text
8 bytes   magic = ZSPTV7O1
2 bytes   version = 1, big endian
4 bytes   total byte length
4 bytes   canonical V7 journal byte length
4 bytes   exact Plan B byte length
4 bytes   exact host state-opening input byte length
18 x 32   fixed identities and commitments
N bytes   canonical V7 journal
```

The fixed fields, in order, are:

1. verified V7 program ID;
2. verified V7 profile ID;
3. verified V7 program-manifest root;
4. V7 journal SHA-256;
5. verified V6 child program ID;
6. required V6 child receipt-security-profile ID;
7. V6 child claim binding;
8. V6 child journal SHA-256;
9. DA certificate root;
10. DA data root;
11. exact Plan B commitment;
12. economic pre-state root;
13. economic post-state root;
14. action IDs root;
15. action-authorization bindings root;
16. authorization-grant spends root;
17. consumed-object IDs root;
18. host state-opening input SHA-256.

Plan B occurs exactly once, inside the canonical V7 journal. The output decoder
strictly decodes that journal and exposes the exact canonical Plan B bytes. It
checks the declared Plan B length and every duplicated association. This keeps
the complete payload below Firecracker's 64 KiB cap without weakening the
binding.

Proof-independent golden vectors freeze both canonical byte surfaces:

- V7 journal: 2,706 bytes, SHA-256
  `c5ee64c62a27f09f3966ab62c3de469e4c70bda8f20369cc4edeac6ae91c7e74`;
- Firecracker output framing: 3,308 bytes, SHA-256
  `e319bb78a5fd0aa11974ca70d9810f297bc3386e5de736b40e2bd025b613fd93`.

The Firecracker vector deliberately uses synthetic outer identities and is
accepted only by the private proof-independent codec test. The public governed
decoder rejects it, so the vector cannot manufacture a verified receipt or a
runner execution capability.

The raw bytes and their commitment marker remain data only. Parsing them cannot
construct, reconstruct, deserialize, or replace the sealed Rust verified type.
A future private Firecracker-runner execution capability must validate the
governed VM execution record and bind the exact request, nonce, artifacts,
runtime profile, output, and teardown result before an application adapter can
advance. The adapter must also compare the host-input length and SHA-256 with
the exact canonical bytes it supplied. That capability is distinct from the
output parser and does not yet exist in this workspace.

The output is not an attestation, signature, finality certificate, release
authorization, settlement authorization, or production authorization.

## Local checks

The RISC0 guest must not be executed as a host test binary because its syscalls
exist only inside the zkVM. Run focused host checks with the placeholder method
build:

```bash
PINNED_BIN="$HOME/.risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin"
export PATH="$PINNED_BIN:$PATH"
export RUSTC="$PINNED_BIN/rustc"
export RUSTDOC="$PINNED_BIN/rustdoc_tool_binary"

RISC0_SKIP_BUILD=1 cargo test --locked \
  -p zenodex-zrpf-risc0-spot-settlement-v7-child-policy \
  -p zenodex-zrpf-risc0-spot-settlement-v7-shared \
  -p zenodex-zrpf-risc0-spot-settlement-v7-verifier \
  -p zenodex-zrpf-risc0-spot-settlement-v7-harness

RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace \
  --exclude zenodex-zrpf-risc0-spot-settlement-v7-guest \
  --all-targets -- -D warnings

RISC0_SKIP_BUILD=1 cargo clippy --locked \
  -p zenodex-zrpf-risc0-spot-settlement-v7-guest \
  --bin zenodex-zrpf-risc0-spot-settlement-v7-guest -- -D warnings

cargo fmt --all -- --check
```

A source-build lane must omit `RISC0_SKIP_BUILD`, use the pinned RISC0
toolchain, start from an absent target directory, and compare the freshly built
ELF-derived image ID with the governed release identity. The resulting native
verifier then runs under the Firecracker jailed-runner contract.

## Current non-claims

This workspace does not yet establish:

- a materialized final V6 child image;
- fresh V7 proof evidence;
- durable atomic application-state settlement;
- data retrievability beyond the exact full-blob certificate relation;
- finality, release, governance, or production authority;
- cross-host reproducible builds;
- privacy or covert-channel freedom.
