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

## Deterministic guest-input builder

The `input_builder` package constructs the exact proof-neutral V7 guest
envelope from four canonical files:

1. a V6 `SettlementAdmissionJournalV1`;
2. a V6 `FullBlobDataAvailabilityCertificateV1`;
3. a V6 `ProposedSourceOpenedSpotSettlementReplayV3`;
4. a V7 `BoundedSpotStateRootV7HostInputV1`.

Each input is opened without following symlinks, bounded before allocation,
read once through a stable file descriptor, and checked against before/after
metadata. The builder strictly decodes and canonically re-encodes every
component before constructing and round-tripping the V7 envelope. Output uses
create-new semantics, mode `0600` on Unix, a complete sync, and exact reread
verification. An existing output is never overwritten.

Run it from this workspace:

```bash
cargo run --locked --offline \
  -p zenodex-zrpf-risc0-spot-settlement-v7-input-builder \
  --bin build_spot_settlement_v7_guest_input -- \
  --source-child-journal /path/to/settlement-admission-v6.bin \
  --data-availability-certificate /path/to/full-blob-da-v1.bin \
  --replay /path/to/source-opened-replay-v6.bin \
  --state-root-host-input /path/to/state-root-host-input-v7.bin \
  --output /new/path/spot-settlement-v7-guest-input.bin
```

The builder validates byte framing and canonical form only. It does not verify
a receipt, establish data availability, execute the transition, validate the
state opening, or grant release, settlement, or production authority. Those
checks remain inside the guest, sealed verifier, and future atomic admission
boundary.

## Accepted source-operation profile

The V1 guest profile accepts exactly one ordinary `TauSwap` `v1`
`SwapExactIn` intent from the transaction sender. The transaction must carry
the intent marker, contain exactly one signed intent, and contain no faucet
operation or faucet mint. Pool creation, liquidity changes, faucet framing,
multi-intent transactions, and every other intent variant reject before the
state opening can be composed. This restriction keeps the proved V7 state and
effect relation identical to the first production Spot slice; expanding it
requires a new governed profile and fresh proof evidence.

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
19 x 32   fixed identities and commitments
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
12. exact canonical Plan B bytes SHA-256;
13. economic pre-state root;
14. economic post-state root;
15. action IDs root;
16. action-authorization bindings root;
17. authorization-grant spends root;
18. consumed-object IDs root;
19. host state-opening input SHA-256.

Plan B occurs exactly once, inside the canonical V7 journal. Both the journal
and output fixed fields commit SHA-256 of those exact canonical bytes. The Rust
verifier derives the digest after exact Plan B decode and canonical re-encode;
the Python boundary hashes the exact bounded slice and requires both committed
digests to agree before candidate binding. The superseded 18/12-field frame
rejects. This keeps the complete payload below Firecracker's 64 KiB cap without
reimplementing Postcard semantics in Python.

This append-only V1 tightening occurred before any governed V7 image or receipt
was materialized. `SPOT_SETTLEMENT_V7_ABI_V1_MATERIALIZATION_STATUS` records
that source fact. After initial materialization, incompatible changes require a
new ABI version.

Proof-independent golden vectors freeze both canonical byte surfaces:

- V7 journal: 2,738 bytes, SHA-256
  `b406492100a3624fa41c0a3ba5694219f1dc609616f22d8e6fdfd775862546cf`;
- Firecracker output framing: 3,372 bytes, SHA-256
  `979b2e9cb4757de50ec935c55ca827c693ad5cb4e22ee8034bee9e7866de148c`.

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

## Authority-neutral proof runner

The harness includes `prove_spot_settlement_v7`. It consumes one exact encoded
V7 guest envelope and one canonical governed V6 child receipt. The runner uses
the sealed harness to verify the child, prove V7, verify the resulting Succinct
receipt, recompose the complete journal, derive the Firecracker output and Plan
B, and require the exact seal-word mutation to fail at receipt verification.
Only then does it create the five candidate output files.

```bash
PINNED_BIN="$HOME/.risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin"
export CARGO="$PINNED_BIN/cargo"
export PATH="$PINNED_BIN:/usr/bin:/bin"
export RUSTC="$PINNED_BIN/rustc"
export RUSTDOC="$PINNED_BIN/rustdoc_tool_binary"
unset RISC0_DEV_MODE
unset RISC0_SKIP_BUILD

"$PINNED_BIN/cargo" run --locked --offline --release \
  -p zenodex-zrpf-risc0-spot-settlement-v7-harness \
  --bin prove_spot_settlement_v7 -- \
  --v7-receipt-out /new/output/v7.receipt.json \
  --v7-receipt-seal-mutation-out /new/output/v7.mutation.json \
  --v7-journal-out /new/output/v7.journal.bin \
  --v7-verifier-output-out /new/output/v7.verifier-output.bin \
  --v7-plan-b-out /new/output/v7.plan-b.bin \
  --v6-child-receipt /input/v6.child.receipt.json \
  --v7-guest-input /input/v7.guest-input.bin
```

All output paths must be distinct, must not exist, and must not alias either
input. The command can leave an incomplete authority-neutral candidate set if
the host fails between file writes. The independent seven-artifact builder and
checker reject incomplete sets. A successful runner report grants no release,
settlement, production, privacy, DA, finality, or Firecracker authority.

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
  -p zenodex-zrpf-risc0-spot-settlement-v7-input-builder \
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
