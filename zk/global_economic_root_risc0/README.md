# Global economic root guest V1

This new guest supports initialization and recursive epochs under one compiled
root image. A fresh isolated V1 profile can name that image for both statement
families. Existing standalone guests, profiles and public journals retain their
original meaning.

The private input has an eight-byte `ZDXROOT1` magic, a one-byte tag, a four-byte
little-endian payload length, and exactly that payload. Tag 0 carries canonical
initial-state JSON with its existing 8 MiB ceiling. Tag 1 carries canonical
recursive-epoch postcard with its existing 2 MiB ceiling. Unknown tags, trailing
bytes, noncanonical encoding and invalid preflights reject before journal commit.

The shared dispatcher calls the existing initial-state, direct-epoch,
command-aggregation and aggregated-epoch preflights. It returns private-field
prepared values containing the exact existing journal and ordered child claims.
The guest verifies every child claim and commits only that journal. Rejection
aborts execution; this guest proves accepted statements only.

Initialization and epochs share the `GlobalSettlementABI V1` schema identifier.
Their closed field sets and exact journal bytes determine the statement family.
The private tag is never permission to commit arbitrary bytes.

The host measures the compiled ELF and checks its ID, rejects placeholder
methods, binds initial/epoch public `root_image_id` to that exact ID, and checks
every supplied child receipt's count, order, kind, journal and cryptographic
verification before installing assumptions. Only Succinct receipts are accepted;
the host compiles RISC0 with `disable-dev-mode`. The existing aggregate preflight
requires every aggregation child image to equal the certificate root image, so
an aggregate under an old standalone epoch image cannot substitute for a child
under this new root image.

`host/src/bin/verify_receipt_v1.rs` mounts the shared measured receipt endpoint
with this compiled root image and the canonical postcard receipt codec. It has
no image fallback, codec negotiation or publication capability.

## Checks

Use an authorized remote host for proof builds. A host-only check is:

```sh
RISC0_SKIP_BUILD=1 cargo test --locked -p zenodex-global-economic-root-risc0-shared
RISC0_SKIP_BUILD=1 cargo test --locked -p zenodex-global-economic-root-risc0-host
RISC0_SKIP_BUILD=1 cargo clippy --locked -p zenodex-global-economic-root-risc0-shared -p zenodex-global-economic-root-risc0-host --all-targets -- -D warnings
```

The ignored real proof test proves genesis, a structural child, the matching
direct epoch, and a foreign-image receipt with the exact epoch journal. It
checks same-profile genesis-to-epoch state-root continuity and exact acceptance;
it rejects missing children, fake children, changed child journals, changed
contexts, exchanged statement families and the genuine foreign-image receipt.
Those child-refusal cases exercise the host guard. The separate raw-executor
test verifies a retained genuine epoch receipt as its positive control, then
bypasses the host guard and executes the exact same input with missing or wrong
child assumptions. It requires prover refusal or a receipt rejected by the
cryptographic verifier. This detects removal of the guest assumption loop.

```sh
RISC0_DEV_MODE=0 RISC0_PROVER=local cargo test --locked --release -p zenodex-global-economic-root-risc0-host --features cuda --test real_initialization_epoch real_genesis_then_epoch_share_one_profile_image_and_reject_foreign_receipts -- --exact --ignored --nocapture
RISC0_DEV_MODE=0 RISC0_PROVER=local cargo test --locked --release -p zenodex-global-economic-root-risc0-host --features cuda --test real_guest_assumptions -- --ignored --nocapture
RISC0_DEV_MODE=0 RISC0_PROVER=local cargo test --locked --release -p zenodex-global-economic-root-risc0-host --features cuda --test real_aggregation -- --ignored --nocapture
```

Set `ZENODEX_ROOT_EVIDENCE_DIR` to a dedicated output directory to retain the
four receipts, journals, root and structural-child ELFs, canonical private input
frames and exact image IDs. Preserve the source manifest, actual compiler path
and executable hash, resolved dependency lock, build log and verifier binary
alongside those outputs. A startup rustup alias alone does not identify the
compiler selected by `risc0-build`; use a job-specific `RISC0_HOME` with a pinned
installed toolchain and retain the build's actual `Using rustc:` line.

The aggregation tests prove both nine commands and the admitted 64-command
ceiling using this root image for command aggregations and the final epoch.
The 65-command certificate returns the exact command-count bound rejection
before proving. Preserve separate output directories for each run. At the
64-command ceiling the retained source08 run computed 73 Succinct proofs in
121.45 seconds; its epoch frame was 33,579 bytes, journal 14,588 bytes and
canonical postcard receipt 300,322 bytes. These are one isolated build's
measurements, not a general throughput guarantee. Source08 manifest SHA-256:
`923b11557e0893fdf0f035278f4823639b7ea77bea951319bec589f917dc4255`.
Its retained evidence archive SHA-256 is
`fbdd484426fc452463b8f9ed8b66f6b8fdc7dc12d052170089ae7c8366fcaf52`.
The earlier initialization, direct epoch, nine-command aggregation and raw
guest controls archive SHA-256 is
`dc2843430247e087e9c0220e0cf3916c12b6d1bd41b9005786ea23ae189274d7`.

The pinned compiler can retain source paths in ELF panic locations. Moving the
source tree can therefore change an image without changing source bytes.
Qualify the actual measured ELF under a fixed build path or a reviewed stable
path-remapping contract; source hashes alone do not imply image reproducibility.

## Dependency and claim boundaries

The crate reuses pinned RISC0 3.0.6, postcard 1.1.3 and the existing shared
preflights, plus the three existing compatibility patches. Its optional host
`cuda` feature exposes the existing RISC0 local GPU prover. Verification builds
leave it disabled. The complete resolved proving dependency closure must be
checked separately from a startup `--locked` flag. The lock is seeded from the existing initial-state lock and
normalized by `cargo test --offline -p zenodex-global-economic-root-risc0-shared`;
the six base registry additions match the already pinned epoch dependencies.
The required CUDA additions are compared with the checksum-verified resolved
dependency manifest of the earlier isolated CUDA job. This avoids replacing any
existing initial-state pins. Disabling CUDA and supplying a separately qualified
external prover is an alternative, with a separate executable trust boundary. Test-only
fixture support reuses the retained initial-state fixture and structural leaf.

The structural child proves supplied bytes. It does not prove asset transfer,
coordinator or route economic semantics. Initial-state source-authorization
legitimacy and the existing initial-state nonclaims remain external obligations.
This crate does not establish publication authority, profile admission, allocation
continuity, datastore durability, full lane semantics, refinement or production
value safety. It repairs the single-image dispatch obstacle within that scope.
