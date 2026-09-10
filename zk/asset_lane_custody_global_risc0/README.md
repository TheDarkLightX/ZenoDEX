# V2 custody and global refinement guest

This flat guest calls the existing Rust custody coordinator and global state
refiner, then commits their exact four-field economic statement. Its Python
producer and native Rust entry share five retained economic vectors. A fixed
verifier selects this guest's compiled ELF/image and exact JSON Receipt codec
through the existing raw receipt protocol. A bounded proof-producer CLI uses
that same image and independently verifies its returned receipt. The workspace
has no recursive children, signing authority or publisher.

The [statement specification](../../docs/specifications/ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_V2.md)
defines the inner payload and bounded witness frame. Guest stdin is the frame's
length as four little-endian bytes, followed by exactly that many bytes and EOF.
The reader checks the 5,242,909-byte ceiling before allocation. Invalid framing,
canonical decoding, economic rejection or global refinement aborts execution.

Native transport tests and source integration do not qualify a RISC0 image or
receipt. The Python integration now combines isolated command authentication
with explicit guest-role selection and measured endpoint verification. The
workspace still has no qualified measured image, genuine receipt, store-owned
role selection or durable publication path. In particular, the module journal's
`receipt_root` is a deterministic semantic commitment, not a cryptographic
receipt. Historical ABI V1 proof families remain separate.

Native checks, which do not build or execute a zkVM guest:

```bash
cargo +1.90.0 test --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-guest --lib
cargo +1.90.0 check --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-guest --bin zenodex-asset-lane-custody-global-guest
cargo +1.90.0 test --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-risc0-host --lib
```

Build the actual ELF and computed image ID on qualified proof infrastructure:

```bash
cargo +1.90.0 build --locked --release \
  --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-risc0-methods
cargo +1.90.0 build --locked --release \
  --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-risc0-host --features compiled-guest \
  --bin verify_receipt_v2 --bin prove_receipt_v2
```

The host library's default build contains the bounded Receipt codec, input
framing and native statement preparation. The executables require
`compiled-guest` and the actual methods dependency; there
is no alternative image selection or placeholder executable. It reuses the
shared verifier's Succinct-only, compiled-image and exact-journal checks.
`disable-dev-mode` is a required SDK feature. Run verifier processes with
`RISC0_DEV_MODE=0`, as the existing Python transport enforces. The pinned SDK
panics if called with both that feature and `RISC0_DEV_MODE=1`; this refuses
verification and is not a typed codec error.

`prove_receipt_v2` reads the same outer length and five-component frame as the
guest from stdin. It recomputes the statement locally, requests a Succinct proof,
requires its exact journal and compiled image, verifies it, then writes one
canonical JSON Receipt to stdout. It refuses development-mode configuration and
empty or zero method placeholders. Its 16,777,216-cycle session ceiling is a
provisional work bound; no minimum or maximum legal custody-state fit has been
measured. Native environment construction does not demonstrate enforcement by
the guest executor.

The producer enables the pinned SDK's `client` feature and needs a compatible
external `r0vm`. Leave `RISC0_PROVER` unset or select `ipc`/`actor`; this build
does not enable `local` or `bonsai`. SDK selection/setup can panic on unsupported
configuration or unavailable executables, producing no accepted receipt. Typed
selection failure, actual execution, build-size review and proving performance
remain qualification work. The external prover receives the witness, so its
confidentiality and availability remain operational premises. Independent local
receipt verification is required even when the prover is remote.

`src/integration/asset_lane_custody_receipt_verification_v2.py` connects native
statement preparation to a snapshot of the concrete measured verifier config.
Its result remains ordinary bytes under a trusted configuration premise. A
wrong or maliciously selected executable is not made trustworthy by hashing it.
Native codec and protocol-fixture tests provide no genuine-receipt success.

`src/integration/profiled_asset_lane_custody_receipt_v2.py` selects the separate
`ASSET_LANE_CUSTODY_GLOBAL_V2` role using an independently supplied binding root.
Its [role specification](../../docs/specifications/asset-lane-custody-guest-role-v2.json)
binds the custody/global schema and exact journal to the selected image, endpoint
bytes, build commitments and limits. It acquires the existing sealed BLS and
receipt transports in the same call. The V1 profile's ROOT image slot and V1
receipt ports retain their existing meanings. The selected root and active
profile are trusted isolated configuration; evidence labels do not qualify a
build or grant writer authority.

The methods build refuses `RISC0_SKIP_BUILD`; it supplies no placeholder images.
The direct SDK/build dependencies reuse RISC0 `=3.0.6`, as in the existing guest
families. No additional runtime dependency family was introduced. The initial
lockfile was seeded from `zk/asset_transfer_module_risc0/Cargo.lock` and resolved
offline for these workspace members; retain the resulting lock for replay.
Both direct RISC0 crates declare Apache-2.0. Reusing their existing pinned stack
avoids a second prover implementation; it retains the SDK's transitive build
size and security assumptions. The economic core remains deterministic and
performs no IO. Removing this unadmitted guest workspace leaves native custody
and global refinement available. Image and dependency qualification are still
required before release admission.

The producer adds the same SDK's client feature and the existing local V2 ABI
crate. Its lock update was resolved offline; it includes client IPC dependencies
and avoids an additional proving implementation or in-process proving server.
Removing the producer and that feature leaves the fixed receipt verifier and
native custody transition available.
