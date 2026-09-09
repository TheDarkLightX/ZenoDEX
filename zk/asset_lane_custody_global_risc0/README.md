# V2 custody and global refinement guest

This flat guest calls the existing Rust custody coordinator and global state
refiner, then commits their exact four-field economic statement. Its Python
producer and native Rust entry share five retained economic vectors. The guest
has no recursive children, host prover service, signing authority or publisher.

The [statement specification](../../docs/specifications/ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_V2.md)
defines the inner payload and bounded witness frame. Guest stdin is the frame's
length as four little-endian bytes, followed by exactly that many bytes and EOF.
The reader checks the 5,242,909-byte ceiling before allocation. Invalid framing,
canonical decoding, economic rejection or global refinement aborts execution.

Native transport tests and source integration do not qualify a RISC0 image or
receipt. The initial integration has no measured image, admitted release
profile, complete CBC admission binding, cryptographic authentication, current
store witness or durable publication path. In particular, the module journal's
`receipt_root` is a deterministic semantic commitment, not a cryptographic
receipt. Historical ABI V1 proof families remain separate.

Native checks, which do not build or execute a zkVM guest:

```bash
cargo +1.90.0 test --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-guest --lib
cargo +1.90.0 check --locked --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-guest --bin zenodex-asset-lane-custody-global-guest
```

Build the actual ELF and computed image ID on qualified proof infrastructure:

```bash
cargo +1.90.0 build --locked --release \
  --manifest-path zk/asset_lane_custody_global_risc0/Cargo.toml \
  -p zenodex-asset-lane-custody-global-risc0-methods
```

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
