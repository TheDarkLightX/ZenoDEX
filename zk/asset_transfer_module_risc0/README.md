# ASSET_TRANSFER RISC0 module guest

This research-only workspace is the first economic leaf for
`GlobalSettlementABI V1`. The guest consumes one canonical
`AssetTransferLaneModuleInputV1`, calls the same deterministic Rust transition
used by the host, and commits the exact canonical
`LaneModuleTransitionJournalV1` only when the economic transition accepts.

The proof statement binds the module release, command occurrence, pre/post lane
roots, global effect-plan root, private-port root, semantic receipt root, and
terminal-obligation root already validated by the stable ABI. Typed economic
rejection aborts proving and therefore supplies no value-moving receipt.

Fast replay:

```bash
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Real release-evidence replay:

```bash
cargo test --locked -p zenodex-asset-transfer-module-risc0-host \
  --test real_proof \
  real_asset_transfer_transition_proves_the_exact_module_journal \
  -- --ignored --nocapture
```

Recorded local evidence for the exact current guest:

```text
RISC0 version: 3.0.6
image words: [3494995490, 1275137722, 1377448836, 1356757021,
              2581487242, 1957138521, 501643869, 607044243]
image root: 0x226651d0ba0e014c84331a521d78de508a5ede995990a7745d7ae61d93c22e24
embedded method bytes: 537272
embedded method SHA-256: 30278587c905f74373fb496acf518ffdfef7b415ad3c3ca6585b0a011b781c21
guest ELF bytes: 504848
guest ELF SHA-256: b3b58f60f38cfa8916c240d659a4e7728a8227e3215384f8eaee0b80b6780374
real proof elapsed: 569.750161942 seconds
```

The embedded method constant points to RISC0's generated `.bin`; the guest ELF
is recorded separately. The timing is one local evidence datum and supplies no
throughput or resource-ceiling claim. This guest links the std-based stable ABI
to preserve exact host/guest transition reuse. A future no-std extraction would
be a new image and requires equivalence evidence.

This crate is unmounted. No active `EconomicProfileSnapshotV1` selects its
image, no lane coordinator or route composer consumes the receipt, and no
ZenoLedger writer can publish it. A real module receipt proves only this exact
asset-transfer transition; it does not establish whole-economy settlement,
terminal completeness, migration, durability, or production readiness.
