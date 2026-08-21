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
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --lib --tests -- -D warnings
cargo fmt --all -- --check
```

Real release-evidence replay:

```bash
RISC0_PROVER=local cargo test --locked \
  -p zenodex-asset-transfer-module-risc0-host \
  --features cuda \
  --test real_proof \
  real_asset_transfer_transition_proves_the_exact_module_journal \
  -- --ignored --exact --nocapture
```

The `cuda` feature makes the CUDA backend available while CPU-only replay stays
portable. `RISC0_PROVER=local` selects the local prover. Record live
`nvidia-smi` utilization and `nvcc --version` because feature selection alone
does not establish that GPU kernels executed.

Recorded RunPod evidence for the exact current guest:

```text
proof-run source: f574f677c2474a81dceebdde8157b8fe0d6f3f8d
evidence head: 6aa4333cc6104136bb8a19b6207c53226e3b760b
RISC0 version: 3.0.6
image words: [2708773262, 3284681053, 4030353785, 209039674,
              2904775276, 1338612034, 3001795512, 4066241436]
image root: 0x8e9974a15d41c8c379513af03ab1750c6c5a23ad4299c94fb8c3ebb29ceb5df2
generated method .bin SHA-256:
  4affdf1877192a51fff973aab9051aaeb36eb548f650baa7e82882bbabd68283
real proof test elapsed: 37.53 seconds
complete command elapsed: 43.23 seconds
receipt kind: Succinct
result: exact module journal and image verified
```

The asset workspace is byte-identical between the proof-run source and evidence
head. The timing is one remote evidence datum and supplies no throughput or
resource-ceiling claim. This guest links the std-based stable ABI to preserve
exact host/guest transition reuse. A future no-std extraction would be a new
image and requires equivalence evidence.

This crate is unmounted. No active `EconomicProfileSnapshotV1` selects its
image, no lane coordinator or route composer consumes the receipt, and no
ZenoLedger writer can publish it. A real module receipt proves only this exact
asset-transfer transition; it does not establish whole-economy settlement,
terminal completeness, migration, durability, or production readiness.
