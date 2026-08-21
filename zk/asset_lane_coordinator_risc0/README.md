# ASSET_TRANSFER lane coordinator RISC0 guest

This research-only workspace is the first economic coordinator proof for
`GlobalSettlementABI V1`. The guest deterministically re-executes one typed
`ASSET_TRANSFER` module transition, runs the stable asset-lane coordinator,
verifies the exact pinned module image and canonical module journal as a RISC0
assumption, and commits the exact canonical `LaneCompositionJournalV1`.

The child module image is closed in coordinator source as
`ASSET_TRANSFER_MODULE_IMAGE_ID_V1`. Callers cannot select another child image.
Changing that image requires a new coordinator image and replacement
composition evidence. Typed module or coordinator rejection aborts before a
lane journal is committed.

Fast replay:

```bash
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --lib --tests -- -D warnings
cargo fmt --all -- --check
```

Real recursive replay:

```bash
RISC0_PROVER=local cargo test --locked \
  -p zenodex-asset-lane-coordinator-risc0-host \
  --features cuda \
  --test real_composition \
  real_module_receipt_composes_into_the_exact_lane_journal \
  -- --ignored --exact --nocapture
```

The `cuda` feature makes the CUDA backend available while CPU-only replay stays
portable. `RISC0_PROVER=local` selects the local prover. Record live
`nvidia-smi` utilization and `nvcc --version` because feature selection alone
does not establish that GPU kernels executed.

Recorded RunPod evidence on 2026-08-20:

- proof-run source: `5d3bc192811197b250d4e5fbdc8f40ffea5c8433`;
- evidence head: `6aa4333cc6104136bb8a19b6207c53226e3b760b`;
- coordinator image words:
  `[3654251601, 3195487566, 3106616364, 3539379948, 2697163327, 3171258320, 3221320101, 2106873291]`;
- coordinator image root:
  `0x5174cfd94e4577be2c342bb9eca6f6d23f72c3a0d08f05bda57101c0cb55947d`;
- generated method `.bin` SHA-256:
  `a555abc0a29c02942df847d2e4b3fb2dfac2b7b2a07a9888945b395c3e3bf157`;
- child `ASSET_TRANSFER` module proof: `38.76300509` seconds;
- complete module-to-lane proof: `98.481183913` seconds;
- test elapsed: `99.46` seconds;
- release-aware verified-lane binding root:
  `0x8afbb9391f2f4fa0e850253aaf0093b14c7e848ff51d000d3bb6e02f3fa30877`;
- result: one real `Succinct` module receipt was consumed as an exact guest
  assumption and the exact coordinator journal was committed and verified.

The lane workspace is byte-identical between the proof-run source and evidence
head. The fixture constructs content-derived module, coordinator, route, and
profile records; binds the exact occurrence and journals; and passes the real
receipt to the stable verifier that alone can construct
`VerifiedLaneCompositionV1`. Its synthetic active evidence labels and
placeholder route image are test data and carry no governance or release
authority.

This remains source-scoped research evidence. No deployment-selected profile,
authenticated verifier registry, governed route composer, economic epoch, or
ZenoLedger writer consumes the lane receipt. The historical receipt and the
compiled test fixture confer no route, settlement, migration, publication, or
production authority.
