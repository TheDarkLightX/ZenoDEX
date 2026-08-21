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
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Real recursive replay:

```bash
cargo test --locked -p zenodex-asset-lane-coordinator-risc0-host \
  --features cuda \
  --test real_composition \
  real_module_receipt_composes_into_the_exact_lane_journal \
  -- --ignored --nocapture
```

The `cuda` feature is explicit so CPU-only replay remains portable and a GPU
runner cannot silently execute the real-proof command through the CPU backend.
Record `nvidia-smi` and `nvcc --version` with the replay evidence.

Recorded local evidence on 2026-08-11:

- coordinator image words:
  `[1427482587, 4254091243, 771966465, 1925511048, 138359819, 1501093537, 4207195010, 1643793649]`;
- coordinator image root:
  `0xdba71555eb4790fd0146032e88f7c4720b343f08a1de785982b3c4faf14cfa61`;
- embedded method: 659,560 bytes, SHA-256
  `0bef82521f2ab986cc1e4e3ec8f6f39e79a172189bdeb17095a4ddf80f6bd438`;
- guest ELF: 627,136 bytes, SHA-256
  `407e3dae554b509580e67030dbb80148ca695fd0ce0f208012398e50cae649fe`;
- child ASSET_TRANSFER module proof: 522.722552067 seconds;
- complete module-to-lane recursive proof: 1,443.666295007 seconds;
- result: one real `Succinct` module receipt was consumed as an exact guest
  assumption and the exact coordinator journal was committed and verified.

That successful replay predates the current release-aware host fixture while
covering the same unchanged module and coordinator guest images. The current
fixture constructs content-derived module, coordinator, route, and profile
records; binds the exact occurrence and journals; and passes the real receipt
to the stable verifier that alone can construct `VerifiedLaneCompositionV1`.
Its synthetic active evidence labels and placeholder route image are test data,
not governance or release evidence.

The release-aware fixture compiled, passed the fast workspace tests, Clippy,
formatting, and structural-quality checks on 2026-08-11. Its real ignored replay
was interrupted with exit code 130 at the operator's request because sustained
local proving exceeded the workstation's heat and CPU budget. No release-aware
verified-lane binding root or successful receipt result was recorded. That
replay is deferred to a larger Runpod machine.

This remains source-scoped research evidence. No deployment-selected profile,
authenticated verifier registry, governed route composer, economic epoch, or
ZenoLedger writer consumes the lane receipt. The historical receipt and the
compiled test fixture confer no route, settlement, migration, publication, or
production authority.
