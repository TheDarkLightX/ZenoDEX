# Global economic epoch RISC0 guest

This research-only crate closes the first cryptographic recursion seam for
`GlobalSettlementABI V1`. The host accepts only nonempty `Succinct` route
receipts, verifies each receipt against its governed image and exact canonical
route-journal bytes, installs those receipts with `add_assumption`, and asks
the guest to resolve the same `(image ID, journal bytes)` pairs with
`env::verify`.

The guest preflight rederives each route journal root, direct SHA-256 journal
digest, and public route-assumption root. It checks canonical JSON, exact
profile/writer/occurrence bindings, deterministic state-root sequencing, and
the certificate's ordered assumption commitments before emitting the exact
epoch certificate journal.

The same closed guest image now supports three typed statements:

- a direct epoch over `1..=8` route receipts;
- a canonical command aggregation over `1..=8` route receipts; and
- an aggregated epoch over `9..=64` commands, partitioned into `2..=8`
  contiguous groups of eight.

The aggregated root accepts only same-image command-aggregation receipts and
binds their exact canonical partition, occurrence, route-journal,
route-assumption, state-chain, profile, writer-epoch, height, and derived
module-leaf totals. The release-aware host also requires the certificate's
root image to equal the compiled method image before proving.

The crate is unmounted. Placeholder ELFs and all-zero image IDs fail closed.
It does not grant settlement, commit, migration, outbox, profile activation,
or production authority.

Pinned SDK: `risc0-zkvm = 3.0.6` and `risc0-build = 3.0.6`.

The isolated host toolchain is pinned by `rust-toolchain.toml` to Rust 1.90.0;
the RISC0 guest compiler is supplied by the installed 3.0.6 toolchain. The
current reproducible method identifiers are:

```text
epoch generated method `.bin` sha256:
  6ea9191aa391a1961692e18825aa2380ed173715d252bb7aa465cb6bddaee5b2
epoch image root:
  0x0b2bbc04abe3cf8839c6e7763fcb403b5f3ba9473c07efe66f47e815e0435331

quarantined structural test-leaf generated method `.bin` sha256:
  838b14b0ce37e50b949c31f748b282b6b71c788efea184c3a174dba3bd91bf02
quarantined structural test-leaf image root:
  0xbce4d1087bba50d24e26848a83740cb3a41019e8af90d81f4bfd088059024a40
```

These values describe research artifacts. They are absent from every
active economic profile and carry no release authority.

`test_methods/route_structural_test_leaf` is quarantined test code. It merely
commits caller-supplied bytes so the ignored integration test can generate a
real child receipt and exercise recursive assumption resolution. It proves no
route transition, economics, authorization, conservation, or release status,
and its image ID must never appear in an economic profile.

## Replay

```bash
cargo build --locked -p zenodex-global-economic-epoch-risc0-methods
cargo test --locked -p zenodex-global-economic-epoch-risc0-shared
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --lib --tests -- -D warnings
cargo fmt --all -- --check

RISC0_PROVER=local cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --features cuda \
  --test real_composition \
  real_succinct_child_assumption_resolves_into_exact_epoch_journal \
  -- --ignored --exact --nocapture

RISC0_PROVER=local cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --features cuda \
  --test real_aggregation_nine \
  eight_routes_compose_directly_into_one_exact_epoch_root \
  -- --ignored --exact --nocapture

RISC0_PROVER=local cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --features cuda \
  --test real_aggregation_nine \
  nine_routes_compose_through_two_groups_into_one_exact_epoch_root \
  -- --ignored --exact --nocapture

RISC0_PROVER=local cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --features cuda \
  --test real_aggregation_nine \
  sixty_four_routes_compose_through_eight_groups_into_one_exact_epoch_root \
  -- --ignored --exact --nocapture
```

The `cuda` feature makes the CUDA backend available while CPU-only replay stays
portable. `RISC0_PROVER=local` selects the local prover. Record live
`nvidia-smi` utilization and `nvcc --version` because feature selection alone
does not establish that GPU kernels executed.

RunPod replay at source commit
`6c0594b7e6fdf8fbfebc21d7e3b95ea1126f56c8` generated and verified these
real `Succinct` receipt sets:

- one command: one structural child, one command-aggregation statement, and
  one direct epoch statement in `24.71` seconds;
- eight commands: eight structural children and one direct epoch root in
  `87.49` seconds;
- nine commands: nine structural children, canonical `8+1` group receipts,
  and one aggregated epoch root in `117.54` seconds;
- sixty-four commands: sixty-four structural children, eight canonical group
  receipts, and one aggregated epoch root in `748.41` seconds.

Every receipt was verified in memory under its expected image and exact journal
and was not exported as a release artifact. At source commit
`6aa4333cc6104136bb8a19b6207c53226e3b760b`, isolated non-proving preflight
fixtures accept the valid `1`, `8`, `9`, and `64` shapes and reject invalid
`0`, `9` for the direct path, `8` for the aggregated path, and `65`. No
throughput or release-backed 64-command claim follows from this evidence.
