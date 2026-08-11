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
epoch ELF sha256:
  769f762fd1a77e22d776387aa3d72ad167d4811ca825ca9fbcad2e2e06e98d3f
epoch image root:
  0x5374bab8dbe303f907c281566f6e5cd24a21ddaa4332a783223d1bd572ed40cc

quarantined structural test-leaf ELF sha256:
  e1a5ff0cf71b1c50449b600f1890ad3056b675383d71ea4771d59935a881a9a0
quarantined structural test-leaf image root:
  0x7e8adcaf17f8c07bf7303fde3ee764a624cf40412cb8ad9718bf033eb464e93e
```

These values describe local research artifacts. They are absent from every
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
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
cargo fmt --all -- --check

cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --test real_composition \
  real_succinct_child_assumption_resolves_into_exact_epoch_journal \
  -- --ignored --nocapture

cargo test --locked \
  -p zenodex-global-economic-epoch-risc0-host \
  --test real_aggregation_nine \
  nine_routes_compose_through_two_groups_into_one_exact_epoch_root \
  -- --ignored --nocapture
```

The ignored test generated a real Succinct structural child, used it to prove
both a real command-aggregation receipt and a direct epoch receipt, checked
exact journals and image IDs, and killed a foreign root-image substitution
before proving. It took 217.73 seconds in the recorded final local run. The
three receipts were verified in memory and were not exported as release
artifacts.

The full `9`-command topology additionally generated nine distinct structural
route receipts, canonical `8+1` command-aggregation receipts, and one exact
aggregated epoch receipt in 985.82 seconds. All 12 receipts were verified in
memory under their expected images and journals. The `64`-command boundary has
typed BVA, canonical-partition, substitution, and Fake-receipt evidence; its
full 73-receipt real replay has not been generated. No throughput or
release-backed 64-command claim follows from this evidence.
