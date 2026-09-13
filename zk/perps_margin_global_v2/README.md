# Perps margin/global V2 successor

This standalone crate is a research-only Rust twin of the reviewed Python
margin/global successor.  Its values are pure candidates with no
authentication, settlement, receipt, publication, or runtime authority.

The `examples/parity.rs` JSON-lines program is test transport only.  Each input
line contains complete typed snapshots for either a `perps` transition or an
ordinary `transfer` lane transition.  The program emits canonical successor
states, effects, lifecycle plans, refinement observations, roots, or exact
no-op reject codes.  It accepts at most four MiB per line and closes the outer
operation fields; nested records use the ABI's closed serde shapes.  It is not
a production JSON decoder.

Run the bounded checks offline with:

```text
CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-global-v2-target cargo test --offline --locked --manifest-path zk/perps_margin_global_v2/Cargo.toml
CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-global-v2-target cargo run --offline --locked --quiet --manifest-path zk/perps_margin_global_v2/Cargo.toml --example parity
```

The crate reuses the pinned GlobalSettlementABI V1 and V2 path dependencies and
does not alter their guest dependencies or images.
