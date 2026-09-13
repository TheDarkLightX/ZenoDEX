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

`prepare_perps_margin_global_from_frame_v2` is the strict, bounded `ZDPM2\0`
boundary used by the separate margin V2 guest. It admits exactly four canonical
components (assets, margin, global state, request), reruns the joint transition,
checks that each successor fits the next input bound, and returns the existing
two-root statement journal. Rejected frames produce a typed error and no journal.
`examples/receipt_frame.rs` exposes this function as a bounded native test tool.
The Python/Rust suite sends the same lifecycle and rejection cases through both
the typed transport and this strict frame boundary.

Run the bounded checks offline with:

```text
CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-global-v2-target cargo test --offline --locked --manifest-path zk/perps_margin_global_v2/Cargo.toml
CARGO_TARGET_DIR=/tmp/zenodex-perps-margin-global-v2-target cargo run --offline --locked --quiet --manifest-path zk/perps_margin_global_v2/Cargo.toml --example parity
```

The crate reuses the pinned GlobalSettlementABI V1 and V2 path dependencies and
does not alter their guest dependencies or images.
