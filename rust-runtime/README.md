# ZenoDEX Rust Runtime Core

The **production-candidate** deterministic runtime core for ZenoDEX. Today it is
a **shadow** of the authoritative Python runtime (`../src`): it must agree with
Python bit-for-bit on every golden trace before any surface is promoted to Rust
authority (see `../docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md`).

## Layout

```
rust-runtime/
├── Cargo.toml                      # workspace
├── rust-toolchain.toml             # pinned stable + clippy + rustfmt
└── crates/
    ├── zenodex-runtime-core/       # #![forbid(unsafe_code)] consensus core
    │   └── src/
    │       ├── lib.rs
    │       ├── arith.rs            # explicit checked u128 arithmetic
    │       ├── canonical.rs        # LEB128 / domain-sep / sha256 (mirrors Python)
    │       ├── error.rs            # RejectedReason (thiserror), stable codes
    │       └── fee_router.rs       # route_fee: 4-way split + dust carry
    └── zenodex-runtime-cli/        # bin `zenodex-runtime`: trace replay bridge
        └── src/main.rs
```

## Commands (Phase 2/3 acceptance)

```bash
cd rust-runtime
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

## Cross-language conformance

The CLI is the bridge to the Python reference (no FFI for the MVP):

```bash
# Replay a golden trace and print computed per-step results as JSON.
cargo run -q --bin zenodex-runtime -- replay-fee-trace ../tests/runtime/golden_traces/smoke.json

# From the repo root: diff Rust vs. Python over the same trace.
python3 tools/runtime/rust_shadow_replay.py tests/runtime/golden_traces/smoke.json

# Python/Rust differential test suite (static + 400-case randomized).
pytest tests/runtime/test_fee_router_conformance.py -q
```

## Design rules

* `#![forbid(unsafe_code)]` on every crate (Hard Rule #9).
* No floats, no system time, no randomness, no I/O in transition paths.
* Fixed-width integers (`u128`) with **explicit checked arithmetic** (`arith`);
  overflow becomes a typed `RejectedReason::ArithmeticOverflow`, never a panic
  or silent wrap.
* No panics in public transition functions — `route_fee` returns
  `Result<Accepted, RejectedReason>` (Hard Rule #10).
* Canonical output is built from explicit, ordered byte encodings — never from
  unordered map iteration.

## Dependency rationale (minimal trusted surface)

The consensus core (`zenodex-runtime-core`) keeps its dependency surface tiny:

| Crate | Where | Why |
|-------|-------|-----|
| `sha2` | core | Audited, deterministic SHA-256. Preferred over a hand-rolled hash (lower bug risk for consensus). |
| `thiserror` | core | Typed errors with derived `Display`. No runtime behavior. |
| `hex` | core | Lowercase hex for `0x`-prefixed digests. |
| `proptest` | core (dev) | Property tests (conservation / no-panic). |
| `serde`, `serde_json` | **cli only** | Trace I/O. `arbitrary_precision` preserves integers larger than `u64` (the corpus includes `2**112`). |

`serde` is intentionally **not** used inside the core transition logic: canonical
encoding is explicit byte assembly (`canonical.rs`), not derive-driven, so the
on-the-wire format is auditable and decoupled from struct layout.

`Cargo.lock` is committed for reproducible builds.

## Determinism notes

State roots and receipt hashes are `0x`-prefixed SHA-256 over LEB128-encoded,
domain-separated, explicitly-ordered byte pre-images. They are identical across
platforms and Python versions, and identical between this crate and
`src/state/canonical.py`. See `../docs/runtime/GOLDEN_TRACE_FORMAT.md`.
