# Fuzz targets (advisory — requires nightly)

`cargo-fuzz` (libFuzzer) targets for the runtime kernels. This crate is
**excluded from the stable workspace** (`rust-runtime/Cargo.toml` `exclude`) and
needs a **nightly** toolchain plus `cargo-fuzz`, neither of which is available in
the environment that authored these files — so the corpora here have **not** been
run yet. The always-on, stable-toolchain robustness net lives in
`../crates/zenodex-runtime-core/tests/robustness.rs` (proptest, ~4000 adversarial
cases per kernel); these targets let a real libFuzzer campaign run when nightly
is present, which is the Phase 9 "fuzzing has run for that module" gate.

## Targets

| Target | Kernel | Property |
|--------|--------|----------|
| `fee_router` | `route_fee` | no panic; per-(source,asset) conservation on accept |
| `replay_guard` | `admit` | no panic; accept iff nonce == last+1; reject is a no-op |
| `balance_kernel` | `credit`/`transfer` | no panic; canonical state |
| `zusd` | `step` | no panic; supply conservation (free + sp == debt) |
| `burn_receipts` | `verify_rails` | no panic; supply + accumulator equalities on accept |
| `cpmm_swap` | `swap_exact_in/out` | no panic; constant-product k never decreases |

## Run

```bash
rustup toolchain install nightly
cargo install cargo-fuzz
cd rust-runtime
cargo +nightly fuzz run fee_router -- -max_total_time=60
cargo +nightly fuzz run zusd        -- -max_total_time=60
# ... one per target; -runs=N or -max_total_time=S to bound a campaign.
```

A crash writes a reproducer under `fuzz/artifacts/<target>/`; replay it with
`cargo +nightly fuzz run <target> fuzz/artifacts/<target>/<crash-file>`.

## Promotion note

These targets assert the *same* invariants as the differential and the
semantic-invariant tests, but over machine-mutated byte inputs. A clean campaign
(no crashes for a bounded run) on each target is the remaining Phase 9 evidence
item for the kernels; see `../../docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md`.
