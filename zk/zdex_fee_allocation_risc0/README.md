# ZDEX fee-allocation RISC0 guest

This research-only workspace is a source-level proof candidate for one
deterministic ZDEX protocol-fee allocation transition. The guest consumes canonical
`ZDEXFeeAllocationGuestInputV1` bytes, calls the same Rust transition as the
host, and commits the exact canonical `ZDEXFeeAllocationOccurrenceV1` only
when the transition accepts. Typed rejection aborts proving and yields no
receipt journal.

The occurrence binds the chain, deployment, profile, writer epoch, allocation
route, authorized buy-and-burn route, tokenomics module release, command
occurrence, fee policy, fee asset, charged amount, destination allocations,
carried residue, pre/post lane roots, and effect-plan root. The governed host
admission path independently selects the profile and image, recomputes the
transition, and requires an exact `Succinct` receipt.

Fast replay:

```bash
RISC0_SKIP_BUILD=1 CARGO_INCREMENTAL=0 CARGO_PROFILE_TEST_DEBUG=0 \
  cargo test --locked --workspace
RISC0_SKIP_BUILD=1 CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0 \
  cargo clippy --locked --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Real-proof smoke target, with no recorded receipt yet:

```bash
cargo test --locked -p zenodex-zdex-fee-allocation-risc0-host \
  --test real_proof \
  real_zdex_fee_allocation_proves_the_exact_occurrence_journal \
  -- --ignored --nocapture
```

This workspace is unmounted. No active economic profile selects its image and
no settlement writer accepts its output. A real receipt would prove only this
exact fee-allocation leaf transition. It would not establish purchase
execution, ZDEX burn, route composition, epoch aggregation, durable
publication, migration, whole-economy safety, or production readiness.

Promotion also requires a real receipt to pass through the governed economic
profile binder and ABI receipt verifier. That integration replay must include
wrong profile, authority epoch, route, module, image, journal, and serialized
fake-receipt substitutions. The current ignored smoke target exercises only the
pinned RISC0 adapter.
