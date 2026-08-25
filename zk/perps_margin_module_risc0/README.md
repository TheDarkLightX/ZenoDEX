# PERPS_MARKET margin module RISC0 guest

This research-only workspace proves the bounded SHADOW perps-margin functional
core. The guest decodes one canonical PerpsMarginLaneModuleInputV1, executes the
deterministic Rust transition, rejects typed economic denials, and commits the
exact canonical LaneModuleTransitionJournalV1.

Fast replay uses placeholder method constants that all proving and verification
entry points reject:

    RISC0_SKIP_BUILD=1 cargo test --locked --workspace
    RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
    cargo fmt --all -- --check

A real recursive replay completed on RunPod on 2026-08-25 with RISC Zero 3.0.6,
host Rust 1.90.0, and RISC Zero guest Rust 1.97.0-dev. The coordinator test
generated this child as a real Succinct receipt, checked its exact journal and
image, and supplied it as the coordinator assumption.

The replay pinned the module image words to
`[695572787, 3504753096, 3337513134, 2865730872, 3839057979, 1870156240,
2829371707, 1610587060]`, corresponding to image root
`0x33997529c849e6d0ae68eec63895cfaa3b60d3e4d051786f3bc9a4a8b49bff5f`.
The 497,704-byte guest ELF had SHA-256
`78cb0ad79c919dc9500cf70fbbbe29f1d57bc75714a18696500355ce7969e135`;
the 530,128-byte embedded method had SHA-256
`89906d9380eca757dae8bd76888854623a512e17a421a9a5e9c36e99c8c5bfce`.
The child proof took 567.335547795 seconds within the complete recursive replay
and remained below the 4,194,304-cycle release ceiling.

This proof covers the deterministic margin deposit, withdraw, and close
transition language in GlobalSettlementABI V1. It does not prove
authentication, Oracle truth, governed market-policy selection, complete perps
lifecycle semantics, route composition, epoch settlement, mounting, durable
publication, or production authority.
