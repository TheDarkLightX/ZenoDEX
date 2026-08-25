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

A real replay must build the pinned RISC0 3.0.6 method, produce a Succinct
receipt, and verify the exact image and journal. That replay is deferred to
RunPod because local sustained proving exceeds the workstation heat budget.

This proof covers the deterministic margin deposit, withdraw, and close
transition language in GlobalSettlementABI V1. It does not prove
authentication, Oracle truth, governed market-policy selection, complete perps
lifecycle semantics, route composition, epoch settlement, mounting, durable
publication, or production authority.
