# PERPS_MARKET margin lane coordinator RISC0 guest

This research-only workspace recursively verifies the exact pinned perps-margin
module receipt before committing one canonical PERPS_MARKET lane journal. The
host accepts only real Succinct child receipts, binds the exact child image and
journal, adds the verified receipt as an assumption, and rejects development
mode, placeholders, noncanonical receipt bytes, and mismatched journals.
The host caps the child execution at 4,194,304 cycles and the recursive lane
execution at 8,388,608 cycles before proving.

Fast replay uses placeholder coordinator method constants that every proving and
verification entry point rejects:

    RISC0_SKIP_BUILD=1 cargo test --locked --workspace
    RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
    cargo fmt --all -- --check

## Real recursive replay evidence

The CPU replay completed on RunPod on 2026-08-25 with an AMD EPYC 9354 host,
RISC Zero 3.0.6, host Rust 1.90.0
(`1159e78c4747b02ef996e55082b704c09b970588`), and RISC Zero guest Rust
1.97.0-dev (`e638c6cfea1eff5fbbb24a27e60538e3760d21b8`). It ran without
`RISC0_DEV_MODE`:

    RUST_LOG=info cargo test --locked \
      -p zenodex-perps-margin-lane-coordinator-risc0-host \
      --test real_composition \
      real_module_receipt_composes_into_exact_perps_margin_lane_journal \
      -- --ignored --nocapture --exact

The test produced a real Succinct child receipt, recursively resolved it in the
lane proof, then exercised wrong-journal, wrong-image, noncanonical-receipt, and
pinned-verifier controls. Result: 1 passed, 0 failed. The child proof took
567.335547795 seconds and the full recursive proof took 1612.162645708 seconds.
The preserved log SHA-256 is
`067322ae052dd0449efc4ee965f1deb4272cfe472871e26b42a5b5d312713a8e`.

The coordinator image words are
`[4041762456, 2955254071, 1350845632, 143171303, 2674396660, 1609919496,
4059712571, 1345619922]`, corresponding to image root
`0x9866e8f0379925b0c0448450e79e8808f40d689f086cf55f3b4cfaf1d2873450`.
The 719,764-byte guest ELF had SHA-256
`f0ecd2d6e4816908213b6ba45992ae89890a836469cafeed44d0cf5dca18e1a4`;
the 752,188-byte embedded method had SHA-256
`59f10d36439aeaa69948406ff319694a0c68fccfe3dbeb3ae91a70e7e546a029`.
The separate missing-child-assumption real test also passed, establishing that
the coordinator cannot produce this lane receipt without resolving the exact
child proof.

This proof covers one bounded margin deposit, withdrawal, or close transition
and its single-module lane composition. It does not prove the complete perps
lifecycle, route or epoch composition, mounting, durable publication, or
production authority.
