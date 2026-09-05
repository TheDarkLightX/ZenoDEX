# Actual Rust asset-transfer arithmetic qualification

This packet checks two existing private functions in
`zk/global_settlement_abi_v1/src/asset_transfer.rs`. It appends Kani harnesses to
a temporary copy of the complete source-pinned ABI crate. Every original file
is verified before copying; baseline instrumentation preserves every original
source byte as an exact prefix. The complete addition and each deliberate
mutant are retained as separate diffs. Production source is never instrumented.

The proof obligations are:

1. For every `u128 current` and `i128 delta`, `apply_delta` returns the exact
   inverse-equation result when the debit is funded or credit fits. Otherwise
   it returns exactly `INSUFFICIENT_BALANCE` or `BALANCE_OVERFLOW` according to
   the sign. The minimum signed delta is included.
2. For every `u128 left` and `u128 right`, `checked_negative_sum` succeeds
   exactly when their mathematical sum is at most `2^127`, returning its
   negative value, including `i128::MIN` at equality. All other inputs return
   exactly `EFFECT_DELTA_OVERFLOW`.

The harnesses use no assumptions or reduced integer bounds. Their assertions
express inverse equations and a subtraction-based admissible domain, without
replacing the implementation by a copied arithmetic model. Explicit zero,
minimum, maximum and one-atom neighbors accompany the universal checks.
Unwinding assertions remain enabled. The three retained semantic mutants are
wrapping debit, wrapping credit and omission of the signed-minimum case.
Each must fail the corresponding unchanged harness.

## Toolchain and reproduction

The selected verifier is [Kani 0.67.0](https://github.com/model-checking/kani/releases/tag/kani-0.67.0).
Its [pinned toolchain](https://github.com/model-checking/kani/blob/kani-0.67.0/rust-toolchain.toml)
is `nightly-2025-11-21`. The official installation process supports
[an isolated KANI_HOME](https://model-checking.github.io/kani/install-guide.html).
Keep `RUSTUP_HOME`, installation output, Cargo target and proof subjects in a
dedicated remote job directory. Do not change the RISC0 toolchain defaults.
Retain the official release metadata, downloaded bundle checksum, actual
compiler and solver versions/hashes, commands and complete outputs.

```sh
cargo install --locked --version 0.67.0 --root "$KANI_JOB/install" kani-verifier
cargo kani setup --use-local-bundle "$KANI_JOB/release-bundle.tar.gz"
python3 formal/kani/asset_transfer_arithmetic_v1/prepare.py --repo . --output "$KANI_JOB/baseline"
cd "$KANI_JOB/baseline/zk/global_settlement_abi_v1"
cargo kani --lib --harness apply_delta_full_width_exact_outcome
cargo kani --lib --harness checked_negative_sum_full_width_exact_outcome
```

Create each mutant with `prepare.py --mutant <name>` in a separate fresh
directory and run its corresponding harness. A build error, timeout or unknown
result is inconclusive, never a mutant kill or successful proof.

These are actual-source finite-width arithmetic obligations under Kani's pinned
nightly compiler and CBMC model. They do not prove the RISC0 1.97 compiler,
ELF/code-generation equivalence, complete crate refinement, asset authorization,
allocation partition completeness, publication, durability or production safety.
Source identity and stronger semantic invariants must be connected separately.

## Retained result, 2026-09-05

Both universal harnesses passed: 102 checks each, zero failed. Verification
times were 1.0306609 seconds for `apply_delta` and 0.81480986 seconds for
`checked_negative_sum`, after compilation. All three independently prepared
mutants produced semantic verification failures with exit code 1; no build
error or timeout was counted as a kill. The complete 153-file source inventory
was rechecked after every run, including the unchanged Cargo lock and exact
instrumented-module hash. A separate preparation control rejected an altered
source module before creating an output directory.

The actual checker stack was Kani 0.67.0, Rust
`1.93.0-nightly (53732d5e0 2025-11-20)`, LLVM 21.1.5 and CBMC 6.8.0 with its
default CaDiCaL solver. The downloaded Kani release bundle SHA-256 matched the
digest in the official GitHub release metadata:
`3b5f7afd3b51603ee720db7bc1bc4fe46b5a4f5d36daad9939c4b4c658b51ac0`.
The exact original arithmetic source SHA-256 is
`78d28167d5360c22b3749812bdab224fe1a2b7888899db363b5dbc5d981dbcb0`;
the appended harness SHA-256 is
`1229ba80e6ef59423174ca8098d41f14b28c8fde5c8c1400c1c33797c9c7d92e`.

The compact evidence archive SHA-256 is
`8e8015e5c1eaa8ab2cc126cdeedad18cca35833007cd411c39030a96e8b167ff`.
It contains the original source packet, full successful and failing logs,
official release metadata, tool versions and executable hashes, each exact
instrumentation diff, and the post-run source audit. The separately preserved
official tool bundle can be fetched again and checked against the digest above.
