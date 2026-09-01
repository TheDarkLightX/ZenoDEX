# RISC0 3.0.6 source-pinned dependency patches

This directory contains the closed build-time dependency patch selected for
the O-008A economic-initial-state RISC0 workspace. It resolves two advisories
that cannot both be removed by changing the existing lock alone:

- `RUSTSEC-2023-0071` through `risc0-build -> rzup -> rsa`;
- `RUSTSEC-2025-0055` through
  `risc0-zkvm -> risc0-groth16 -> ark-relations -> tracing-subscriber`.

The patch is scoped to
`zk/economic_initial_state_risc0/Cargo.toml`. It grants no runtime,
verification, settlement, release, or value-movement authority.

## Source identities

| Package | Version | Recorded crates.io archive SHA-256 | Upstream VCS commit | License |
| --- | --- | --- | --- | --- |
| `rzup` | 0.5.2 | `96909a7ea8fdf7e18da727d7facbc43eea8a4f77635e7ec75a69794dede16fb6` | `8c215e2f4ccdd935f0517bf05d90f1ae032840a9` | Apache-2.0 |
| `ark-relations` | 0.5.1 | `ec46ddc93e7af44bcab5230937635b06fb5744464dd6a7e7b083e80ebd274384` | `b34f11d670c2667de3eda6e33daed8027f35043e` | MIT/Apache-2.0 |
| `tracing-subscriber` | 0.3.22 | `2f30143827ddab0d256fd843b7a66d164e9f271cfa0dde49142c5ca0ca291f1e` | `cc44064b3a41cb586bd633f8a024354928e25819` | MIT |

The archive checksums above are provenance metadata recorded before this exact
restage. The archive files were not rehashed during the restage. Registry
extraction marker `.cargo-ok` and upstream `Cargo.lock` files are excluded.
The package metadata, upstream license files where supplied, and
`.cargo_vcs_info.json` identities are retained.

## Changes from upstream

`rzup-0.5.2` has four changed files:

- `Cargo.toml` makes `rsa` optional, introduces the `signature` feature, and
  makes both `install` and `publish` retain that feature.
- `src/distribution/signature.rs` preserves the upstream RSA implementation
  when `signature` is enabled. When it is disabled, parsing may retain opaque
  signature bytes, while private-key construction and verification reject with
  `signature feature not enabled`.
- `src/lib.rs` and `src/components.rs` keep upstream feature-dependent tests
  behind the complete install-and-publish test profile. This leaves the
  no-feature build-only profile able to execute its dedicated fail-closed
  signature regression without enabling unrelated CLI, network, archive, or
  publishing dependencies.

The selected RISC0 3.0.6 build graph uses `rzup` with default features
disabled. It performs local toolchain discovery and does not need install or
publish signature operations. The no-signature implementation exists to keep
that API compilable and fail closed. Building `rzup` with its default features
still enables the upstream RSA path and is outside the selected clean lock.

`ark-relations-0.5.1` has two changed files:

- `Cargo.toml` raises the optional `tracing-subscriber` compatibility floor
  from `0.2` to `0.3.20`.
- `src/r1cs/trace.rs` implements the 0.3 `Layer::on_new_span` method name.

`tracing-subscriber-0.3.22` is an unmodified, independently pinned cached
upstream extraction. The primary patch donor omitted four files because an
inherited `env/` ignore rule hid them. This restage restores these exact cached
upstream paths:

- `src/filter/env/builder.rs`;
- `src/filter/env/directive.rs`;
- `src/filter/env/field.rs`;
- `src/filter/env/mod.rs`.

The checker explicitly lists those paths and binds them inside the complete
86-file tracing tree, whose package identity, upstream VCS commit, and tree
SHA-256 are independently pinned. The cached `.crate` archive was absent, so
the recorded archive checksum is not a rehash claim for this exact run. The
closed extracted tree remains available for the offline selected workspace.

## Validation

Run:

```bash
subject="$(git rev-parse HEAD)"
python3 tools/check_o008a_risc0_dependency_patch_v1.py --subject "$subject"
O008A_TEST_SUBJECT="$subject" python3 -m pytest -q \
  tests/test_o008a_risc0_dependency_patch_v1.py
cargo audit --json --no-fetch \
  --file zk/economic_initial_state_risc0/Cargo.lock
RISC0_SKIP_BUILD=1 cargo +1.90.0 test --locked --workspace \
  --manifest-path zk/economic_initial_state_risc0/Cargo.toml
```

The deterministic checker owns the exact source-tree identities, workspace
patch mapping, feature policy, fail-closed stubs, selected lock versions, and
absence of `rsa` from that lock. A clean dependency check remains insufficient
for O-008A host qualification. The real guest image must also be rebuilt and a
real receipt must be proved and independently replayed against the exact
source subject.

## Removal

Remove this patch when an adopted RISC0 release provides a reviewed lock that
removes the RSA advisory path and uses a fixed tracing-subscriber release.
That upgrade requires new guest image IDs, proof receipts, cross-language
parity evidence, and exact-subject review. Reverting to the original RISC0
3.0.6 lock reopens both advisories and must fail the dependency gate.
