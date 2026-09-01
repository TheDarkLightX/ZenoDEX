---
title: 2026-08-31-risc0-3-0-6-source-pinned-patches
type: note
permalink: autonomous-tau-dex-review/docs/dependency-approvals/2026-08-31-risc0-3-0-6-source-pinned-patches
---

# 2026-08-31 RISC0 3.0.6 source-pinned patches

## Exact restage subject

- Parent commit:
  `b6655bf0c7ef7e099c9430485010baf4df15fd65`.
- Primary patch donor:
  `8b589e373f2ff6018d2f952b0a104f4f9f28a438`.
- That donor supplied the dependency-patch implementation but omitted four
  ignored files from its tracing source capture. This restage restores the
  following files from the independently pinned cached upstream
  `tracing-subscriber` 0.3.22 extraction:
  - `src/filter/env/builder.rs`;
  - `src/filter/env/directive.rs`;
  - `src/filter/env/field.rs`;
  - `src/filter/env/mod.rs`.
- The restage preserves the parent's O-008 bounded-core commits and changes
  only the economic-initial-state workspace patch and selected lock.
- Donor edits to the historical O-008A blocker generator/tests and to RISC0
  receipt-admission/support tests are deliberately excluded. Those artifacts
  belong to different source subjects and are not prerequisites for this
  dependency-selection repair.

## Change

- Added closed local source trees for `rzup` 0.5.2, `ark-relations` 0.5.1,
  and unmodified `tracing-subscriber` 0.3.22.
- Scoped the Cargo patch to `zk/economic_initial_state_risc0`.
- Removed `rsa` from the selected lock by making signature support optional in
  the `rzup` build-only profile. Install and publish profiles retain signature
  support.
- Kept the upstream feature-dependent `rzup` test suites behind their complete
  install-and-publish test profile so the no-feature build-only profile can run
  its dedicated fail-closed signature regression without importing unrelated
  CLI, network, archive, or publishing dependencies.
- Raised the Arkworks tracing adapter to the fixed 0.3 API and changed
  `Layer::new_span` to `Layer::on_new_span`.

## Why

RISC0 3.0.6 is the current pinned release for this proof workspace. Its stock
lock selected `rsa` 0.9.10 under `rzup` and `tracing-subscriber` 0.2.25 under
`ark-relations`. The RustSec database reports `RUSTSEC-2023-0071` for the RSA
path with no patched RSA release and `RUSTSEC-2025-0055` for
`tracing-subscriber`, fixed in 0.3.20 and later.

The RISC0 build dependency selects `rzup` without default features and only
needs installed-toolchain discovery. Removing RSA from this exact feature
graph avoids carrying a vulnerable cryptographic implementation that the build
does not use. The disabled signature surface rejects verification and private
key construction. The standard install and publish surfaces continue enabling
the upstream signature implementation.

## Determinism and pinning

- Cargo resolves all three patched packages through repository-relative paths.
- The selected workspace lock contains no `rsa` package and exactly one
  `tracing-subscriber` package at 0.3.22.
- The deterministic checker binds every regular vendored file, executable bit,
  size, SHA-256 digest, package identity, license, repository, and upstream VCS
  commit. It records crates.io archive checksums as provenance metadata. The
  archive files were not rehashed during this exact restage.
- A path-scoped `.gitattributes` rule disables Git whitespace rewriting and
  whitespace-error reporting only for this vendored subtree. The source-tree
  hash continues to bind inherited upstream whitespace byte for byte.
- Anchored `.gitignore` exceptions retain the four upstream Rust sources under
  `tracing-subscriber-0.3.22/src/filter/env`; the deterministic checker binds
  all 86 tracing package files to exact committed-tree modes and blob
  identities. The checker reads the literal named commit through `ls-tree` and
  `cat-file`; working-tree and index bytes are outside its authority.
- The four restored paths are explicitly reported under the complete 86-file
  tracing tree identity. That identity also binds package metadata, upstream
  VCS commit `cc44064b3a41cb586bd633f8a024354928e25819`, and tree SHA-256
  `0e36c6b8e465689117c83fc2dd29acf7b846a9f4a6133730ef61d3c328aa2a12`.
- The unmodified tracing source is local so the qualification build can run
  with `CARGO_NET_OFFLINE=true`.

## License and size

- `rzup`: Apache-2.0.
- `ark-relations`: MIT or Apache-2.0.
- `tracing-subscriber`: MIT.
- The closed source payload contains 124 files and 1,440,861 bytes before this
  approval note and vendor README.

The source files retain upstream notices and license files where the packages
supplied them. `rzup` source files contain the upstream Apache-2.0 notice and
its package metadata declares Apache-2.0.

## Security and authority impact

The selected lock is expected to produce zero RustSec vulnerabilities. Three
informational unmaintained-package notices remain in the wider graph and must
remain visible in qualification evidence.

That expectation is established here from the deterministic selected-lock and
vendored-source checker. A current `cargo audit --no-fetch` result remains a
separate required qualification artifact.

The cached `tracing-subscriber` `.crate` archive was absent from this exact
restage, so its recorded archive checksum is not a restage-time rehash claim.

This dependency decision is research build infrastructure. It does not qualify
the host, establish proof validity, change an economic transition, mount a
verifier, authorize settlement, or grant release or value-movement authority.

## Validation

Required evidence includes:

```bash
subject="$(git rev-parse HEAD)"
python3 tools/check_o008a_risc0_dependency_patch_v1.py --subject "$subject"
O008A_TEST_SUBJECT="$subject" pytest -q \
  tests/test_o008a_risc0_dependency_patch_v1.py
cargo audit --json --no-fetch \
  --file zk/economic_initial_state_risc0/Cargo.lock
RISC0_SKIP_BUILD=1 cargo +1.90.0 test --locked --workspace \
  --manifest-path zk/economic_initial_state_risc0/Cargo.toml
```

O-008A additionally requires a clean isolated real guest-image build, artifact
hashes, a real proof, separate canonical receipt replay, exact toolchain and
resource receipts, and independent exact-subject review.

## Removal alternative

Adopt a reviewed upstream RISC0 release whose selected lock removes both
advisory paths, then rebuild every affected guest and proof receipt. Delete the
local source patches only after the new lock, image IDs, parity evidence, and
release evidence pass against one exact promotion subject.
