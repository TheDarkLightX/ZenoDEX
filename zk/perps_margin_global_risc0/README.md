# Margin/global V2 execution and receipt tools

This guest reruns the existing pure joint margin transition. Its input is a
u32LE frame length followed by exactly one `ZDPM2\0` frame and EOF. Each of the
four canonical JSON components is bounded to 1 MiB. The unchanged journal is:

```json
{"input_root":"0x...","refinement_root":"0x...","schema":"zenodex/perps-margin-global-statement/v2"}
```

The roots bind the complete existing statement and refinement. They do not
grant profile, writer, finality, withdrawal, or publication authority. The
current-store publisher must independently admit the expected image, exact
journal, authenticated command, predecessor and active authority.

The SDK is pinned to RISC0 3.0.6 with `disable-dev-mode` on the host. All external
package versions reuse the current custody workspace's lockfile; no additional
external package is required. The lockfile was seeded from
`../asset_lane_custody_global_risc0/Cargo.lock` and updated by the offline native
test command. Rust 1.97.1 is the native host toolchain used for this build; the
installed `risc0` toolchain supplies the zkVM target. No placeholder guest is
supported. `RISC0_SKIP_BUILD` makes the build fail.

From the repository root, with a sufficiently sized build filesystem:

```bash
cargo +1.97.1 test --offline --locked --manifest-path zk/perps_margin_global_risc0/Cargo.toml
RISC0_BUILD_LOCKED=1 cargo +1.97.1 test --offline --locked --manifest-path zk/perps_margin_global_risc0/Cargo.toml --features compiled-guest
RISC0_BUILD_LOCKED=1 cargo +1.97.1 build --offline --locked --manifest-path zk/perps_margin_global_risc0/Cargo.toml --features compiled-guest --bins --examples
```

The first command tests bounded transport and receipt decoding without building
a guest. The feature builds the real guest and fixed verifier/prover binaries.
Native test success alone is not receipt qualification.

The measured execution candidate image is
`0x0c7b609c4a86d126d4de393e649f2551a191d3aaf87d5ddc217f659fdcb08204`.
Its host image test runs with `compiled-guest` and has no proving-dependent
ignore gate. The actual execution/negative-verifier suite is opt-in:

```bash
ZENODEX_MARGIN_EXECUTOR="$CARGO_TARGET_DIR/debug/examples/execute_margin_frame_v2" \
ZENODEX_MARGIN_R0VM="$(command -v r0vm)" \
python3 -m pytest -q tests/integration/test_perps_margin_real_guest_v2.py
```

Retain executable hashes with each run. The test expects the fixed verifier at
`$CARGO_TARGET_DIR/debug/verify_margin_receipt_v2`; missing configured binaries
fail. An entirely unconfigured run skips and supplies no execution evidence.

- `verify_margin_receipt_v2` takes the existing `ZDXRV1RQ` protocol on stdin. It
  binds the supplied image to its compiled ELF, requires an exact canonical JSON
  receipt, exact journal, Succinct kind, successful cryptographic verification
  and no unresolved assumptions. It uses the shared measured verifier endpoint.
- `prove_margin_receipt_v2 /absolute/path/to/r0vm` reads the bounded outer frame
  from stdin and emits a canonical receipt only after verifying its image, kind
  and journal. It explicitly selects the SDK's external IPC prover. Prover
  selection does not depend on `RISC0_PROVER`. Run full proving on the authorized
  proof host. Subprocess containment remains an operator responsibility.
- The `execute_margin_frame_v2` example takes the same r0vm argument and input.
  It executes the real guest and prints its journal for differential testing,
  without creating or verifying a cryptographic receipt. It deliberately omits
  native semantic preflight so malformed inner frames reach the guest.

The provisional session ceiling is 16,777,216 cycles. It does not establish that
all valid maximum states fit. Execution-cycle enforcement assumes the pinned
honest IPC server; receipt verification provides economic checking rather than
resource isolation. A compromised proposer process or operating system is
outside these standalone tools' authority boundary.

AS02 remains open until genuine receipts for the rebuilt image pass through the
existing isolated publisher with wrong-image, wrong-journal/context, fake,
malformed, stale-head and unavailable-verifier controls. No deployment, live
balance migration or authority activation is included.
