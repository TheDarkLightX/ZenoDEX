# Custody-complete ASSET coordinator native candidate

This shared crate composes the custody-complete ASSET transfer module into the
existing single-module lane coordinator. Its prepared value owns the complete
module and lane results and both canonical journals. This advances the native
W04/W10 implementation surface; it does not close either whole-program task.

The input retains the existing V1 fields and wire schema. The separately named
Rust input and entry points select the custody-complete calculation. Exactly one
custody-module preflight runs, followed by one lane composition. The module's
validated result and bounded canonical journal are reused. The coordinator
validates its lane result and bounds the lane journal.

Raw admission checks the 1 MiB ceiling before decoding, rejects unknown fields,
requires exact canonical bytes before domain validation, and returns typed
errors without a prepared result. Module rejection codes and coordinator
binding rejection codes remain distinct. Typed preparation performs domain
validation; serialized input size is enforced by the canonical encoder and raw
entry point. There is no process, storage, callback, or effect application here.

## Authority and version boundary

Inputs, prepared results and supplied release IDs are ordinary data. Preparation
does not establish that a release ID designates this calculation. The fixture
uses synthetic contexts and explicitly carries `authority=NONE`.

The new crate has no measured guest, child-image pin, receipt, release-profile
registration or publisher consumer. Before mounting it, the release-aware
adapter must select the reviewed semantic family from a closed normative
specification-root map, bind the exact active profile and release, and verify
the measured image and exact journal. Unknown semantic families must reject.
The specification root must be independent of the implementation that consumes
it; a descriptive semantic-version string cannot select semantics.

The legacy coordinator and its image pin remain intact. With zero custody,
identical synthetic inputs produce identical journal bytes in both native
calculations. With nonzero custody, the new coordinator accepts the complete
physical totals and the legacy coordinator rejects its account-only module
result with `CONSERVATION_STATE_MISMATCH`. Neither comparison transfers receipt
authority between releases.

## Evidence and replay

Run from the repository root with the existing pinned offline toolchains:

```bash
python3 tools/render_asset_lane_custody_coordinator_v1_golden.py --check
python3 -m pytest -q tests/core/test_asset_lane_custody_coordinator_golden_v1.py tests/core/test_asset_transfer_lane_module_custody_v1.py
python3 tools/check_asset_lane_custody_coordinator_mutants_v1.py
cd zk/asset_lane_custody_coordinator_risc0
CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=../global_settlement_abi_v1/target cargo +1.90.0 test --workspace --locked --offline -j 2
CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=../global_settlement_abi_v1/target cargo +1.90.0 clippy --workspace --all-targets --locked --offline -j 2 -- -D warnings
cargo +1.90.0 fmt --all -- --check
```

Omit `--check` from the renderer command to regenerate the Python fixture. The
renderer checks transfer balances against an independent integer-account
calculation and physical totals against account-plus-custody sums. It retains
complete Python module/lane values, canonical input/journal bytes and source
hashes for Rust comparison.

Eight Rust tests and 25 Python tests passed on the initial candidate. The Rust
suite covers 11 full Python lane vectors: custody boundaries through u128 max,
high absolute balances with small signed deltas, fee-owner aliases, and foreign
asset custody. It also consumes the retained seven accepted and three rejected
module vectors, checks independent context failures, malformed/canonical input
precedence, input-size neighbors and projection overflow.

The stateful fixture uses two distinct transfer occurrences with a rejected
zero-amount attempt between them. Full post-to-pre state and lane-root
continuity, unchanged custody and a repeated pure preparation are checked.
This is a deterministic core history; datastore replay consumption, concurrent
publication and committed retries require their separate shell evidence.

The mutation checker compiles each altered implementation before running an
unchanged test. Substituting the legacy module must fail full Python lane
parity; omitting canonical-byte equality must fail the raw-boundary test.
Compilation failures do not count as mutation kills.

These are native execution and differential results. Guest compilation,
cryptographic composition, source-to-formal refinement, authenticated restart,
publication and whole-program value safety remain open.
