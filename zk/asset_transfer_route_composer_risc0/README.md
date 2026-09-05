# Asset transfer route composer V1

This isolated route proves the existing accepted asset-transfer transition,
coordinator journal and full global before/after relation. It preserves the
existing route journal format. The private input includes the exact profile,
module/coordinator/route registries, governed asset and fee policies, occurrence,
module input, coordinator context and both complete global states.

The shared preflight checks those bindings, derives the module and lane result,
applies the restricted asset allocation relation, and replays the existing
global state projection and exact state/effect refinement. It derives the
public full-state roots from those states. The restricted relation supports one
active ASSET_TRANSFER lane, unchanged other lanes and historical roots, exact
claimant continuity and one replay insertion. Other supported state categories
remain constrained by that relation; this does not complete other lanes.

The guest verifies the exact coordinator image selected by the disclosed
profile registry and the exact derived coordinator journal. The host additionally
measures its compiled route and coordinator ELFs and checks their IDs against
that selection. The selected coordinator verifies its fixed module image.
Changing an image requires a new release and profile identity. A disclosed
profile, prepared value or receipt confers no publication or signer authority.

The private frame is a little-endian u32 length and canonical JSON, bounded at
8 MiB before allocation. Typed closed fields, exact reencoding and the existing
bounded ABI decoders reject ambiguous or excessive inputs. The standalone V1
receipt endpoint uses the shared cryptographic checker, this compiled route
image and canonical native JSON receipts. It has no fallback image or codec.

## Reproduction

Use an authorized remote prover for heavy builds. The lock preserves all 516
registry pins from the reviewed ROOT proving graph; offline `cargo metadata
--format-version 1` only replaces workspace package entries. Existing compatible
RISC0 3.0.6 dependencies and three vendored patches are reused. The optional
`cuda` feature enables the SDK prover, and verification builds omit it.

```sh
RISC0_SKIP_BUILD=1 cargo test --locked --release -p zenodex-asset-transfer-route-composer-risc0-shared -p zenodex-asset-transfer-route-composer-risc0-host
RISC0_SKIP_BUILD=1 cargo clippy --locked -p zenodex-asset-transfer-route-composer-risc0-shared -p zenodex-asset-transfer-route-composer-risc0-host --all-targets -- -D warnings
```

Set `ZENODEX_ROUTE_REFERENCE_OUTPUT` when running the shared tests to export
the complete input, exact journals, effect plan and Rust relation roots. From
the repository root run `python3
zk/asset_transfer_route_composer_risc0/check_reference.py <reference.json>`.
That checker independently reconstructs the Python typed values, compares both
relation roots, checks the transfer's integer arithmetic and requires rejection
of a conserved but misattributed balance change. It grants no authority.

The ignored `real_transfer` test exports a genuine module, coordinator and route
proof. `ZENODEX_ASSET_ROUTE_INPUT` selects an exact canonical input file; the
host preflight validates it before proving, so a new isolated profile requires
no source edits or recompilation. Without that file, a test-only fixture reuses
the existing USD policy and transfer scenario. Optional
`ZENODEX_ASSET_ROUTE_ROOT_IMAGE` and `ZENODEX_ASSET_ROUTE_PRE_HEIGHT` set its root
image and predecessor height, with height zero as the exporter default. The
other eleven lanes remain nonaccepting SHADOW entries. Its evidence labels are
synthetic fixture data and do not attest real deployment readiness.

```sh
RISC0_DEV_MODE=0 RISC0_PROVER=local cargo test --locked --release -p zenodex-asset-transfer-route-composer-risc0-host --features cuda --test real_transfer real_asset_transfer_module_coordinator_route_with_exact_export -- --exact --ignored --nocapture
```

Set `ZENODEX_ASSET_ROUTE_EVIDENCE_DIR` to retain exact input, receipts, journals,
ELFs and roots. Retain source/lock hashes and actual compiler path/hash with the
logs. This proof does not authenticate the signer, certify the predecessor
allocation partition, establish store provenance or authorize publication.
Those obligations remain with initialization and the isolated verifier/publisher
boundary. No live authority or balance migration is provided here.
