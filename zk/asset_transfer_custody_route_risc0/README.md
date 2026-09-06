# Asset transfer custody route (ordinary data)

Standalone workspace with one member, `shared`, packaged as
`zenodex-asset-transfer-custody-route-risc0-shared`.

The crate prepares one governed custody-complete `asset_transfer` route from the
unchanged V1 route wire value: the same field layout, closed parser, canonical
encoding, and byte ceiling as the legacy `AssetTransferRouteGuestInputV1`. No
coordinator membership field is added to the wire. The successor is selected
only when the selected `ASSET_TRANSFER` module release, its coordinator release,
and the governed single-lane route all carry the reviewed custody semantic
bundle root as their `specification_root`.

Preparation order:

1. exact governed profile, registries, policy registry, occurrence, and
   coordinator context;
2. `require_asset_transfer_custody_semantics_v1`;
3. the unchanged 8 MiB canonical outer input bound, including typed input;
4. `prepare_asset_lane_custody_coordinator_v1`;
5. `check_asset_transfer_global_allocation_v1`;
6. route journal, `project_route_global_state_v1`, and
   `refine_route_global_economic_state_effects_v1`;
7. module, coordinator and route release journal bounds, each also limited by
   the ABI journal ceiling.

Unknown or mixed specification roots reject at step 2, before any custody
recomputation and before any global check.

A prepared value is ordinary data: the input, the custody coordinator preflight
value, the route journal and its canonical bytes, the projection and refinement
values with their roots, and the `guest_image_id` values copied from the
selected coordinator and route releases as expected image metadata.

Non-claims: this crate has no guest, methods build, host, prover, receipt
verifier callback, pinned image constant, publisher mount, or activation
authority. It validates the supplied profile's selected active releases and
qualifies no image, profile, release, or
publication. The legacy route composer crate is unchanged.

Focused verification:

```bash
rustup run 1.90.0 cargo fmt --manifest-path zk/asset_transfer_custody_route_risc0/Cargo.toml --check
rustup run 1.90.0 cargo test --manifest-path zk/asset_transfer_custody_route_risc0/Cargo.toml \
  --offline --locked -p zenodex-asset-transfer-custody-route-risc0-shared
```

Root verification passes 14 native tests. Two retained regressions first
demonstrated acceptance beyond the selected module journal ceiling and
acceptance of a coherent 9,387,855-byte typed route beyond the outer ceiling.
All three public entries now reject those over-limit values. The large fixture
has valid maximum-length tokens and bounded rows, exactly backed liabilities,
and 951,101/952,015-byte module/coordinator inputs below their 1 MiB ceilings.
This is finite native evidence; it provides no guest execution or universal
implementation refinement. The legacy composer retains its prior behavior.

From the repository root, the Python integration gate replays the native tests
with an installed toolchain and offline dependencies:

```bash
python3 -m pytest -q tests/integration/test_asset_transfer_custody_route_native_v1.py
python3 -B -m experiments.v3_custody_native_route_v1.render_evidence
```

The second command renders this batch's source-pinned declaration only; it
does not run tests or update earlier evidence records. Set `CARGO_TARGET_DIR`
to reuse an existing native cache.
