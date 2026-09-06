# Custody successor semantic and release-route binding

The Python and Rust host cores now expose separate custody-successor binding
entries over the existing V1 input, output, and opaque structural-witness types.
They select the reviewed [semantic bundle](../specifications/ASSET_TRANSFER_CUSTODY_SEMANTICS_V1.md),
reuse the existing policy/context/journal/release/route checks, and confirm the
supplied acceptance through the completed custody recomputation. Legacy public
entries retain their previous behavior.

The selector requires the occurrence-governed single-ASSET route, its selected
module release, and the profile's ASSET coordinator release to carry exactly:

```text
0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1
```

That identity is the domain-separated hash of the canonical decoded semantic
bundle. The raw file SHA-256 is a separate byte identity. A retained regression
distinguishes these and rejects a coherently rebuilt release graph carrying
the raw SHA as its specification root. Version text and source/image metadata
do not substitute for the reviewed semantic root.

Python takes one aggregate owned snapshot before selection and binding. Rust
uses immutable shared references and validates its separately supplied
registries against the profile. Both selectors perform ordinary semantic
selection; ACTIVE-profile and occurrence/profile admission remain in the
structural binder. The module-level witness commits the coordinator indirectly
through the profile identity. Native route composition separately requires its
coordinator context; no route coordinator-membership field is invented.

## Evidence and review

The root Python replay passed 123 new and retained tests, plus the separate
shared-vector regeneration test. Cases include custody zero, one, and seven;
coherently rebuilt module/coordinator/route mismatches; altered conservation
totals; context and route failures; exact-type rejection; unchanged inputs;
and retained legacy root vectors. Python instrumentation observes one custody
recomputation and no legacy recomputation on the new path.

The Rust suites cover the new binding, retained release-route/receipt behavior,
and custody execution. The shared Python-generated canonical vector decodes
through the existing Rust V1 types and produces the same binding root. Native
Rust exactly-once recomputation is established by the one-call source and
recomputation-mismatch cases, rather than call-count instrumentation.

Independent review identified and corrected the raw-SHA selection defect and
the Rust selector's initially stricter activation/context boundary. The initial
Fable calls reached their launcher's former time limit; their preserved patches
were completed and checked by the integration team. No worker success claim
substituted for these checks.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/core/test_asset_transfer_custody_semantics_v1.py \
  tests/core/test_asset_transfer_custody_release_route_binding_v1.py \
  tests/core/test_lane_module_release_route_binding_v1.py \
  tests/core/test_asset_transfer_lane_module_custody_v1.py \
  tests/core/test_asset_transfer_custody_binding_vector_v1.py

cargo test --manifest-path zk/global_settlement_abi_v1/Cargo.toml --offline --locked \
  --test asset_transfer_custody_release_route_binding \
  --test lane_module_release_route_binding \
  --test asset_transfer_lane_module_custody

python3 -B -m experiments.v3_custody_successor_v1.render_vectors
```

Ruff and focused new-test MyPy checks pass. The existing Python binder retains
three read-only-context versus writable-protocol MyPy findings, reproduced
against the unchanged baseline with `--shadow-file`; this patch adds none.

## Qualification boundary

This is tested host binding code. Synthetic ACTIVE_NEW and evidence-status
fixture rows are ordinary test data. No genuine receipt, measured successor
guest, qualified release/profile, activation, publisher mount, custody genesis,
deposit/withdrawal policy, or migration is supplied by this increment. Custody
receipt and native-route entries remain subsequent integration tasks. The
whole formal core and production value-safety claims remain closed.
