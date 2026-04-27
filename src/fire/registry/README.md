FIRE registry lane.

Current status: public registry entrypoints now route through `src/fire/registry/`.
Native registry implementations now exist for:
- `src/fire/registry/bundle_v1.py`
- `src/fire/registry/instance_v1.py`
- `src/fire/registry/index_v1.py`
- `src/fire/registry/lock_v1.py`
- `src/fire/registry/object_manifest_v1.py`
- `src/fire/registry/release_v1.py`
- `src/fire/registry/deployment_contract_v1.py`
- `src/fire/registry/replay_input_v1.py`
- legacy `src/kernels/python/fire_*` registry modules now exist only as
  compatibility shims back to this lane

The remaining bridge-oriented work in this lane is now above the artifact layer:
- `src/fire/registry/snapshot_v1.py`

Current concrete modules:
- `src/fire/registry/bundle_v1.py`
- `src/fire/registry/instance_v1.py`
- `src/fire/registry/index_v1.py`
- `src/fire/registry/lock_v1.py`
- `src/fire/registry/object_manifest_v1.py`
- `src/fire/registry/release_v1.py`
- `src/fire/registry/deployment_contract_v1.py`
- `src/fire/registry/replay_input_v1.py`
- `src/fire/registry/snapshot_v1.py`

Target role:
- publication status
- supersession and lifecycle metadata
- signed index and release metadata
- deployment policy receipts
