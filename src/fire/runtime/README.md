FIRE runtime lane.

Current status:

- native object runtime modules now live in `src/fire/runtime/` for:
  - `burn_boost_call_v1.py`
  - `fee_note_v1.py`
  - `lp_loss_cover_v1.py`
- shared runtime verifier glue lives in `common_v1.py`
- native interface registry now lives in `interface_registry_v1.py`
- persisted-bundle adapter gate and FIRE native adapters now live in:
  - `adapter_manifest_gate_v1.py`
  - `burn_boost_call_v1_native_adapter.py`
  - `fee_note_v1_native_adapter.py`
  - `lp_loss_cover_v1_native_adapter.py`
  - `native_adapter_registry_v1.py`
- legacy `src/kernels/python/fire_*` runtime modules now exist only as
  compatibility shims back to this lane or to `src/fire/kernel`
