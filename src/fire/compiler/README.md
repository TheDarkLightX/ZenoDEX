The canonical FIRE compiler entrypoints now live under `src/fire/compiler/`.

Current status:

- native core in `src/fire/compiler/`:
  - `compile_receipt_v1.py`
  - `object_compiler_v1.py`
  - `fmos_file_v1.py`
  - `fmos_v1.py`
  - `zpl_v1.py`
  - `compiler_registry_v1.py` for list/get/compile/composition, including
    the span-aware ZPL runtime-compatibility checks
- the runtime `SPEC` definitions consumed by the compiler now come from
  `src/fire/runtime/`
- legacy `src/kernels/python/fire_*` compiler modules now exist only as
  compatibility shims back to this lane

Assurance boundary:

```text
CompileOK -> PackageEvidence
PackageEvidence ∧ FIREVReceiptOK(receipt) -> SettlementAuthority
```

Plain English: compiler output may contribute package evidence, but the
compiler is not settlement authority. A money-moving path must still pass
FIRE-V/FIRE-VCore and produce a verifier receipt bound to object, instance,
certificate, witness, and delta hashes.

Compile receipts also carry `formal_proof_bindings` for the Lean proof surface:
`Proofs.ZenoPayoffLanguage`, `Proofs.CALCoreSoundness`, the fixed-point bridge
stack ending at `Proofs.ZenoPayoffPortfolioFixedPointBridge`, and their shared
dependencies. The checker compares those bindings against current source hashes,
so a receipt generated under one proof surface does not silently validate after
theorem or source drift.

The compiler must not be described as bug-free or formally verified unless
`src/fire/spec/formal-assurance-claims.yaml` carries checked proof receipts and
`tools/check_fire_formal_assurance_claims.py` accepts them.

Public tool entrypoints should continue importing from `src/fire/compiler/`
instead of reaching into the legacy path directly.
