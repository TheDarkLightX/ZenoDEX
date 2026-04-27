FIRE verifier lane.

Current status:
- `src/fire/verifier/cert_v1.py`
- `src/fire/verifier/object_package_v1.py`
- `src/fire/verifier/proof_tree_cert_v1.py`
- `src/fire/verifier/settlement_v1.py`
- `src/fire/verifier/settlement_apply_report_v1.py`
- `src/fire/verifier/settlement_apply_artifact_v1.py`
  are native under `src/fire`
- legacy `src/kernels/python/fire_*` verifier/reporting modules now exist only
  as compatibility shims back to this lane or to `src/fire/kernel`
- `src/fire/verifier/esso_kernels_v1.py` remains a maintainer-only admission helper for the
  private ESSO toolchain

Current concrete module:
- `src/fire/verifier/cert_v1.py`
- `src/fire/verifier/object_package_v1.py`
- `src/fire/verifier/proof_tree_cert_v1.py`
- `src/fire/verifier/esso_kernels_v1.py`
- `src/fire/verifier/formal_assurance_claims_v1.py`
- `src/fire/verifier/settlement_v1.py`
- `src/fire/verifier/settlement_apply_report_v1.py`
- `src/fire/verifier/settlement_apply_artifact_v1.py`

`src/fire/verifier/esso_kernels_v1.py` is a maintainer-only admission helper for the private ESSO toolchain. It is not part of the public GitHub-required verification surface.

Target role:
- schema and hash binding
- draft proof-tree cert validation for CAL-style FIRE-Cert artifacts
- cert checking
- witness and collateral checks
- deterministic integer evaluation
- replay and delta checks
- runtime receipt binding for object, instance, certificate, witness bundle,
  delta hash, and bundle hash when a persisted bundle is used

Formal-assurance claim gate:

```text
FormalVerified(component) -> CheckedProofReceipt(component)
BugFree(component) -> reject
```

Plain English: no FIRE compiler or verifier component may be advertised as
bug-free, and no formal-verification claim is accepted without an explicit
checked proof receipt. The current verifier remains part of the trusted
computing base until those proof receipts exist.

Run:

```bash
python3 tools/check_fire_formal_assurance_claims.py
python3 tools/check_fire_release_assurance.py
```

Current proof-tree cert discipline:
- `proof_tree_certificate.json` is non-authoritative package evidence only
- it must still bind to:
  - `object_hash`
  - `instance_hash`
  - `certificate_sha256`
  - dependency hashes from `object_lock.json`
- it must carry `runtime_certificate_summary` derived from the live interval certificate
- its node `rule` ids must come from `src/fire/spec/verifier-rules.yaml`
- each node `rule` must be allowed by the canonical rule catalog to establish
  that node's predicate
- where the canonical rule catalog declares input predicates, the node inputs
  must match those prerequisite predicates exactly
- the `ReplayOK` node must bind to the current `replay_input.json` summary and
  its `sha256`, plus the concrete `kernel_replay_receipt.json` artifact via its
  `sha256` and replay transcript hashes, plus the concrete
  `kernel_settlement_receipt.json` artifact via its `sha256` and its emitted
  settlement deltas/effects
- the `IntegerEvalOK` node must bind to the runtime certificate's root rule,
  node count, exact-parameter names, and source-bound names, plus the concrete
  `compile_receipt.json` artifact via its `sha256`, plus the concrete
  `kernel_receipt.json` artifact and admitted ref-kernel provenance surface via
  its `sha256`, plus the concrete `kernel_eval_receipt.json` artifact via its
  `sha256`
- the `UnitOK` node must bind to the manifest settlement asset plus parameter
  and imported-interface units
- the `WitnessOK` node must bind to the manifest witness and imported-interface
  policy surface plus the concrete bundle contract-receipt surface
- the `ParamOK` node must bind to manifest parameter bounds plus instance
  parameter values
- the `AuthorizationOK` node must bind to instance policy and actual bound
  parties
- the `NonceOK`, `MaturityOK`, and `WindowOK` nodes must bind to the manifest
  policy requirement flags plus actual instance presence/state
- required claim evidences must stay consistent with the live manifest evidence labels and runtime `certificate.json` instance-gate claims
- the `BoundOK` root node must match the runtime certificate root interval

Settlement authority remains:

```text
SettlementAuthority := runtime cert ∧ verifier receipt
FIREVReceiptOK(receipt) := object_hash ∧ instance_hash ∧ cert_sha256 ∧ witness_hash ∧ delta_hash
SettlementAuthority(packet) -> verify_fire_settlement_authority_packet(packet)
```

Plain English: a runtime verifier receipt is settlement authority only when
it binds the accepted object, instance, certificate, witness bundle, and emitted
delta. Package evidence such as `compile_receipt.json`, `kernel_receipt.json`,
`kernel_eval_receipt.json`, `kernel_replay_receipt.json`,
`kernel_settlement_receipt.json`, and `proof_tree_certificate.json` can
strengthen provenance and fail-closed checks, but they do not authorize funds
movement by themselves.

Native adapter boundary:

```text
ProductionAdapterSettle -> PersistedBundleOK ∧ FIREVReceiptOK
SimulationAdapterSettle -> KernelTraceOnly ∧ ¬SettlementAuthority
```

Plain English: production `make_adapter` settlement rejects without a
persisted bundle and verifier receipt. `make_simulation_adapter` exists only for
private ESSO shell-equivalence against the pure kernel trace and is not a
settlement-authorizing surface.

Use the explicit authority APIs for funds movement:

- `verify_fire_settlement_authority_receipt`
- `verify_fire_settlement_authority_packet`
- `extract_verified_fire_settlement_authority_packet`
- `verify_fire_authority_apply_receipt`

The generic receipt/packet checkers remain available for structural or
simulation-only checks, but they are not the settlement-authority API.
