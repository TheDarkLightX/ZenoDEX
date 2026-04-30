FIRE spec tree.

This directory is the canonical rules surface for the current FIRE migration slice.

Files here are normative for:
- rule naming
- canonical serialization guidance
- evidence lattice labels
- verifier rule names
- package layout naming
- schema names and schema locations for:
  - `fire-ir.schema.json`
  - `fire-instance.schema.json`
  - `fire-cert.schema.json`
  - `fire-compile-receipt.schema.json`
  - `fire-kernel-receipt.schema.json`
  - `fire-kernel-eval-receipt.schema.json`
  - `fire-kernel-replay-receipt.schema.json`
  - `fire-kernel-settlement-receipt.schema.json`
  - `fire-cert-rules.schema.json` (draft proof-tree cert schema)
  - `fire-lock.schema.json`
  - `fire-replay-input.schema.json`
  - `object-package.schema.json`
  - `fire-formal-assurance-claims.schema.json`

The formal-assurance posture is pinned in `formal-assurance-claims.yaml` and
checked by `tools/check_fire_formal_assurance_claims.py`. That gate is
intentionally conservative:

```text
CompilerOK ∧ VerifierOK ∧ FIREVReceiptOK(receipt) -> SettlementAuthority
```

Plain English: compiler and verifier correctness are trusted-computing-base
assumptions unless a component has a checked proof receipt, and settlement
authority still requires a FIRE-V receipt bound to object, instance,
certificate, witness, and delta hashes.

The gate rejects claims that the compiler or verifier are bug-free or formally
verified without machine-checkable proof receipts. It also rejects any attempt
to make package acceptance receipts authorize settlement.

`fire-compile-receipt.schema.json` now requires `formal_proof_bindings`.
Those bindings record the Lean module, checker command, theorem names,
toolchain, and source hashes for the ZPL/CAL proof surface and fixed-point
runtime bridge that support the compiled object. The release-level formal
claims gate also checks proof-receipt module hashes against the current Lean
source files and rejects Lean trust escapes such as `sorry`, `admit`, `axiom`,
`unsafe`, or `sorryAx` outside comments, so a stale or placeholder-bearing proof
receipt cannot keep a public formal claim alive after theorem-source drift.
The gate also requires Lean proof receipts to name the current Lean toolchain,
checker commands, modules, and non-empty theorem surfaces. Each cited Lean
module must be targeted by a matching `lake env lean <file>` or
`lake build <module>` command in the receipt.

```text
CompileReceiptOK ∧ FormalProofBindingHashesOK -> PayoffProofSurfaceBound
```

Plain English: a compile receipt is not just tied to Python compiler output; it
also names the exact checked Lean facts that justify the payoff-language safety
claim, including the one-tick fixed-point rounding buffers for runtime
settlement and the unified FIRE receipt composition laws, and rejects if those
proof files drift.

Release checks should run the aggregate gate:

```bash
python3 tools/check_fire_release_assurance.py
```

That gate composes the formal-assurance manifest check with the acceptance
receipt schema and verifier rule catalog checks for `FIREVReceiptOK`.

The canonical implementation boundary now lives under `src/fire/`.
Legacy `src/kernels/python/fire_*` modules are compatibility shims only; they are
not the source of truth for FIRE rules, manifests, verifier behavior, or
settlement artifacts.

The repo-local draft proof-tree cert schema now requires the sidecar to bind to:
- `object_hash`
- `instance_hash`
- `certificate_sha256`
- dependency hashes
- `runtime_certificate_summary`

The corresponding verifier also rejects proof-tree node `rule` ids that are not present in `verifier-rules.yaml`.
It now also uses the rule catalog's machine-readable `establishes` shapes to
check that a proof-tree node's `rule` is allowed to establish that predicate,
and, where declared, that the node's input predicates match the rule's
canonical prerequisites.
For the current draft sidecar lane, the verifier also binds:
- `ReplayOK` to `replay_input.json` plus its `sha256`
- `ReplayOK` to the concrete `kernel_replay_receipt.json` artifact via its
  `sha256` plus its replay transcript, delta, and settlement hashes
- `ReplayOK` to the concrete `kernel_settlement_receipt.json` artifact via its
  `sha256` plus its emitted settlement deltas/effects
- `IntegerEvalOK` to a manifest/runtime-cert-derived integer-evaluation summary
  plus `compile_receipt.json`, `kernel_receipt.json`, and
  `kernel_eval_receipt.json` via their `sha256`
- `UnitOK` to the manifest settlement asset and unit surface
- `WitnessOK` to manifest witness/import policy summaries plus the concrete
  bundle contract-receipt surface
- `ParamOK`, `AuthorizationOK`, `NonceOK`, `MaturityOK`, and `WindowOK` to
  manifest/instance policy summaries derived from the canonical package
