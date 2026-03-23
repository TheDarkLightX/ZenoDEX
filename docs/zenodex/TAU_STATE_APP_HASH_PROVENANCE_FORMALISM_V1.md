# Tau State App-Hash Provenance Formalism v1

## Purpose

This note states the explicit control-layer logic for the Tau-state/app-hash provenance path used by the settlement signer-registry loader.

It separates:

- host-side data predicates:
  - hash recomputation,
  - JSON decoding,
  - transport response parsing,
  - byte-level canonicalization
- from the smaller protocol predicates that determine whether settlement admission may proceed.

That is the right split for maximum assurance at this stage:

- `Lean` proves the exact boolean acceptance relation.
- `ESSO` verifies the bounded fail-closed guard.
- `TLA+` checks bounded temporal behavior for the stable-window and transport outcomes.

## Scope

This formalism covers the provenance shell for:

- `getstateproof full`
- `getappstate full`
- optional `gettaustate <state_hash>`

It does **not** prove:

- the upstream Tau node implementation,
- cryptographic collision resistance,
- DHT network liveness or anti-equivocation beyond the modeled control surface,
- block/header identity refinement for `anchor_block_hash`.

## Atom Table

### Control atoms

- `exec_req`: the runtime is evaluating a settlement admission request
- `bridge_payload_present`: the settlement signer-registry bridge object is present in app-state
- `bridge_payload_object_ok`: the bridge payload decodes as an object
- `bridge_schema_ok`: the bridge payload uses the expected Tau bridge schema
- `bridge_snapshot_present`: the bridge payload includes a snapshot payload
- `request_binding_ok`: requested policy tuple matches the intended settlement tuple
- `anchor_binding_ok`: loaded anchor matches the intended request tuple
- `policy_binding_ok`: loaded snapshot policy hash matches the governed policy object
- `strong_binding_required`: runtime requires Tau-state/app-hash provenance binding

### Host-computed data predicates

- `state_proof_present`
- `state_hash_present`
- `state_proof_stable`
- `state_proof_error_free`
- `app_state_present`
- `app_state_stable`
- `app_state_hash_ok`
- `tau_state_transport_available`
- `tau_state_present`
- `tau_state_stable`
- `tau_state_hash_matches_proof`
- `tau_state_app_hash_present`
- `tau_state_app_hash_matches_app_state`

Interpretation:

- `app_state_hash_ok` means `sha256(canonical_json(app_state)) = app_hash`
- `tau_state_hash_matches_proof` means the `tau_state` object retrieved by transport corresponds to the stable `state_hash`
- `tau_state_app_hash_matches_app_state` means the committed `tau_state.app_hash` equals the committed `getappstate.app_hash`

## Core formulas

### Bridge payload readiness

```text
BridgePayloadReady
  := exec_req
   ∧ bridge_payload_present
   ∧ bridge_payload_object_ok
   ∧ bridge_schema_ok
   ∧ bridge_snapshot_present
   ∧ request_binding_ok
   ∧ anchor_binding_ok
   ∧ policy_binding_ok
```

### Baseline provenance

```text
BaselineProvenanceOK
  := state_proof_present
   ∧ state_hash_present
   ∧ state_proof_stable
   ∧ state_proof_error_free
   ∧ app_state_present
   ∧ app_state_stable
   ∧ app_state_hash_ok
```

### Strong Tau-state binding

```text
StrongTauStateBindingOK
  := tau_state_transport_available
   ∧ tau_state_present
   ∧ tau_state_stable
   ∧ tau_state_hash_matches_proof
   ∧ tau_state_app_hash_present
   ∧ tau_state_app_hash_matches_app_state
```

### Final loader acceptance

```text
LoaderOK
  := BridgePayloadReady
   ∧ BaselineProvenanceOK
   ∧ (¬strong_binding_required ∨ StrongTauStateBindingOK)
```

This is the intended acceptance law for the control shell.

## Disaster paths

### D1. Stable app-state without committed Tau-state relation

```text
D1 := BridgePayloadReady
   ∧ BaselineProvenanceOK
   ∧ strong_binding_required
   ∧ ¬StrongTauStateBindingOK
   ∧ settlement_admitted
```

If this occurs, the runtime is trusting an app snapshot that is not proven to be the one committed under the stable Tau `state_hash`.

### D2. Tau transport missing but silently downgraded

```text
D2 := strong_binding_required
   ∧ ¬tau_state_transport_available
   ∧ settlement_admitted
```

### D3. Tau-state app-hash drift

```text
D3 := strong_binding_required
   ∧ tau_state_present
   ∧ tau_state_app_hash_present
   ∧ ¬tau_state_app_hash_matches_app_state
   ∧ settlement_admitted
```

### D4. Stable-window laundering

```text
D4 := state_proof_present
   ∧ app_state_present
   ∧ tau_state_present
   ∧ ¬(state_proof_stable ∧ app_state_stable ∧ tau_state_stable)
   ∧ settlement_admitted
```

## Artifact map

### Runtime

- [tau_net_client.py](../../src/integration/tau_net_client.py)
- [settlement_signer_registry.py](../../src/integration/settlement_signer_registry.py)

### ESSO

- [`tau_state_app_hash_provenance_guard_v1.yaml`](../../src/kernels/dex/tau_state_app_hash_provenance_guard_v1.yaml)

### TLA+

- [`TauStateAppHashProvenanceBridge.tla`](../../formal/tla/TauStateAppHashProvenanceBridge.tla)
- [`TauStateAppHashProvenanceBridge.cfg`](../../formal/tla/TauStateAppHashProvenanceBridge.cfg)

### Lean

- [`ZenoDEXTauStateAppHashProvenance.lean`](../../lean-mathlib/Proofs/ZenoDEXTauStateAppHashProvenance.lean)

## Honest limit

This formalism gives a machine-checked acceptance shell.
It is not yet a full refinement proof from:

- Tau node implementation
- to TCP transport
- to Python loader
- to settlement admission

That refinement step remains future work.
