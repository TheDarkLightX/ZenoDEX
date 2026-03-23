# Settlement Signer Registry Tau-Native Bridge v1

## Purpose

This slice defines the next honest upgrade beyond the current settlement attestation governance posture.

Current code can bind a governed policy to a typed registry snapshot and a typed chain-anchor adapter.
That is stronger than operator-local allowlists, but it is still not a Tau-native proof of chain state.

This document states the minimal Tau-native bridge contract we need before widening the decentralization claim.

## ShapeForge State

```text
Φ := ⟨
  M = ZenoDEX,
  S = settlement signer registry Tau-native bridge,
  A = registry retrieval / proof binding,
  T = replace adapter-trust with Tau-native state-bound admission,
  V = {
    exec_req,
    chain_id,
    registry_contract,
    policy_id,
    policy_epoch,
    registry_root,
    policy_hash,
    snapshot_present,
    anchor_present,
    request_binding_ok,
    anchor_binding_ok,
    policy_binding_ok,
    proof_ok,
    anchor_block_number,
    anchor_block_hash
  },
  O = { request_anchor, load_snapshot, check_binding, admit_settlement_bundle },
  G = {
    snapshot_present,
    anchor_present,
    request_binding_ok,
    anchor_binding_ok,
    policy_binding_ok,
    proof_ok
  },
  Obs = { tau_bridge_ok, policy_epoch_echo, anchor_block_number_echo },
  K = { policy_hash = H(policy), registry_root = Root(registry_state) },
  E = {
    contract: settlement_signer_registry.py,
    contract: tau_net_client.py,
    contract: settlement_signer_registry_anchor_gate_v1.tau,
    proved: SettlementSignerRegistryTauBridge.tla
  },
  Gap = {
    Tau-native state proof retrieval,
    runtime loader wired to Tau Net state instead of adapter-only transport,
    stronger proof story for anchor_block_hash provenance
  },
  N = {
    adapter binding is not chain proof,
    typed JSON-RPC transport is not enough for a decentralization claim,
    a valid signer policy is weaker than a proved chain-state binding
  },
  Δ = host-computed Tau guard + protocol-level TLA bridge model for state-bound registry admission
⟩
```

## Minimal Admission Formula

The Tau-native bridge gate should remain intentionally small.
Large arithmetic, parsing, and proof decoding stay host-side.
Tau only sees the control surface:

```text
BridgeReady
  := snapshot_present
   ∧ anchor_present
   ∧ request_binding_ok
   ∧ anchor_binding_ok

TauNativeRegistryBindingOK
  := BridgeReady
   ∧ policy_binding_ok
   ∧ proof_ok

TauNativeRegistryGateOK(exec_req)
  := exec_req ∧ TauNativeRegistryBindingOK
```

Interpretation:

- `snapshot_present`: a registry snapshot for the requested `(chain_id, registry_contract, policy_id, policy_epoch)` exists
- `anchor_present`: a chain anchor for the same request exists
- `request_binding_ok`: the request tuple matches the intended settlement packet/policy tuple
- `anchor_binding_ok`: the chain anchor matches the loaded snapshot root/epoch tuple
- `policy_binding_ok`: the loaded snapshot policy hash matches the governed policy object carried into settlement
- `proof_ok`: the host has accepted the Tau-native state retrieval/proof path

## Disaster Paths This Slice Closes

### D1. Adapter drift accepted as truth

```text
D1 := adapter_snapshot_present ∧ ¬anchor_binding_ok ∧ settlement_admitted
```

If the runtime accepts an off-chain snapshot that does not match the chain anchor, the policy can drift without detection.

### D2. Request/epoch confusion

```text
D2 := request_epoch ≠ snapshot_epoch ∧ settlement_admitted
```

If the requested policy epoch and loaded snapshot epoch differ, later governance updates can be misbound to older packets.

### D3. Proof path downgraded silently

```text
D3 := snapshot_present ∧ anchor_present ∧ ¬proof_ok ∧ settlement_admitted
```

If the runtime can fall back from a Tau-native proof lane to an unproved adapter path without changing the admission result, the public claim overstates the system.

In the bounded protocol model, once the request/snapshot/anchor bindings are otherwise ready, proof-path availability is an explicit state bit. An unavailable or downgraded proof lane is treated as rejectable drift rather than being conflated with 'proof not granted yet' or a state that may stutter forever.

## Artifact Plan

### Tau Guard

- file: `src/tau_specs/recommended/settlement_signer_registry_anchor_gate_v1.tau`
- role: fail-closed guard for the host-computed bridge booleans
- claim level: `contract`

### TLA+ Model

- file: `formal/tla/SettlementSignerRegistryTauBridge.tla`
- role: bounded protocol model for request, snapshot load, anchor load, accept/reject resolution
- claim level: `proved` for the bounded temporal obligations checked by TLC

### Runtime Wiring Target

The next runtime integration should be a Tau-native loader layered on `src/integration/tau_net_client.py` or a Tau state-proof surface.
It should emit the booleans consumed by the Tau guard above and fail closed when any of them is false.

## Upgrade Discipline

This slice does not yet prove direct Tau state proof verification in runtime code.
It does make the missing contract explicit and replayable.

That is the correct next step because it prevents the repo from claiming a decentralized registry path before the chain-bound loader actually exists.
