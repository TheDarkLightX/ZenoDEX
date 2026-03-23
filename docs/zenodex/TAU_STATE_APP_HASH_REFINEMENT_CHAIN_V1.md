# Tau State App-Hash Refinement Chain v1

## Purpose

This note states the next formal layer beyond the `LoaderOK` acceptance shell.

The previous bundle formalized the exact loader acceptance relation once the
host has already computed the relevant booleans.

This note formalizes the refinement chain from transport observations to those
booleans.

## Layers

### L0. Transport observations

The runtime reads:

- `getstateproof full`
- `getappstate full`
- optional `gettaustate <state_hash>`

across a bounded stable-read window with `stable_read_attempts = 3` by default.

Each retry is a fresh observation. The model does not assume that an unstable
first attempt forces every later attempt to stay unstable.

Because the runtime budget is finite, `StableWindowPossible` does not imply
eventual return by itself. Three fresh unstable observations may still exhaust
the retry budget before a stable one is seen.

### L1. Typed host views

The TCP surface is parsed into:

- `TauNetStateProofView`
- `TauNetAppStateView`
- `TauNetTauStateView`

These are still transport-facing objects, not yet admission predicates.

### L2. Stable-window predicates

```text
StableWindowOK
  := state_proof_stable
   ∧ app_state_stable
   ∧ (¬strong_binding_required ∨ tau_state_stable)
```

Interpretation:

- `state_proof_stable`: the before/after `getstateproof full` views are equal
- `app_state_stable`: the before/after `getappstate full` views are equal
- `tau_state_stable`: the before/after `gettaustate <state_hash>` views are equal

### L3. Transport refinement predicates

```text
TransportRefinementOK
  := bridge_payload_ready
   ∧ state_proof_present
   ∧ state_hash_present
   ∧ app_state_present
   ∧ app_state_hash_ok
   ∧ StableWindowOK
   ∧ (¬strong_binding_required
      ∨ (
           tau_state_transport_available
         ∧ tau_state_present
         ∧ tau_state_hash_matches_proof
         ∧ tau_state_app_hash_present
         ∧ tau_state_app_hash_matches_app_state
        ))
```

This is the exact host-side refinement surface that should imply the abstract
loader gate, once the request/anchor/policy binding predicates are established.

### L4. Loader acceptance shell

The previous note defines:

```text
LoaderOK
  := BridgePayloadReady
   ∧ BaselineProvenanceOK
   ∧ (¬strong_binding_required ∨ StrongTauStateBindingOK)
```

where:

- `BridgePayloadReady`
- `BaselineProvenanceOK`
- `StrongTauStateBindingOK`

are abstract booleans already exposed to the acceptance shell.

## Refinement law

The intended relation is:

```text
TransportRefinementOK
  => (
       BridgePayloadReady
     ∧ BaselineProvenanceOK
     ∧ (¬strong_binding_required ∨ StrongTauStateBindingOK)
     )
```

This is not yet a proof that the upstream Tau node implementation refines the
typed host views. It is the explicit logical bridge from typed host observations
to the abstract acceptance predicates.

## Disaster paths

### R1. Stable-window laundering

```text
R1 := ¬StableWindowOK ∧ TransportRefinementOK
```

This must be impossible.

### R2. Strong binding silently ignored

```text
R2 := strong_binding_required
   ∧ ¬tau_state_transport_available
   ∧ TransportRefinementOK
```

This must be impossible.

### R3. App-hash mismatch survives refinement

```text
R3 := strong_binding_required
   ∧ tau_state_present
   ∧ ¬tau_state_app_hash_matches_app_state
   ∧ TransportRefinementOK
```

This must be impossible.

## Artifact bundle

- [TAU_STATE_APP_HASH_PROVENANCE_FORMALISM_V1.md](./TAU_STATE_APP_HASH_PROVENANCE_FORMALISM_V1.md)
- [TauStateAppHashStableWindow.tla](../../formal/tla/TauStateAppHashStableWindow.tla)
- [ZenoDEXTauStateAppHashStableWindow.lean](../../lean-mathlib/Proofs/ZenoDEXTauStateAppHashStableWindow.lean)

## Honest limit

This refinement chain still stops at the typed host-view boundary.

It does not yet prove:

- the upstream Tau TCP implementation emits those views correctly,
- the node cannot equivocate across peers,
- the reported `state_hash` and any block/header identity are globally canonical.
