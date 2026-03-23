# Tau Node Conformance Boundary v1

## Purpose

This note makes the remaining upstream boundary explicit.

The repo now has:

- formal acceptance-shell artifacts for Tau app-hash provenance,
- formal stable-window refinement artifacts,
- formal typed TCP view contracts,
- executable parity coverage for the Python host parser,
- and a focused formal gate for that chain.

What it still does not have is a proof that the upstream Tau node's TCP server
refines those contracts.

## Observable Conformance Formula

```text
ObservedAppStateOK
  := getappstate_full_returns_typed_view

ObservedStateProofOK
  := getstateproof_full_returns_typed_view

ObservedTauStateOK
  := gettaustate_state_hash_returns_typed_view

LiveNodeConformanceOK(require_tau_state_transport)
  := ObservedAppStateOK
   ∧ ObservedStateProofOK
   ∧ (¬require_tau_state_transport ∨ ObservedTauStateOK)
```

Interpretation:

- `ObservedAppStateOK`: the live node response for `getappstate full` satisfies the host typed view contract
- `ObservedStateProofOK`: the live node response for `getstateproof full` satisfies the host typed view contract
- `ObservedTauStateOK`: the live node response for `gettaustate <state_hash>` satisfies the host typed view contract

## What This Can And Cannot Show

If the live conformance harness passes, we learn:

- the current node deployment emits TCP payloads accepted by the repo's typed host views
- the deployment supports the expected command surface for the checked commands

We do not learn:

- that all Tau nodes behave the same way,
- that the upstream server implementation is proved against these contracts,
- that the network is non-equivocating,
- or that the live node cannot change behavior between observations.

## Honest Use

Treat live conformance as:

- an executable observation layer,
- useful for detecting server/transport drift,
- subordinate to the formal host-side artifacts,
- and never a substitute for a proof of upstream implementation semantics.
