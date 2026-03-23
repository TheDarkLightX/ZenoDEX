# Tau TCP View Contract v1

## Purpose

This note states the abstract contracts for the typed TCP views returned by:

- `getappstate_view()`
- `getstateproof_view()`
- `gettaustate_view(state_hash)`

These contracts are the final formal layer before the upstream Tau node
implementation itself.

## App-State View Contract

```text
AppStateViewOK
  := response_is_object
   ∧ app_hash_field_ok
```

Interpretation:

- `response_is_object`: `getappstate full` decodes to a JSON object
- `app_hash_field_ok`: `app_hash` is either empty or a canonical 32-byte hex

Host-side note:

- `app_state` content typing is deferred to the later bridge loader checks
- the parser itself only guarantees object-ness plus normalized `app_hash`

## State-Proof View Contract

```text
StateProofViewOK
  := response_is_object
   ∧ present_field_is_bool
   ∧ (¬present ∨ state_hash_field_ok)
   ∧ proof_type_field_ok
   ∧ proof_bytes_field_ok
   ∧ proof_sha256_field_ok
   ∧ error_field_ok
```

Interpretation:

- when `present=true`, `state_hash` must be canonical 32-byte hex
- `proof_type`, `proof_bytes`, `proof_sha256`, and `error` are typed if present

## Tau-State View Contract

```text
TauStateViewOK
  := response_is_object
   ∧ present_field_ok
   ∧ error_field_ok
   ∧ present
   ∧ error_empty
   ∧ state_hash_field_ok
   ∧ rules_field_is_string
   ∧ accounts_hash_field_ok
   ∧ app_hash_field_ok
```

Interpretation:

- `present` is the actual semantic presence bit after typed parsing
- `error_empty` means the typed `error` field is absent or empty
- a typed `present=false` response is rejected
- a non-empty typed `error` response is rejected
- returned `state_hash`, when present, must be canonical and match the requested hash
- `rules` must be a string
- `accounts_hash` must be canonical 32-byte hex
- `app_hash` may be empty or canonical 32-byte hex

## Composition Law

The intended bridge between transport and admission is:

```text
ViewContractsOK
  := AppStateViewOK
   ∧ StateProofViewOK
   ∧ (¬strong_binding_required ∨ TauStateViewOK)

ViewContractsOK
  => TransportRefinementCandidateWellTyped
```

That is still not the full node refinement theorem.
It is the explicit contract boundary between:

- raw TCP JSON payloads
- typed host views
- and the previously formalized stable-window / loader predicates

## Executable Parity

The repo also carries parser-parity tests for representative boundary cases:

- `tests/integration/test_tau_tcp_view_contract_parity.py`

These are not proofs of the upstream Tau node implementation.
They do pin the concrete Python parser behavior to the stated typed-view
contracts so the formal notes and the runtime do not drift independently.

The repo also carries an optional live-node conformance harness:

- [test_tau_tcp_live_contract_conformance.py](/tmp/zenodex-main-merge.RjwkAn/tests/integration/test_tau_tcp_live_contract_conformance.py)
- [TAU_NODE_CONFORMANCE_BOUNDARY_V1.md](/tmp/zenodex-main-merge.RjwkAn/docs/zenodex/TAU_NODE_CONFORMANCE_BOUNDARY_V1.md)

That harness is observational only. It checks whether a running Tau node emits
payloads accepted by these contracts. It is not a proof of the upstream server.

## Honest limit

This note does not prove:

- the Tau node emits truthful payloads,
- the TCP server implementation matches this contract,
- global network non-equivocation.
