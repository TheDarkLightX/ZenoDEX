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
   ∧ (present_false ∨ state_hash_field_ok)
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
   ∧ not_present_false
   ∧ not_error_nonempty
   ∧ rules_field_is_string
   ∧ accounts_hash_field_ok
   ∧ app_hash_field_ok
```

Interpretation:

- a typed `present=false` response is rejected
- a non-empty typed `error` response is rejected
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

## Honest limit

This note does not prove:

- the Tau node emits truthful payloads,
- the TCP server implementation matches this contract,
- global network non-equivocation.
