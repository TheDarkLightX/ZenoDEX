# FCIS M6 D01 Authority Normal Form Schema V1

## Status

`TESTED / UNMOUNTED`

This schema defines a canonical research carrier for one M6 R04 accepted
transition. It does not create a production authority witness.

## Root tuple

`FCISAuthorityNormalFormV1` contains one exact lowercase 32-byte digest for
each of these fields:

```text
source:
  command_root
  execution_context_root
  pre_state_root
  next_state_root
  support_root
  support_set_commitment
  snapshot_commitment

SLNF:
  boundary_root
  policy_root
  witness_tuple_root
  semantic_stream_root
  lineage_stream_root

candidate:
  patch_root
  commit_plan_root

C3 closure:
  c3_claim_set_root
  budget_root
  evaluation_certificate_root
  receipt_certificate_root
  bundle_certificate_root
  outbox_certificate_root

authority and durability:
  acceptance_decision_root
  acceptance_receipt_root
  base_bundle_root
  outbox_plan_root

TCG:
  tcg_topology_root
  tcg_instance_root

DRA and migration:
  dra_pre_history_root
  dra_post_history_root
  migration_authority_epoch_root
```

The value also contains a closed proof-context policy. `NOT_REQUIRED` must
carry `None`; `REQUIRED` must carry one exact proof-context root. This makes
absence and presence distinct typed states.

## Canonical codec

The codec emits:

```text
{
  "schema": "zenodex/fcis/authority-normal-form/v1",
  "value": <closed field object>
}
```

Canonical JSON uses the repository UTF-8, sorted-key, no-whitespace encoder.
The decoder requires exact bytes, rejects duplicate/unknown/missing fields,
rejects wrong schema and wrong types, and returns a typed rejection rather than
silently normalizing malformed input. The ANF root is freshly recomputed as
the SHA-256 digest of those canonical bytes; no root field is stored in the
value.

## Refinement boundary

D01 names the roots that D02-D04 must bind into evaluation, receipt, bundle,
and outbox paths. D01 does not prove that any caller recomputes these roots,
does not authenticate supplied roots, and does not mount an API, datastore,
authority switch, proof verifier, or value-moving path.
