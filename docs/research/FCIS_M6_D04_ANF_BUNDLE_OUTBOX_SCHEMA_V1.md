# FCIS M6 D04 Bundle and Outbox Schema V1

## Canonical fields

`OutboxPlanV1` is encoded as a closed record with:

```text
records
authority_normal_form_root: optional lowercase 0x 32-byte digest
```

`CommitBundleClaimV1` is encoded as a closed record with:

```text
expected_pre_root
decision
receipt_root
outbox_plan
authority_normal_form_root: optional lowercase 0x 32-byte digest
```

The optional fields preserve legacy unbound replay claims. The D04 controlled
builder requires a complete exact ANF whenever the nested receipt contains an
ANF identity. Unknown fields, wrong arity, wrong types, and noncanonical
digests reject through the existing authority grammar.

## Cross-field invariants

For every admitted bundle claim:

```text
bundle.authority_normal_form_root
    == bundle.decision.receipt.binding.authority_normal_form_root
bundle.outbox_plan.authority_normal_form_root
    == bundle.authority_normal_form_root
```

For an ANF-bound authoritative bundle, the controlled wrapper additionally
retains the exact `FCISAuthorityNormalFormV1` value and checks:

```text
canonical_authority_normal_form_root_v1(bundle.authority_normal_form)
    == bundle.decision.receipt.binding.authority_normal_form_root
```

The bundle wire bytes commit to the ANF root through the nested decision and
the explicit outer field. They do not claim to be a production datastore
record or a standalone caller authorization witness.

## Recomputed relations

The D04 verifier reconstructs the receipt root from the exact decision, the
ANF root from the retained exact ANF, the outbox plan from the decision events
and receipt root, the outbox root from the recomputed plan, and the bundle bytes
and root from the admitted claim. Any mismatch rejects before the reference
publication atom is permitted to proceed.

