# FCIS M6 D04 Bundle and Outbox Schema Separation V1

## Canonical schema identities

Legacy, ANF-unbound values retain their exact existing schemas and fields:

```text
zenodex/fcis/outbox-plan/v1
  records

zenodex/fcis/commit-bundle/v1
  expected_pre_root
  decision
  receipt_root
  outbox_plan: zenodex/fcis/outbox-plan/v1
```

ANF-bound values use distinct V2 schemas with a required root:

```text
zenodex/fcis/outbox-plan/v2
  records
  authority_normal_form_root: lowercase 0x 32-byte digest

zenodex/fcis/commit-bundle/v2
  expected_pre_root
  decision
  receipt_root
  outbox_plan: zenodex/fcis/outbox-plan/v2
  authority_normal_form_root: lowercase 0x 32-byte digest
```

The V2 root is required. `null`, omission, unknown fields, wrong arity, wrong
types, and noncanonical digests reject through the closed authority grammar.
The V1 codecs remain byte-identical to their pre-D04 definitions.
V2 outbox and bundle roots use their V2 schema IDs and domain-separator version
`2`; legacy roots retain domain-separator version `1`.

## Cross-field invariants

For every admitted V2 bundle claim:

```text
bundle.authority_normal_form_root
    == bundle.decision.receipt.binding.authority_normal_form_root

bundle.outbox_plan.authority_normal_form_root
    == bundle.authority_normal_form_root
```

The controlled wrapper also retains the exact `FCISAuthorityNormalFormV1` and
requires:

```text
canonical_authority_normal_form_root_v1(bundle.authority_normal_form)
    == bundle.decision.receipt.binding.authority_normal_form_root
```

An unbound receipt can produce only a V1 outbox and bundle claim. An ANF-bound
receipt can produce only a V2 outbox and bundle claim.

## Commit-time recomputation

The reference commit port independently revalidates the complete relation
before publication and while reopening every retained publication:

```text
exact retained ANF
  -> recomputed ANF root
  -> receipt binding equality
  -> recomputed V2 outbox plan and root
  -> recomputed V2 bundle bytes and root
  -> publication permitted
```

Missing, foreign, crossed, or post-construction-corrupted ANF values return
`INVALID`, preserve the exact pre-store, and publish nothing. The schemas and
reference port remain unmounted research evidence.
