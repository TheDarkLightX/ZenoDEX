# FCIS M6 J07 authority switch

J07 is an isolated research relation for the migration edge

```text
QUIESCED -> AUTHORITY_SWITCH
```

The switch consumes a verifier-owned J06 quiescence gate and rechecks an F06
migration authorization at point of use. The complete successor context binds
the prior context, migration token root, phase, epoch, target writer profile,
authority root, durable snapshot root, and current head root.

The relation preserves the current state and deployment roots. It changes the
authority, snapshot, and head roots together, advances the epoch exactly once,
and enables exactly the target writer profile. A legacy writer token bound to
the predecessor context is rejected against the successor context. A fresh
target token bound to the successor context is accepted by the isolated writer
admission function.

The implementation uses verifier-owned construction tokens plus identity and
unchanged-field registries for J07 contexts and writer tokens. Exact-class
forged gates, forged F06 tokens, mutated registered contexts, and mutated
registered writer tokens are rejected at point of use.

## Evidence

- independent checker: `J07_AUTHORITY_SWITCH_MATCH`
- public vector builder: `J07_AUTHORITY_SWITCH_VECTOR_MATCH`
- focused and property tests: 6 passed;
- adjacent J01-J06, F05, and F06 regression: 46 passed before the final
  packet freeze;
- exact implementation commit: `006e2507748d0de0525d636fdbb648b1f7f2f1e9`;
- exact implementation tree:
  `676590e5899ef150ed8aae476d66305023f92f58`;
- pinned switch root:
  `e44729c68c7b9de2876772f2d08123b048f1a6767dc26f45c10cec1f35e73fcb`.

The J07 fixture constructs a canonical history whose final authority row is
`QUIESCED`; its publication atom is authorized at the preceding
`DUAL_CHECK` epoch. This keeps the F06 reopened head and the J06 input phase
semantically aligned.

## Boundary

J07 is a deterministic functional-core model. The F06 verifier adapter is an
external authority premise. The J06 gate and J04 migration manifest are
research evidence inputs. No production datastore transaction, runtime writer
middleware, crash recovery, rollback, caller authentication, no-bypass audit,
accounting, backing, or zUSD safety theorem is claimed. M6 remains unmounted
and non-promotable.
