---
name: zeno-semantic-compressor
description: Refactor Zeno representations so invalid states, repeated validation, duplicate semantic tables, and compensating tests disappear. Use before adding tests for cardinality, ordering, uniqueness, identity, lifecycle, canonicality, caller-supplied derived values, or repeated closed vocabularies.
---

# Zeno Semantic Compressor

## Purpose

Remove degrees of freedom before adding compensating tests. Preserve separately
written independent oracles.

## Search questions

1. Which invalid states are representable?
2. Which derived facts are caller supplied?
3. Which closed vocabulary has multiple hand-maintained copies?
4. Which validations repeat at every read or commit?
5. Which tests disappear under a stronger type?
6. Which duplication is deliberate oracle independence?

## Preferred transformations

```text
Vec<T> plus cardinality/order/duplicate checks
  -> fixed array or bounded collection

arbitrary {id, data} entries
  -> array or map indexed by validated closed ID

caller-supplied root, index, or hash
  -> private construction and recomputation

status flag plus runtime checks
  -> typestate or closed sum type

caller order plus repeated sort/dedup
  -> canonicalize once behind a private field
```

Use one reviewed declarative table to generate enum discriminants, labels,
codes, inventory, parser/formatter, gate inventory, documentation, and
compatibility fixtures. Treat the deterministic generator as part of the trust
surface.

For an exact 12-lane registry, prefer `[LanePolicy; 12]` indexed by the closed
lane ID over an arbitrary vector with length, duplicate, order, linear lookup,
and revalidation logic.

## Workflow

1. Count semantic representations and synchronization tests.
2. Draw the current invariant-enforcement path.
3. Propose the smallest type/API change that removes freedom.
4. List impossible-state tests that can be deleted.
5. Preserve wire compatibility with independent fixed vectors.
6. Run mutation before and after the refactor.
7. Compare production/test/support SLOC, complexity, runtime, and mutant kills.
8. Record generator or macro trust-boundary changes and nonclaims.

Success requires stable or intentionally versioned public semantics, no loss of
critical mutation adequacy, fewer hand-maintained semantic copies, removal of
dead impossible-state tests, and continued oracle independence.
