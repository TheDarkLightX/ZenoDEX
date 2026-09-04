# Choice-fiber treewidth coverage certificate V1

## Result

This research packet implements exact variable-elimination replay for a named
pseudo-Boolean polynomial and binds every scoped result into the existing
canonical ZRPF subcube coverage tree.

The verifier accepts one exact source polynomial, derives the ZRPF ordinal
manifest, substitutes fixed scope signs, derives the elimination bags and
separators, recomputes every message cell, and consumes an exact partition of
the whole choice cube. It returns the exact global minimum and canonical
minimizer.

The selected architecture prevents four important substitutions:

```text
semantic equality cannot replace exact polynomial lineage
one scope cannot reuse another scope's result
parallel scope and proof tuples cannot be independently reordered
a volume-matching leaf set cannot replace exact disjoint coverage
```

## Evidence

The deterministic packet contains:

```text
21 focused tests
6,457 bounded DP/oracle cases
51,656 direct oracle assignments
15 named semantic, authority, and resource mutants killed
0 surviving mutants
```

The retained counterexample

```text
f(y,z) = y + z + yz
```

has exact minimum `-1`. An unsound method that minimizes overlapping bags
independently reports `-3`, showing why exact separator messages are required.

## Usefulness

This extends the earlier affine, forest, and disconnected-component lanes to
arbitrary higher-order terms whose supplied elimination order stays within a
small induced-width bound. Exact ZRPF scopes can divide a larger scenario cube
while preserving complete assignment coverage.

The construction is suitable for bounded governance, alignment-margin, cartel,
and disaster-state experiments whose named variables and coefficient model are
already justified independently.

## Claim boundary

The packet is classified as:

```text
USEFUL_COMPOSITE_NOT_CURRENTLY_NOVEL
BOUNDED_RESEARCH_ONLY
Authority: NONE
```

Tree decomposition, bucket elimination, separator messages, pseudo-Boolean
optimization, and recursive subcube aggregation are established mathematics.
The packet has no RISC0 receipt, no production consumer, no settlement or
governance authority, and no claim of an optimal treewidth order. It does not
advance M6 or ZRPF production readiness by itself.

ZRPF may prove computation. ZenoLedger remains the only permitted selector and
publisher of an economic head.

## Sources

The source and replay packet is under:

```text
experiments/choice_fiber_treewidth_certificate_v1/
```

The packet checker pins both prerequisite implementations by SHA-256 and
regenerates the complete campaign report before accepting it.
