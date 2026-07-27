# FCIS Exact Product Combinator V1

Status: implementation prerequisite for M5-P4B0; unmounted.

## Purpose

Authority evidence contains canonical JSON arrays whose positions have different
types. One example is:

```text
["zenodex/fcis-authority-state/v1", 0, 0]
```

The existing algebra could admit a homogeneous sequence or an exact pair. It
could not admit this flat heterogeneous sequence without changing its shape or
moving structural validation outside the closed admission engine.

`ExactProduct` is the minimal closed-algebra extension for that boundary.

## Why this mechanism

The rejected alternatives are:

- nested `ExactPair`, because it would require rewriting the canonical flat
  array into a different shape before admission;
- `SequenceOf`, because one inner schema cannot describe heterogeneous
  positions;
- `BoundedJsonValue`, because it admits an open structural language;
- `TaggedRecordOf`, because it admits registered record objects rather than a
  decoded array;
- post-decode hand-written field/type checks, because those create a second
  structural authority engine;
- caller-selected validators, constructors, callbacks, or resolvers.

## Schema

```python
ExactProduct(
    accepted_source_kinds: tuple[SequenceSourceKind, ...],
    elements: tuple[SchemaV1, ...],
)
```

The schema is a frozen slotted value. The registry builder accepts it only when:

1. `accepted_source_kinds` is a nonempty exact tuple;
2. every source kind is an exact `SequenceSourceKind` member;
3. source kinds are duplicate-free;
4. `elements` is a nonempty exact tuple;
5. arity does not exceed `MAX_COLLECTION_ITEMS_V1`;
6. every element schema is a valid closed `SchemaV1` value;
7. the complete schema graph is acyclic.

Schema construction is trusted configuration. Authority input cannot select
the source kinds, arity, element schemas, registry, resolver, or encoder.

## Admission relation

For schema `P` and source `x`:

```text
admit(P, x)
  -> AdmitOk(tuple(v_0, ..., v_n))
   | AdmitReject(code, path)
```

Admission follows this stable order:

1. inherited depth check;
2. exact source-kind check;
3. exact arity check;
4. collection-item budget check;
5. container node-budget charge;
6. active-container cycle check;
7. element admission from index `0` through index `n`;
8. inherited canonical-encoding check.

Wrong source type or arity returns `WRONG_CONTAINER` at the product path.
Collection or node exhaustion returns `ITEM_LIMIT`. Element failure preserves
the first failure and appends its numeric index to the path.

## Required laws

### Exact shape

```text
AdmitOk(P, x) -> exact_source_kind(P, x)
                  and len(x) = len(P.elements)
```

Subclasses and arbitrary iterables are rejected before their hooks run.

### Positional typing

```text
AdmitOk(P, x) = (v_0, ..., v_n)
-> admit(P.elements[i], x[i]) = v_i for every i
```

### Ownership

The returned value is an exact tuple containing only outputs already owned by
the child combinators. Later mutation of admitted list children cannot alter
the returned value.

### Determinism and error precedence

Equal schemas, inputs, limits, and source-owned registries produce equal owned
outputs or equal rejection code/path pairs. Multiple invalid positions always
report the lowest invalid index.

### Boundedness

The product consumes one node plus the nodes consumed by its children. It
inherits depth and canonical-byte accounting from the closed engine. Its arity
must satisfy both the trusted schema policy maximum and the active admission
profile's collection limit.

### Cycle safety

A product or child container already active on the current admission path
returns `CYCLE`; no element output escapes.

### Compatibility

Adding the unused schema variant does not alter `ExactPair`, `SequenceOf`, map
key ordering, existing registries, or mounted authority behavior.

## V1 non-goals

`ExactProduct` V1 is not:

- a map-key schema;
- a variable-arity sequence;
- a sum or tagged union;
- a JSON parser;
- a semantic domain constructor;
- permission to normalize a rejected shape before admission.

Map-key support would require a separately specified total-order law and
bounded preflight implementation.

## Promotion gate

P4B0 may use this variant only after the focused tests, full combinator suite,
state suite, structural authority profiles, Ruff, mypy, compilation, and diff
review pass at one exact commit. The P4B0 packet must then bind that reviewed
commit as its required ancestor.
