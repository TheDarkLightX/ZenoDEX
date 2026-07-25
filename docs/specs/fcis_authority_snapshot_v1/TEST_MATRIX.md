# Mandatory Test Matrix

Status: **normative for PR #477 and PR #478**

The PR-specific domain rows continue in `TEST_MATRIX_PR477_PR478.md`. Both
files form one mandatory test contract.

Every row is required unless implementation stops with a source-pinned
contradiction. A replacement test must exercise the same authority boundary and
the handoff must record the old ID, replacement node ID, and reason.

## 1. Rules

1. Capture each minimized witness against the pinned pre-repair head first.
2. Preserve every witness as a permanent negative regression.
3. Assert exact rejection code and field path when this packet specifies them.
4. Assert rejection returns no candidate authoritative value.
5. Assert source objects remain unchanged after acceptance and rejection.
6. Exercise retained aliases, inherited initializers, direct child references,
   hostile protocol hooks, and repeated initialization.
7. Use injected small limits for fast boundary tests; separately exercise the
   mounted production limits with compact fixtures.
8. Parameterize declared record, enum, intent-kind, and perps-variant
   registries. A new variant must make a drift test fail before mounting.
9. Record property-test seeds and serialize minimized failures canonically.
10. Each broad mechanism in `AUDIT_FINDINGS.md` needs its own hostile witness.

## 2. Shared deterministic-combinator tests

Target: `tests/state/test_snapshot_combinators.py`.

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-COMB-001` | `ExactInt` at both bounds and their neighbors | bounds accepted; outside is `OUT_OF_RANGE` |
| `FCIS-T-COMB-002` | `ExactInt` receives bool, int subclass, and object with `__int__` | `WRONG_EXACT_TYPE`; hook never called |
| `FCIS-T-COMB-003` | `ExactBool` receives bool, `0`, `1`, and bool-like object | only exact bool accepted |
| `FCIS-T-COMB-004` | string/bytes receive exact built-ins, subclasses, and conversion objects | only exact bounded built-ins accepted; hooks never called |
| `FCIS-T-COMB-005` | registered enum, foreign enum, `IntEnum`, raw int, and string alias | only exact registered member accepted |
| `FCIS-T-COMB-006` | exact tuple/list plus subclasses, generator, custom iterable, set, and frozenset | only schema-declared exact source container accepted; custom iterator not called |
| `FCIS-T-COMB-007` | exact dict in varied insertion order plus dict subclass, custom mapping, and hostile `items` | only declared exact source accepted; hostile hooks not called |
| `FCIS-T-COMB-008` | exact record, subclass, identical arbitrary dataclass, named tuple, and mapping | only exact registered source record accepted |
| `FCIS-T-COMB-009` | unknown schema, record, enum, or variant; registry/field drift | stable `UNSUPPORTED_VARIANT` for an unknown tag/type or `REGISTRY_DRIFT` for declared-schema drift |
| `FCIS-T-COMB-010` | direct self-cycle and two-object indirect cycle | stable `CYCLE`; no `RecursionError` |
| `FCIS-T-COMB-011` | one acyclic child shared by two legal fields | accepted; sharing is not misclassified as a cycle |
| `FCIS-T-COMB-012` | exact depth limit and one level beyond | boundary accepted; next is `DEPTH_LIMIT` |
| `FCIS-T-COMB-013` | node, item, byte, string, and collection limits at bound and bound plus one | stable corresponding limit code |
| `FCIS-T-COMB-014` | two invalid children under different map insertion orders | identical code and path under fixed precedence |
| `FCIS-T-COMB-015` | two noncanonical alias spellings that a permissive normalizer would collapse | each independently rejects as `NONCANONICAL_SCALAR`; admission never normalizes or applies last-write-wins |
| `FCIS-T-COMB-016` | hostile copy, reduce, state, hash, equality, ordering, iteration, integer, and string hooks | rejection occurs before every hook |
| `FCIS-T-COMB-017` | render every `AdmitCode` twice | byte-identical code/path; no repr, address, locale, or exception text |
| `FCIS-T-COMB-018` | recursively inspect every successful owned result | only declared owned scalars, tuples, `OwnedMapV1`, records, and enums occur |
| `FCIS-T-COMB-019` | construct a limit profile with zero, negative, bool, subclassed-int, inverted, or over-policy fields | `BuildAdmissionLimitsV1` rejects before `Admit` can run; no authority value is inspected |
| `FCIS-T-COMB-020` | admit an exact enum whose `.value` is a retained mutable object, then mutate the source alias | output is a fresh `OwnedEnumV1`; bytes and owned fields remain unchanged |
| `FCIS-T-COMB-021` | submit a large exact dict under a one-item limit while tracing allocations | `ITEM_LIMIT` occurs before an entry tuple or sort work list proportional to source length |
| `FCIS-T-COMB-022` | submit an oversized string/bytes map key or aggregate pair-key byte overflow while forbidding sort-value derivation | `BYTE_LIMIT` occurs before any raw key sort; nested pair components share the graph budget |
| `FCIS-T-COMB-023` | admit a heterogeneous map through an exact record union, then submit a subclass, lookalike, and unknown record | each exact registered class becomes its distinct owned class; all other classes reject before field access |
| `FCIS-T-COMB-024` | exercise character and UTF-8 byte bounds independently, including multibyte values and map keys | each exact boundary is accepted; either bound plus one returns stable `BYTE_LIMIT` |

## 3. Owned collection tests

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-OWNED-001` | retain source collection aliases | later source mutation has no effect |
| `FCIS-T-OWNED-002` | call `OwnedMapV1.__init__` twice | deterministic reject; bytes and contents unchanged |
| `FCIS-T-OWNED-003` | invoke old base-class mutator/initializer shapes | impossible because no mutable base exists |
| `FCIS-T-OWNED-004` | mutate a non-authoritative presentation projection | committed value remains unchanged; no mutable core projection exists |
| `FCIS-T-OWNED-005` | encode all insertion permutations | identical canonical order and bytes |
| `FCIS-T-OWNED-006` | try to insert an unowned child via public construction | no bypass; closed admission is required |
| `FCIS-T-OWNED-007` | inspect mutable bases, `__dict__`, and child references | none are exposed by committed collections |
