# Domain Test Matrix for PR #477 and PR #478

This file is the mandatory domain continuation of `TEST_MATRIX.md`. Both files
form one test contract.

## 1. PR #477 committed-state tests

Main target: `tests/core/test_dex_state_immutability.py`. Registry tests belong
in `tests/state/test_state_snapshot_schema_drift.py`.

### Tables and pools

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-477-001` | retain balance-table source aliases and nested entries | state bytes, root, and later behavior remain unchanged after mutation |
| `FCIS-T-477-002` | bool amounts, integer subclasses, malformed keys, corrupt raw balance internals | reject before any source getter, setter, or normalizer hook |
| `FCIS-T-477-003` | invoke old `BalanceTable.__init__` or mutator shape on committed balances | no applicable base route; value unchanged |
| `FCIS-T-477-004` | retain LP balance and duration-metadata aliases | ownership, duration, bytes, and root remain unchanged |
| `FCIS-T-477-005` | invoke old `LPTable.__init__` or mutator shape on committed LP state | no applicable base route; value unchanged |
| `FCIS-T-477-006` | retain nonce aliases and attempt replay-relevant mutation | committed nonce and replay behavior unchanged |
| `FCIS-T-477-007` | retain pool map, pool object, and every mutable child alias | reserves, fees, curve/config, quotes, bytes, and root unchanged |
| `FCIS-T-477-008` | pool subclass, dataclass lookalike, scalar subclasses, corrupt pool internals | exact reject before semantic `PoolState` construction |
| `FCIS-T-477-009` | mutate fresh scratch balance/LP/nonce/pool values | committed source unchanged; resnapshot reflects only explicit changes |

### Optional modules and perps

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-477-010` | retain vault, Oracle, and fee-accumulator child aliases | committed bytes and behavior remain unchanged |
| `FCIS-T-477-011` | optional-module subclass, lookalike, or unregistered value | exact reject; no generic optional-object fallback |
| `FCIS-T-477-012` | every supported perps market/account variant and nested container | exact owned schema; recursive type audit passes |
| `FCIS-T-477-013` | behavior-changing perps subclass at top level and nested in maps | exact reject; behavior methods not called |
| `FCIS-T-477-014` | temporary new dataclass field or registry variant | drift gate names the missing field or variant |
| `FCIS-T-477-015` | bool, subclass, below-minimum, and above-maximum in each perps scalar family | stable field-specific reject before update code |
| `FCIS-T-477-016` | mutate fresh perps scratch and resnapshot | old state unchanged; new state has only explicit change |

### Atomic admission and parity

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-477-017` | final `DexState` field invalid after earlier fields are valid | no state escapes; every source remains unchanged |
| `FCIS-T-477-018` | trusted fixture corrupts an already-owned value | full revalidation rejects; owned-looking values are not blindly trusted |
| `FCIS-T-477-019` | full state with every optional module and perps variant | bytes, state/support roots, reads, and transition effects equal pinned baseline |
| `FCIS-T-477-020` | rejected transition from committed state | no state, effect, receipt, nonce, outbox, or source mutation |
| `FCIS-T-477-021` | stateful quote, settle, LP, nonce, perps, reject, retry sequence | old roots stable; successors owned; retry deterministic |
| `FCIS-T-477-022` | property mutates every retained source alias | committed bytes and behavior invariant |
| `FCIS-T-477-023` | `snapshot(to_scratch(snapshot(x)))` on valid corpus | bytes and roots equal `snapshot(x)` |
| `FCIS-T-477-024` | mounted item/byte limits at bound and one over | behavior matches `FCIS-D009` |

## 2. PR #478 owned JSON and canonical ingress

Targets: `tests/state/test_owned_json.py` and the existing strict-decoder tests.

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-478-001` | every allowed JSON scalar/container at exact bounds | accepted into closed owned-JSON language |
| `FCIS-T-478-002` | bool-as-int, subclasses, set, wrong array type, custom mapping/iterable, arbitrary dataclass/enum | exact reject; no caller hook executes |
| `FCIS-T-478-003` | cycle, excessive depth, nodes, items, bytes, key length, and string length | corresponding stable bounded reject |
| `FCIS-T-478-004` | duplicate keys, alternate numbers, float, exponent, `-0`, BOM, trailing bytes, key order, alternate escapes | strict raw-byte ingress rejects before authentication |
| `FCIS-T-478-005` | canonical bytes decode to owned JSON and re-encode | byte-identical full-consumption round trip |
| `FCIS-T-478-006` | mutate fresh JSON projection used by legacy shell adapter | owned JSON and signed bytes unchanged |

## 3. PR #478 intent and signature ownership

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-478-007` | every intent kind at minimum/maximum valid fields | exact `OwnedIntentV1`, canonical bytes, stable field order |
| `FCIS-T-478-008` | missing, extra, duplicate-after-normalization, wrong-kind, and wrong-type fields | exact kind-indexed closed-field rejection |
| `FCIS-T-478-009` | mutable `Intent`, `ValidatedIntent`, subclass, lookalike, and mapping sources | only registered exact source types accepted |
| `FCIS-T-478-010` | mutate `Intent.fields` and nested aliases after snapshot/signing | signature message, nonce, route, recipient, and execution unchanged |
| `FCIS-T-478-011` | invoke old `Intent.__init__`, `set_field`, or attribute mutation shape | no mutable-base route exists |
| `FCIS-T-478-012` | mutate/reorder/append retained input batch list | admitted tuple and canonical batch root unchanged |
| `FCIS-T-478-013` | batch lengths 0, 1, 256, and 257 | declared valid boundaries accepted; 257 rejected |
| `FCIS-T-478-014` | parser and owned-intent registries differ in fixture | drift checker names missing kind/field |
| `FCIS-T-478-015` | parse, own, sign, and decode through supported verifier/proof adapter | exact message and fields agree byte-for-byte |

## 4. PR #478 settlement and effects

| ID | Required case | Required result |
|---|---|---|
| `FCIS-T-478-016` | settlement with all fills, deltas, intents, and event families; retain all aliases | owned settlement remains byte/behavior stable after source mutation |
| `FCIS-T-478-017` | mutable subclass, child subclass, dataclass lookalike, or corrupted owned value | exact reject; no copy or semantic hook executes |
| `FCIS-T-478-018` | bool, subclass, negative, and overflow in every fill/delta scalar family | exact field-bound reject before effect construction |
| `FCIS-T-478-019` | inspect every owned settlement dataclass field | protocol fields only; no seal/cache/index metadata |
| `FCIS-T-478-020` | event payload at JSON bounds and with forbidden values | bounded owned JSON; `EVENT-TYPING-001` remains open |
| `FCIS-T-478-021` | effect receives wrong settlement type, subclass, or recomputed lookalike | reject; exact owned settlement required |
| `FCIS-T-478-022` | accepted step with fees, fills, events, and deltas | state, effect, receipt, and hashes use one owned candidate |
| `FCIS-T-478-023` | reject at final effect consistency check | no state, settlement, effect, receipt, nonce, or outbox escapes |
| `FCIS-T-478-024` | canonical full settlement/effect fixture | bytes, hashes, fees, ordering, and mounted behavior equal baseline |
| `FCIS-T-478-025` | sign, queue, reorder attempt, execute, retry/replay sequence | signed meaning, order, nonce, and rejection remain deterministic |
| `FCIS-T-478-026` | property partitions and rejoins canonical intent batch | sequence unchanged; no element aliases source data |

## 5. Static checker mutation tests

Target: `tests/tools/test_check_fcis_authority_snapshot_contract.py`.

| ID | Injected violation | Required result |
|---|---|---|
| `FCIS-T-STATIC-001` | `copy.copy` or `copy.deepcopy` | nonzero forbidden-copy result |
| `FCIS-T-STATIC-002` | `pickle` or copy-protocol reconstruction | nonzero forbidden-reconstruction result |
| `FCIS-T-STATIC-003` | authority function contains `typing.Any` | nonzero open-authority-type result |
| `FCIS-T-STATIC-004` | committed class inherits mutable container/domain class | nonzero mutable-base result |
| `FCIS-T-STATIC-005` | broad mapping/iterable or authority-base `isinstance` | nonzero broad-admission result |
| `FCIS-T-STATIC-006` | reflective dataclass/enum admission | nonzero reflective-admission result |
| `FCIS-T-STATIC-007` | `object.__new__` constructor bypass | nonzero constructor-bypass result |
| `FCIS-T-STATIC-008` | registry entry missing | nonzero registry-drift result |
| `FCIS-T-STATIC-009` | requirement lacks mapped test/evidence | nonzero uncovered-requirement result |
| `FCIS-T-STATIC-010` | compliant miniature tree | zero with sorted JSON rule results |
| `FCIS-T-STATIC-011` | alias a private admission/owned-construction capability or replace the profile result | nonzero private-capability or profile-facade result |

## 6. Required properties

```text
FCIS-PROP-001  source-alias mutation invariance
FCIS-PROP-002  scratch round-trip canonical equality
FCIS-PROP-003  canonical map permutation invariance
FCIS-PROP-004  deterministic rejection permutation invariance
FCIS-PROP-005  Python encoder parity with existing strict reference
FCIS-PROP-006  pinned versus repaired behavior on canonical valid corpus
FCIS-PROP-007  reject-is-no-output across every admission phase
FCIS-PROP-008  source registry equals parser/runtime/adapter registry
FCIS-PROP-009  one accepted value has one accepted authority encoding
FCIS-PROP-010  equal state/command/context replay is byte-identical
```

## 7. Closure evidence

A row is `SATISFIED` only when the exact-head handoff binds its test node ID,
pre-repair witness or structural rationale, post-repair result, exact command,
source SHA, and relevant artifact hash. `SKIPPED`, `XFAIL`, weakened assertions,
or an infrastructure failure leave the row open.
