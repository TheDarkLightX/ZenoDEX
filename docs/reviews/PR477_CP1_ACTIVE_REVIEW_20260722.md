# PR #477 CP1 Active Review

Date: 2026-07-22

Scope: FCIS admission and owned-collection primitives only

Original implementation commit: `ea40986369b36f86aedecc3b4f1b1b5d660e1af7`

Reviewed base: `44d7f0d2a36b2141b553af1df734926c9d559bca`

Intended stack parent: `fc2f9150c1eacfdb7f6e4272f2a8efbd5fdafe85`

## Decision

**PASS FOR CP1 PRIMITIVE CHECKPOINT ONLY.**

This decision covers the closed schema interpreter, validated resource limits,
composition-owned maps and enums, the source-wide authority checker, and the
normative packet checker. It does not approve domain snapshots, `DexState`
mounting, the production profile facade, PR #478 authority/effect values, or a
merge-ready PR #477.

## Original implementation grade

| Dimension | Grade | Reason |
|---|---:|---|
| Spec fidelity | 1/5 | Added the explicitly rejected `BoundAdmissionV1` architecture and executed declarative registry types. |
| Authority safety | 1/5 | A caller could bind registry and resolver behavior outside the single source-pinned profile. |
| Determinism and totality | 2/5 | Common paths were typed, while resource work and rejection behavior remained incomplete. |
| Transitive ownership | 2/5 | Maps owned their index, while Python `Enum` singleton aliases survived admission. |
| Evidence quality | 2/5 | Broad gates passed against a stale matrix that omitted the decisive adversarial cases. |

The original checkpoint's passing test count did not establish conformance to
the corrected design. The corrected checker reproduced these two structural
violations directly:

```text
PROFILE_BINDING_ESCAPE          snapshot_combinators.py:421
DECLARATIVE_REGISTRY_EXECUTION  snapshot_combinators.py:1465
```

A runtime witness also showed that the original enum result was the same
mutable source singleton. Mutating `source_enum.value` after admission changed
the admitted result. A 100,000-entry rejected map allocated about 6.4 MB before
its one-item limit was applied.

## Corrected checkpoint grade

| Dimension | Grade | Reason |
|---|---:|---|
| Spec fidelity | 4.5/5 | The primitive follows the corrected closed-admission, composition-ownership, and single-profile design. |
| Authority safety | 4.5/5 | Production callers cannot select a registry, constructor, postcondition, encoder, or private construction token through the mounted source tree. |
| Determinism and totality | 4.5/5 | Stable traversal, typed rejection, graph budgets, canonical map order, and fail-closed resolver boundaries are executable. |
| Transitive ownership | 4.5/5 | Maps, enum values, sequences, pair keys, and records reconstruct from admitted children without caller-owned mutable aliases. |
| Evidence quality | 4.5/5 | The checkpoint has 155 focused tests, mutation tests for checker evasions, allocation witnesses, exact packet bindings, and independent adversarial review. |

The remaining half-point in each category belongs to the unimplemented
production profile and domain mounting. Those are later checkpoints.

## Repairs and rationale

1. Removed `BoundAdmissionV1` and its public builder.

   The only production API shape is a four-argument module facade that directly
   returns the private interpreter result. This prevents a caller from selecting
   registry or resolver behavior.

2. Replaced registry-driven construction with a module-owned construction
   resolver.

   Registry records remain declarative. The interpreter checks that the trusted
   resolver returns the exact registered owned type and preserves admitted child
   identities. Executable behavior cannot enter through registry data.

3. Added `OwnedEnumV1`.

   Python enum members are singleton objects with mutable reachable storage.
   Admission now validates the exact registered member and copies only schema,
   enum-tag, and member ordinals into a fresh composition-owned value.

4. Moved map cardinality checks before entry materialization.

   Exact dictionaries use the exact built-in length operation before allocating
   an entries tuple or sorted work list. The 100,000-entry one-item-limit witness
   now peaks below 500 KB.

5. Added bounded map-key sort preflight.

   Exact-shaped string and bytes key components, including nested pair keys, are
   checked against field and remaining graph-wide byte limits before sort-value
   derivation. Oversized and aggregate overflow paths return `BYTE_LIMIT` without
   invoking `_key_sort_value`.

6. Rejected missing instance fields before class defaults can repair them.

   Exact source type alone does not prove that every declared field exists in
   instance storage. Missing fields now return `MISSING_FIELD`.

7. Hardened the source-wide authority checker.

   Direct imports, module attributes, literal `getattr`, `setattr`, `delattr`,
   `vars(module)[name]`, and `module.__dict__[name]` cannot capture private engine,
   owned-construction, registry, or limit capabilities outside their allowlisted
   source boundary.

## Evidence

```text
pytest focused checkpoint                         155 passed
ruff check                                        passed
ruff format --check                               7 files already formatted
mypy                                              3 source files passed
packet checker                                    ok=true
packet evidence                                   34 findings, 39 requirements,
                                                  100 declared/bound test IDs,
                                                  77 referenced test IDs
authority checker                                 ok=true, zero violations
read-only compile()                               7 files passed
oversized-key witness, 1 MB                       0.000139 s, BYTE_LIMIT
oversized-key witness, 32 MB                      0.000174 s, BYTE_LIMIT
```

Reviewed source and evidence hashes:

```text
a68a18922208fd7b88b7cdaba6a2d6e1e5611a83e9db997270968f731daa7d5b  src/state/owned_collections.py
ecac7699075b1eb2cf4756915b183ee6b382fd89e60b91973d4fdf1da0dc1eca  src/state/snapshot_combinators.py
f4614195260a8129f87ab814e0c20f15b43a83309309d69f93a7f3e2dcdd4b0a  tools/check_fcis_authority_snapshot_contract.py
b6a6ecd212eb40926fbdf05b8fc62a53965a7b6348484f1d463efb9811f7f251  tests/state/test_snapshot_combinators.py
7b55af8a16fefcc38eab10dcc77bcfce460c2b9378666675b787699d9ff9d2d3  tests/tools/test_check_fcis_authority_snapshot_contract.py
78b7910516d0093640bf4f264d07ccf24b619bbfd241ab089cf7166c9698df40  tests/tools/test_fcis_authority_packet_checker.py
e16ea51d2df2aa2cc6df6d98ec14310b609ee86692ca68f987f37806612daec1  docs/specs/fcis_authority_snapshot_v1/requirements.json
2f436aa1080c70b2c3ec4afdeca099c097e3f280a0721de5bdb365f760941bbe  docs/specs/fcis_authority_snapshot_v1/check_packet.py
```

## Residual scope

- `src/state/state_admission_profile.py` remains intentionally absent.
- Domain schemas, snapshot adapters, scratch reconstruction, and `DexState`
  mounting remain unimplemented.
- State-byte and state-root parity remain unproved for the domain migration.
- PR #478 must wait for the mounted PR #477 boundary.
- Python trusted-process mutation through `object.__setattr__`, debugger, native
  extensions, or `ctypes` remains outside this checkpoint's threat model.
- The three broad exception catches are deliberate typed no-output boundaries
  around corrupted index lookup, trusted record construction, and canonical
  encoding.
- Persistent maps remain a later performance optimization after semantic parity
  and profiling. They are not part of this repair.

## Next checkpoint

Implement the source-pinned production profile with exhaustive construction and
encoder matches, then mount one domain snapshot family at a time. Every mounted
family must add source-alias mutation, scratch detachment, canonical byte/root
parity, rejection no-op, and registry-drift evidence before promotion.
