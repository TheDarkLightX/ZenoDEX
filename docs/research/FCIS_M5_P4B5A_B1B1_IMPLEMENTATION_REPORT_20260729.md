# FCIS M5-P4B5A B1B-1 exact-head repair report

```text
status: IMPLEMENTED_UNMOUNTED_EXACT_HEAD_REPAIR_PENDING_REVIEW
checkpoint: B1B-1
repaired implementation code head before this report:
  83a45dbfe5821e38bfaf6389aa3aeaad366580de
prior reviewed exact-head target:
  a48ac55385cc22d62b5ca00339d60da443d73be6
prior reviewed packet commit:
  98a7c8e171534769d1b5542c388c5b06a5abd3d8
prior repair code head:
  1bba350babe1d7b0eaac11501b6f93b2fc8fa440
original refuted implementation target:
  221f7d1c6d6aab4baa01327da2801793ec31abc2
approved Revision 3.4 target:
  a8b9d191b91a3258e3d7857784bbd6067a0463e1
approved Revision 3.4 packet:
  1665e788a4c4daf43982262c307d0c04b914d89b
approved verdict:
  APPROVE_B1B1_REVISION_3_4_UNMOUNTED
approved Revision 3.4 document SHA-256:
  cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5
```

## Result

The repair retains every earlier exact-head correction and closes the two Rust
source-layout counterexamples reported by independent review:

1. all four Python carrier modules reject direct and transitive carrier aliases,
   method capture, dynamic namespace replacement, and post-definition identity
   mutation;
2. an isolated full-closure import probe verifies class identity, exact bases,
   generated equality and hashing, validation hooks, module bindings, invalid
   sentinels, and canonical dataclass fields;
3. admission and canonical projection use standalone pure field validators, so
   hostile replacement of a class hook cannot bypass point-of-use validation;
4. item-aware Rust scanning blanks only complete top-level `cfg(test)` modules,
   inspects production items before, between, and after them, collects balanced
   multiline outer attributes, and closes inherent-implementation, trait,
   macro, const, static, type-alias, and public-function construction surfaces;
5. every Rust encoder and root function freshly revalidates the value and
   returns a typed result;
6. dedicated CI checks out the exact pull-request head, verifies that identity,
   checks the exact packet topology, exports and rechecks the delivery, and
   uploads the verified evidence.

The checkpoint remains carrier-only and unmounted. B1B-2 is not authorized by
this repair.

## Invariant and authority impact

The implemented relation remains:

```text
arbitrary untrusted bytes
  -> deterministic byte and JSON resource bounds
  -> closed structural admission or typed rejection
  -> exact immutable untrusted carrier
  -> canonical bytes
  -> optional audit root
```

For each admitted carrier value `x`, the checked closure requirement is:

```text
stored_fields(x) = schema_fields(x)

canonical_bytes(x) = canonical_bytes(y)
  -> x = y
```

The carrier result cannot construct or authorize:

```text
pinned deployment verifier
verified migration authority
migration candidate or successor
committed V2 state
state-bound configuration
configuration update
transition cause or evaluation candidate
receipt, decision, outbox plan, or commit bundle
proof input
publication
runtime mount
```

## Bounded decoder repair

Python and Rust now share these exact limits:

```text
maximum canonical input bytes:       65,536
maximum JSON nesting depth:          32
maximum total JSON nodes:            256
maximum collection members/elements: 64
```

The Python decoder performs a lexical resource scan before `json.loads` and
returns closed rejection codes for byte, UTF-8, depth, node, and collection
limits. `RecursionError` is also caught as defense in depth. Duplicate-key and
JSON-shape handling remains downstream, with resource-limit precedence frozen
by tests.

The shared golden fixture contains exact-at-limit and limit-plus-one vectors
for arrays, objects, mixed nesting, collection size, total nodes, byte size,
and invalid UTF-8. Python and Rust consume the same descriptors.

## Exact carrier closure and authority isolation

The Revision 3.4 structural checker now enforces:

```text
exact ordered Python carrier field sets
exact ordered Rust carrier field sets
exact schema registries
frozen, slotted, final Python value identity
no carrier inheritance, metaclass, or decorator drift
runtime dataclass field equality with the canonical schema registry
no post-definition carrier identity replacement
no sibling-module or transitive-alias identity mutation
no dynamic namespace replacement or carrier method capture
exact Rust derive and implementation surfaces
balanced multiline Rust outer-attribute closure
production-item inspection before, between, and after test modules
no generated, trait, macro, or unchecked Rust constructor
no carrier-bearing top-level const, static, or type-alias surface
fallible point-of-use Rust encoder validation
private Rust fields
no custom equality or hashing
no independent stored properties or class authority state
closed constructor and codec function inventories
global forbidden-authority symbol scanning
global carrier-consumer scanning across bounded runtime roots
exact Rust lib.rs export surface
fail-closed handling of unreadable, oversized, or novel runtime paths
```

The checker currently scans 936 Python and Rust runtime files and reports zero
findings. Its disk-bounded mutation suite kills:

```text
direct and inherited Python carrier fields
Python base classes, hidden properties, metaclasses, and extra decorators
custom or post-definition Python equality, hashing, and validation replacement
module-level assignment, setattr, delattr, and type-level mutation
sibling-module validation bypass and transitive alias mutation
globals/vars replacement and carrier method capture
extra Rust derives, trait constructors, macros, and unchecked constructors
post-test and between-test Rust constructors, trait implementations, helpers,
macros, constants, and type aliases
multiline cfg_attr derives and attribute macros
deleted Rust encoder revalidation
direct extra Rust carrier fields
Rust publication helper in lib.rs
forbidden pinned-verifier type in a novel path
aliased and fully-qualified Python carrier consumers
neutral-name Python authority consumer
private Rust alias consumer
premature authority builders and runtime mounts
```

## Deletion-aware exact-head packet

The packet builder now parses NUL-delimited Git name-status output with rename
and copy detection. It accepts the complete bounded status set and records
deleted files as tombstones containing the base blob identity and SHA-256.

The packet metadata binds:

```text
approved base commit and tree
implementation target commit and tree
documentation-only packet commit and parent
complete status-aware change inventory
target-present source hashes
Cargo workspace closure and canonical dependencies
```

The delivery export contains the packet files, an incremental Git bundle from
the approved base through the packet commit, and an external receipt. The
receipt avoids a self-referential commit-hash construction. Delivery checking
verifies the bundle hash and advertised HEAD, derives the packet's actual sole
parent and exact five-path diff, derives the base, target, and packet trees,
requires approved-base ancestry, and compares the packet bytes with both the
receipt and committed blobs.

## ATDD evidence

The Git-aware acceptance gate reports:

```text
acceptance_case_count: 20
b1b1_case_count: 12
b1b2_case_count: 8
changed_path_count: 30
errors: []
ok: true
phase_order: [B1B-1, B1B-2]
```

The B1B-1 promotion rule remains fail closed. B1B-2 cannot begin until an
independent exact-head review returns the required B1B-1 approval verdict.

## Evidence

Commands run at repaired code head
`83a45dbfe5821e38bfaf6389aa3aeaad366580de`:

```text
python3 -m pytest -q <focused B1B-1 carrier, checker, and packet tests>
  160 passed

python3 -m pytest -q <three B1A configuration suites>
  14 passed

python3 -m pytest -q tests/tools/test_check_fcis_authority_snapshot_contract.py
  -k p4b5a
  18 passed, 334 deselected

cargo test -p zenodex-runtime-core --lib fcis_b1b_authority
  9 passed

python3 -m tools.build_fcis_b1b_authority_v2_golden --check
  passed

python3 -m tools.check_fcis_b1b_revision34_contract --json
  ok=true, findings=[], required_path_count=17, runtime_files_scanned=936

python3 -m tools.check_fcis_m5_p4b5a_atdd_contract \
  --assigned-id ATDD-B1B1-009 \
  --diff-base 1665e788a4c4daf43982262c307d0c04b914d89b
  ok=true, acceptance_case_count=20, b1b1_case_count=12,
  b1b2_case_count=8, changed_path_count=30

ruff check <complete focused B1B-1 Python surface>
  passed

mypy <four carrier modules and the Revision 3.4 structural checker>
  passed

cargo fmt -p zenodex-runtime-core -- --check
  passed

cargo check -p zenodex-runtime-core --lib
  passed

cargo clippy -p zenodex-runtime-core --all-targets -- -D warnings
  passed

git diff --check
  passed
```

## Commands not run

This report does not claim:

```text
complete repository pytest
complete repository mypy
repository-wide critical quality gate
hosted GitHub Actions at the repaired exact head
Lean, ESSO, Tau, SMT, or proof-system verification of B1B-1
repo-local style-map and security red-flag preflight, unavailable in the
bounded exact-head worktree
```

The next packet commit and exported bundle are generated after this report is
committed, so their identities belong to the packet metadata and delivery
receipt rather than this implementation report.

## Residual risk and non-claims

B1B-1 establishes only bounded exact untrusted carriers, canonical Python/Rust
bytes and roots, and a checked absence of authority consumers in the reviewed
surface. It establishes no deployment identity, migration legitimacy, current
state, configuration authority, publication atomicity, datastore
linearizability, governance authorization, content availability, crash
recovery, proof integration, or value movement.

The resource scanner deliberately bounds denial-of-service exposure; it is not
a general-purpose JSON parser proof. The structural checker is a deterministic
repository gate over declared runtime roots. Arbitrary code execution that can
replace the checker or its inventory remains outside the claim.

## Next safest step

Commit this report as the corrected implementation-review target. Generate one
documentation-only child packet, export its Git bundle and delivery receipt,
and obtain:

```text
APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
```

before beginning B1B-2 design or implementation.
