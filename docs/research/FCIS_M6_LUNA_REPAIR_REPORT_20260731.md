# FCIS M6 Luna Durable-Retraction Repair Report

**Contract:** `fcis-m6-durable-retraction-luna-repair-v1`  
**Date:** 2026-07-31  
**Posture:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`

## Exact source and topology

- Base commit: `babffa56dcbddc5886487fbb6e62740b15370000`
- Base tree: `eb6771943bc490d1f9664d26ec14622a8849b010`
- Repair branch: `agent/fcis-m6-r05-r11-durable-retraction-20260731`
- Original implementation commit: `84b344e3fac132047d83a61cf70ecd687c494161`
- Original packet commit: `eba5f91e21b9bb901325382158de887135c4bec7`
- Reviewed functional implementation target commit: `38c49c5be268a1c758e98f6b4b8ca131c1f054c6`
- Reviewed functional implementation target tree: `7830632e7a00838ede43d309e037d58e5128b0d0`
- Exact-head delivery implementation target commit: `c5954655616629b657bb546207f11af518f897a8`
- Exact-head delivery implementation target tree: `e5a0c6040813570a811181a6d718234cdccb446b`
- Exact-head delivery target parent: reviewed functional implementation target above
- Final packet child: exactly one documentation-only child of the exact-head
  delivery target. The post-commit receipt records its commit, tree, parent
  commit/tree, manifest digest, archive digest, and every packet-file digest.

The reviewed functional target contains the implementation, tests, ESSO, and
Lean repairs. The exact-head delivery target changes only the read-only
workflow: it validates the complete manifest/archive relation, regenerates the
canonical archive, generates a post-commit receipt, and uploads the verified
archive and receipt. The final packet child contains research documents, exact
repair inputs, the source manifest, inventory, toolchain record, nonclaims, and
the canonical archive. The two intermediate documentation commits from the
earlier delivery attempt are excluded from the final delivery topology.

## Post-commit delivery receipt

The packet cannot contain its own commit, tree, or archive digest without a
self-referential hash. The authoritative final handoff is therefore generated
after the packet child is committed as
`artifacts/fcis-m6-external-delivery-receipt.json`. The delivery workflow
binds the receipt to the repository, branch, exact PR head, reviewed functional
target commit/tree, packet commit/tree/parent commit/tree, manifest path/hash,
archive path/hash, and all archive member hashes. The receipt is uploaded
alongside the verified archive and is excluded from the canonical packet
archive.

Reviewed input hashes:

| Artifact | SHA-256 |
| --- | --- |
| `fcis-m6-durable-retraction-tree.tar.gz` | `3d1ac7ed5d9404cc4b293a9707502e4e4d8d714498448501b4b878d7b8afcd70` |
| `fcis-m6-durable-retraction-bundle.zip` | `8e1c5cea2588682f84da2a9fe71f7e1b2bacd79143f1df12695d4542e81d9890` |
| `fcis-m6-durable-retraction-luna-repair-v1.zip` | `341ad62d45a3ff6cfa3b6437b482302654880f96c6c97e3fc505dd8db6c39a37` |
| `LUNA_PROMPT.md` | `acadf5085f77b640c6008f8321f280880e652e56fb22609cfbb0eef548efa94b` |
| `REVIEW_AND_REPAIR_SPEC.md` | `322f9de857b7ca073f40b280c2057cc69184622e06d547a82fa1ae8fe2f096b4` |
| `REPAIR_TASKS.json` | `373fb78412cfb8a74bfe90cd363e1b5e938c1930f00e8cdff5a557b69d36ed39` |

The reviewed source ZIP and TAR share 15 common files. The ZIP alone contains
`README_BUNDLE.md` and `SHA256SUMS.txt`; the TAR alone contains
`lean-mathlib/lakefile.lean`. The canonical packet declares the union rather
than silently choosing one projection. Its archive contains the 29 manifest
files, the root `SHA256SUMS.txt` ledger, and the source manifest itself: 31
members total. The archive excludes itself.

## Repair claims and evidence

1. Reopen authorization now requires raw evidence to pass through a
   shell-owned verifier adapter, an opaque verifier-produced grant, and core
   grant admission before a controlled witness can be constructed. The subject
   binds exact snapshot, current state, authority epoch, deployment
   configuration, verifier profile, statement, and freshness interval.
2. `deliver_effect` no longer constructs a destination response. It requires a
   shell-owned adapter to return an opaque verified receipt. Raw responses and
   caller-constructed structural receipts are rejected. `lose_ack` requires an
   exact Boolean.
3. Publication atoms and retry classification are bound to deployment and
   verifier context. Effect identity excludes adapter profile rotation while
   outbox and acknowledgment rows retain adapter provenance.
4. Migration rejects identical legacy and target writer roots and binds every
   transport transition to its predecessor authority root, lifecycle phase, and
   writer set. Malformed snapshot, atom, crash, Boolean, and output values fail
   closed with typed rejection; `CommitAttemptV1` validates its carried output.
5. Lean models partial reopen with `Except Reject A` and compiles the required
   connective theorem set. ESSO, Python, and Julia use explicit verified
   environment-premise vocabulary.

Permanent witnesses retained in
`tests/core/test_fcis_durable_retraction.py` cover raw self-selected
authorization, changed-head authorization, cross-deployment and cross-epoch
authorization, wrong-subject verifier grants, missing destination adapters,
raw/local destination receipts, crossed effect/destination/payload/verifier
receipts, adapter-profile rotation, identical migration roots, forged
transition roots, u32 maximum-plus-one and Boolean aliases, invalid string
crash points, oversized tables, malformed commit outputs, the Lean
partial-reopen shape, and the ESSO grant premise.

## Exact local verification

The following gates passed in the isolated worktree:

```text
python3 -m py_compile ...                              PASS
python3 -m ruff check ...                              PASS
python3 -m ruff format --check ...                     PASS
python3 -m mypy src/core/fcis_durable_retraction.py    PASS
python3 -m pytest -q tests/core/test_fcis_durable_retraction.py
39 passed
```

The Python bounded explorer reports `max_depth=14`, 49 safe reachable states,
254 safe transitions, and seven killed mutants. Its generated JSON is
structurally and byte-identical to the frozen result. The Julia oracle is
structurally identical to the Python result.

ESSO was run from clean pinned checkout
`external/ESSO-ci` at commit `ef5b06cb7dbed9e8a78d27e9918550ee591e42eb`, tree
`478db05f8f75f5c7cf0fe6164c097f0ea398cb32`. `validate` passed.
`verify-multi` passed 15/15 inductive queries, with Z3 4.15.4 and CVC5 1.1.2
agreeing on every query, no UNKNOWN, no timeout, no disagreement, and
deterministic fingerprints.

Lean used toolchain `leanprover/lean4:v4.27.0`, Lean commit
`db93fe1608548721853390a10cd40580fe7d22ae`, and mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`:

```text
cd lean-mathlib
lake update                         PASS
lake exe cache get                  PASS
lake build Proofs.FCISDurableRetraction PASS
lake env lean Proofs/FCISDurableRetraction.lean PASS
```

The direct axiom audit reports no `sorryAx`, user axiom, or unsafe dependency.
The ordinary connective proofs use Lean's `propext` theorem dependency only.

The exact dependency and tool versions are recorded in
`docs/research/FCIS_M6_LUNA_TOOLCHAIN_V1.json`. The workflow uses
`requirements-dev.lock.txt` with SHA-256
`8ae2a245984d66a60e7fde6c0504b79b1de8fbcc86027b2a42c4adb7164229d8`, checks
the supplied repair-input sums, and checks the exact ESSO and mathlib commit
and tree values.

## Nonclaims and unrun gates

- The Python verifier and destination adapters are deterministic research
  boundary models. They do not establish production signer, quorum, deployment,
  or destination trust. Python object-construction privacy is not claimed as
  cryptographic unforgeability.
- No concrete SQLite/PostgreSQL schema, WAL/crash refinement, production CAS,
  authenticated genesis, live destination contract, or complete publisher
  inventory is proved.
- No runtime mount, authority switch, deployment, value movement, migration,
  merge, or production compatibility decision was performed.
- The repository triage scripts named by the prompt were not present in the
  isolated worktree. Each exact invocation failed with `python3: can't open
  file ...: [Errno 2] No such file or directory`; these scanners are not
  claimed.
- Repository-wide pytest collection remains outside this focused gate and has
  unrelated pre-existing import failures, including missing `cbor2`, missing
  integration exports, and absent `external/ESSO` wiring. The focused gate is
  the declared M6 command and passes.
- The exact-head delivery target and packet child are prepared for a draft PR.
  The hosted packet-delivery job is the acceptance gate for the final branch:
  it checks the exact PR head, one-child topology, both ledgers, every manifest
  file, archive membership and bytes, deterministic archive regeneration, and
  post-commit receipt upload. Hosted CI results and the generated receipt are
  not claimed until that run completes.

The safe operational next step is the delivery-only draft PR and exact-head
workflow run. Keep the work unmounted until concrete datastore,
external-verifier, destination, and no-bypass evidence exists.
