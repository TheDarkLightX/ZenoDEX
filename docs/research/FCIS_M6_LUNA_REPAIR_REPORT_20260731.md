# FCIS M6 Luna Durable-Retraction Repair Report

**Contract:** `fcis-m6-durable-retraction-luna-repair-v1`  
**Date:** 2026-07-31  
**Posture:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`

## Exact source and topology

- Base commit: `babffa56dcbddc5886487fbb6e62740b15370000`
- Base tree: `eb6771943bc490d1f9664d26ec14622a8849b010`
- Repair branch: `agent/fcis-m6-r05-r11-durable-retraction-20260731`
- Implementation target commit: `84b344e3fac132047d83a61cf70ecd687c494161`
- Implementation target tree: `2137a36506de39d9c2c15add477a5f985c059440`
- Implementation target parent: the declared base commit above
- Packet child commit: recorded in the final handoff after this report is committed

The target commit contains only implementation, tests, bounded models, ESSO,
Lean, and the read-only CI workflow. The later packet child contains research
documents, exact repair inputs, the source manifest, inventory, nonclaims, and
the canonical archive.

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
than silently choosing one projection.

## Repair claims and evidence

1. Reopen authorization now requires a controlled verifier-produced witness
   bound to the exact snapshot, current state, authority epoch, deployment
   configuration, verifier profile, statement, and freshness interval.
2. Acknowledgment now requires a controlled destination-verifier receipt bound
   to effect, destination, payload, receipt, adapter, idempotency, and response
   identities. A raw or locally recomputed receipt is rejected.
3. Public boundary values use exact types, u32 checks, bounded row counts, and
   a canonical-byte budget. Invalid crash-point values return typed rejection
   without mutating the snapshot.
4. Lean models partial reopen with `Except Reject A` and compiles the required
   connective theorem set.
5. ESSO, Python, and Julia use explicit verified environment-premise vocabulary.

Permanent witnesses retained in
`tests/core/test_fcis_durable_retraction.py` cover self-selected authorization,
changed-head authorization, cross-deployment and cross-epoch authorization,
raw/local destination receipts, crossed effect/destination/payload/verifier
receipts, u32 maximum-plus-one and Boolean aliases, invalid string crash points,
oversized tables, the Lean partial-reopen shape, and the ESSO grant premise.

## Exact local verification

The following gates passed in the isolated worktree:

```text
python3 -m py_compile ...                              PASS
python3 -m ruff check ...                              PASS
python3 -m ruff format --check ...                     PASS
python3 -m mypy src/core/fcis_durable_retraction.py    PASS
python3 -m pytest -q tests/core/test_fcis_durable_retraction.py
29 passed
```

The Python bounded explorer reports `max_depth=14`, 49 safe reachable states,
254 safe transitions, and seven killed mutants. Its generated JSON is
structurally and byte-identical to the frozen result. The Julia oracle is
structurally identical to the Python result.

ESSO was run from clean pinned checkout
`ef5b06cb7dbed9e8a78d27e9918550ee591e42eb`. `validate` passed. `verify-multi`
passed 15/15 inductive queries, with Z3 4.15.4 and CVC5 1.1.2 agreeing on every
query, no UNKNOWN, no timeout, no disagreement, and deterministic fingerprints.

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

## Nonclaims and unrun gates

- The Python verifier adapters are deterministic research boundary models. They
  do not establish production signer, quorum, deployment, or destination trust.
- No concrete SQLite/PostgreSQL schema, WAL/crash refinement, production CAS,
  authenticated genesis, live destination contract, or complete publisher
  inventory is proved.
- No runtime mount, authority switch, deployment, value movement, migration,
  merge, or production compatibility decision was performed.
- The repository triage scripts named by the prompt were not present in the
  isolated worktree or its parent checkout. Each exact invocation failed with
  `python3: can't open file ...: [Errno 2] No such file or directory`.
- The peer-review subprocess timed out without returning a review. No peer
  review result is claimed.
- Remote push, draft PR creation, exact-head remote CI, and artifact upload are
  pending the final packet publication step.

The safe next step is a read-only review of the exact implementation target and
documentation-only packet child on the dedicated draft PR. Keep the PR draft
and unmounted until the concrete datastore, external-verifier, destination,
and no-bypass evidence exists.
