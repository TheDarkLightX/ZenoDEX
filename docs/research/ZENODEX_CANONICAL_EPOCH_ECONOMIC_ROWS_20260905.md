# Canonical epoch economic rows

This W09 follow-up extends the checked epoch table-composition proof at
`d92dfa9b99ce973d9a410dd0ef70709ce8ea8bff`. It proves a canonical value
representation theorem. Universal Python execution and complete W09 remain
open.

## Constructed representation

The earlier proof returned a function from complete economic keys to signed
totals. That representation did not establish that runtime output tuples had
the same meaning. The new model constructs all three relevant stages:

1. `emitRows` collects complete keys from the ordered input, keeps one copy,
   sorts by `(kind.code, asset, principal, domain)`, replaces each delta with
   its checked total and omits zero totals. A separate theorem proves that
   reconstructing a row from its key is exactly equivalent to replacing the
   delta of any exemplar carrying that key.
2. `projectDeltaRows` selects one accounting table's effect kind and sorts
   records by `(table, owner, asset, domain, delta)`.
3. `checkedStateDeltaRows` enumerates the endpoint key union, uses the last
   value for a duplicate key as the Python dictionary does, computes checked
   signed differences, omits zeros and sorts those same delta records.

Effect ordering and table-delta ordering are distinct. Enum declaration order
cannot substitute for the runtime's kind token order. The model retains all
nine effect kinds and all four key coordinates.

## Theorem and premises

`checked_epoch_canonical_amount_delta_rows` proves:

```text
per-route ExactEconomicTables chain
+ unique endpoint amount keys in each of the four tables
+ successful checked epoch aggregation
=> strictly sorted, unique, nonzero emitted effect rows
   with signed-128-bit deltas and exact complete-key totals
   and, separately for every table:
     checked endpoint delta tuple = projected emitted delta tuple
```

Canonicality and output equivalence follow from the constructed emitter. They
are not supplied as premises. Finite support and signed endpoint bounds follow
from the accepted checked fold. Standard library sorting lemmas supply
permutation and order facts; the proof establishes the membership and
uniqueness facts needed to conclude exact list equality.

Endpoint uniqueness matters because the existing Lean `amountAt` sums rows,
while Python's state-delta dictionaries keep the last value. The theorem
proves their agreement under this explicit premise. It does not require
intermediate state uniqueness for the stated mathematical implication.

## Evidence and replay

Root independently rebuilt the five-module source closure with the pinned
Lean 4.27.0 toolchain and compiled a separately written consumer stating the
full theorem. The main theorem uses only `propext`, `Classical.choice` and
`Quot.sound`. The checked proof source at that review had SHA-256
`5ff80f22fde38729468dc237dd5b40a28bacc57302a483bf42b3e9f90122fe64`.

The focused replay command is:

```bash
python3 -B -m pytest -q tests/formal/test_lean_canonical_epoch_economic_rows_v1.py
```

Independent root replay passed all **10 tests in 41.96 seconds**. It freshly
compiles the five-module source closure, checks independent signatures and
axioms for all 47 named results, and applies the main theorem to a concrete
example. Finite evidence includes 30 actual composer cases, complete emitted
tuples, all four endpoint/projection tables with conflicting sort coordinates,
six signed-boundary cases and explicit duplicate endpoint behavior.

Five temporary definitions-only mutants execute changed effect ordering,
changed table-delta ordering, retained zero effects, duplicate summation and
an omitted endpoint bound. Each disagrees with actual runtime observations.
The mutant subjects contain no admitted or failing theorem placeholders.

The test SHA-256 is
`771fb9e425425842ae48960bc2d617667e3b196a102443ecf33a6ef3403ee985`.
Source and test pins, including the imported checked-epoch test helpers, are
declared in
`tests/evidence/test_hygiene/THV1-20260905-canonical-epoch-economic-rows-v1.json`.
The default `Proofs` aggregate imports the new module. A full aggregate
Lean/Mathlib build has not been run for this follow-up.

## Remaining refinement work

This is a universal Lean value model with finite runtime correspondence
evidence. It does not prove universal Python/Rust/compiler execution or byte
encoding. Its list-based key collection and lookup express value semantics;
they are not complexity claims about Python dictionaries.

Per-route table correctness remains a premise. Runtime row admission also
requires its existing token syntax, kind-specific sign conditions and typed
inputs. Command count, canonical byte size, other resource ceilings, metadata,
supply conservation, fee policy, authority, replay, receipts and publication
remain separate obligations. These conditions cannot be inferred from sorted
rows alone.

The next refinement boundary is the actual per-route admission and its
canonical decode/encode relation. This proof grants no release or publication
authority.
