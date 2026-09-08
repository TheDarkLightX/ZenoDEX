# Registered supply update correspondence

This W04/W09 result proves a representation law for registered supply updates.
It adds no runtime behavior, committed field, policy value or publication
authority. Formal-core and whole-program completion remain open.

The runtime reference is source commit
`8217e2f9e3c7b50d6ac6d5df91752755badd472b`. The new proof is
[`RegisteredSupplyUpdateV1.lean`](../../lean-mathlib/Proofs/RegisteredSupplyUpdateV1.lean),
SHA-256 `3dfa40d5059e54589a9c5597e332b08b0d22c1c5b55caaccad36ecccd6ace6cb`,
checked with Lean 4.27.0 and warnings treated as errors.

## Proved contract

The complete carrier retains every registered row, including zero quantities.
The sparse carrier stores nonzero quantities in strict lexical key order.
Their updates are defined independently: a complete-row map and a sparse
lookup followed by ordered insertion, replacement or deletion.

For unique ordered complete rows C and selected asset a in their keys:

```text
numericRows(adjustComplete(a, d, C))
  = adjustSparse(a, d, numericRows(C))
```

Decoding the sparse output with the unchanged complete keys recovers the
complete output. Each other asset's lookup is unchanged; the selected lookup
changes by exactly d. Pre-row U128 bounds and the computed selected quantity's
U128 bound imply nonzero, bounded, unique, ordered sparse output.

The equality holds over integer deltas. Signed I128 command admission is an
external runtime condition. Strict order also excludes duplicates; uniqueness
is an explicit reusable carrier premise, not an independent policy choice.

An unknown asset exposes why decode equality alone is insufficient: with an
empty registered key list, both decoded outputs can be empty even when the
numeric update has inserted an unregistered asset. The proof retains this
counterexample and requires membership for its stronger numeric-row equality.

## Executable evidence

[`test_lean_registered_supply_update_v1.py`](../../tests/formal/test_lean_registered_supply_update_v1.py)
rebuilds the pinned four-module Std-only closure in a fresh directory, checks
independently written theorem signatures and standard axiom dependencies, and
requires the checker to reject three false update laws.

It compares eighteen actual leaf steps against the executable Lean updates:
first, middle and last insertion positions, each through issue, full burn and
reissue, in both Python ABI versions. V1 additionally runs the global effect
projector. V2 comparisons cover the local leaf and its numeric observation.

[`test_registered_supply_update_runtime_v1.py`](../../tests/core/test_registered_supply_update_runtime_v1.py)
adds fixed integer oracles, untouched zero/positive rows, signed-effect width
boundaries, supply overflow, account shortage, unknown identity and duplicate
key rejection. V1 fixture remainders have explicit custody rows; this fixture
does not establish admitted global initialization or publisher qualification.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider tests/core/test_registered_supply_update_runtime_v1.py tests/formal/test_lean_registered_supply_update_v1.py
python3 -m ruff check --no-cache tests/core/test_registered_supply_update_runtime_v1.py tests/formal/test_lean_registered_supply_update_v1.py
```

## Remaining obligations

The theorem starts from `numericRows(C)`. Arbitrary authenticated views need
an encode-after-decode completeness proof with exact carried policy keys and
covered canonical numeric support. Shared-state lifecycle continuation must
then derive actual finite account rows and reproject changed transfer state.

Python/Rust implementation refinement, parser/order correspondence, registry
authentication, global preservation, mounted issue/burn publication, recovery
and deployment gates remain separate obligations. The complete Lake project,
Rust, Kani, ESSO and RISC0 gates were not run for this proof-only change.
