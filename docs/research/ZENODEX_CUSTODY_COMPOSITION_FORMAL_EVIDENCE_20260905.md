# Custody transfer composition: checked model evidence

This W09 result connects the existing accepted-transfer model, custody-total
completion model and checked signed-delta model. It accompanies the native
custody coordinator committed at `070b1fb875fdf2d9a965610fc51cd5c1f021d16d`.
It grants no receipt, publication, migration or release authority.

## Mathematical result

[AssetTransferCustodyCompositionV1.lean](../../lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean)
contains nine checked theorems. From an accepted modeled transfer and a
well-formed pre-state, every principal's unsigned post/pre holdings pass the
checked signed-delta model and return the transfer's aggregated movement delta.
The holding conversion preserves the exact integer value and requires u128
bounds before converting `Int` to `Nat`.

The complete folded movement map equals post-balance minus pre-balance for
every principal. A general fold lemma accounts for omitted zero rows; the
role-order lemma handles distinct roles and fee-owner aliases. This establishes
coverage of the abstract emitted map as well as correctness of individual rows.
Using the same custody holding on both sides yields a checked zero delta.

For a finite principal enumeration containing each touched role once, assume
the exact pre-projection equation:

```text
sum(pre accounts) + common custody = pre.supplyAtoms
```

The theorem derives nonnegative account totals, completed pre/post totals equal
to the model's declared supply, and successful bounded completion. It derives
the u128 supply bound from `StateWellFormed` and uses the transfer theorem's
unchanged supply to establish the post equation. There is no separate caller
chosen supply parameter.

## Executable evidence

The focused test compiles the actual three imported dependencies and the new
file afresh with Lean 4.27.0, then audits all nine theorem dependencies. No
placeholders or additional axioms were found; the allowed standard set is
`propext`, `Quot.sound`, and `Classical.choice`.

The five tests passed in 33.31 seconds. They include:

- 13 accepted scenarios from the native coordinator fixture, checking 52
  signed account differences and 52 complete movement folds against exact
  integer oracles;
- 13 completed custody-total pairs, including maximum u128 supply, plus each
  fixture custody row's unchanged signed delta;
- a well-formed accepted instance and the supply equation `122 = 115 + 7`,
  with custody 8 failing that same projection premise;
- two compiled semantic mutants: an in-range complemented holding view returns
  `+32` where the integer difference is `-32`, and an empty movement fold returns
  zero for a nonzero debit. Both fail the unchanged theorem packet.

The paired native coordinator evidence compares complete Python/Rust values and
journal bytes; its [README](../../zk/asset_lane_custody_coordinator_risc0/README.md)
records eight native tests, 25 Python tests and two compiled native mutation
kills. The Lean checks add model composition evidence to those native results.

Replay from the repository root:

```bash
python3 -m pytest -q --tb=short tests/formal/test_lean_asset_transfer_custody_composition_v1.py
python3 -m ruff check tests/formal/test_lean_asset_transfer_custody_composition_v1.py
python3 -m mypy --follow-imports=silent tests/formal/test_lean_asset_transfer_custody_composition_v1.py
```

The Python harness records the Lean pin, creates fresh dependency objects in
its temporary test directory and uses `-DwarningAsError=true`. Full `lake build`
was not run; this checkout lacks its configured `external/mathlib4` dependency.
No dependency installation, guest build or remote compute was used.

## Exact sources

Hashes are SHA-256 over the source bytes, obtainable with `sha256sum`:

| Source | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean` | `37375e914576993767eae7484e620e54be300798785b2a57a9953e86be2f34d2` |
| `lean-mathlib/Proofs/AssetTransferRefinementV1.lean` | `2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932` |
| `lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean` | `fc6869b223a427ef22d040e71276d57c1f7b5bca9b95b471d4059ae771a1f8dc` |
| `lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean` | `3a0b3e18a069b14c8fec4e705178a73cb1b3356d9813195e5e7c35b09cf74a4d` |
| `tests/formal/test_lean_asset_transfer_custody_composition_v1.py` | `283491c77e485a68867796b356ea04ceeb89be8ccf3a6962d97f9565cfeef90d` |

## Remaining obligations

The model uses a single-asset balance function, an explicit finite account
enumeration and a common custody scalar. The runtime uses finite keyed rows
`(asset, owner, custody_domain)`. Canonical row coverage, unique keys, multi-asset
filtering and the connection from actual runtime rows to these model inputs
still require a refinement proof. The scalar pre-projection equation remains
an explicit premise.

Theorems do not establish canonical encoding, roots, source/compiler correctness,
cryptographic authentication, measured images, actual custody control, store
provenance, replay consumption or publication. The independently reviewed
statement and passing native comparisons cannot discharge these obligations.

The next mathematical step is a finite keyed-row representation theorem that
derives the complete runtime effect map and checked delta results, including
custody frames and refusal of out-of-range differences. Real custody successor
receipts and release-aware admission remain separate W03/W10 obligations. The
formal core and the complete V3 plan remain unfinished.
