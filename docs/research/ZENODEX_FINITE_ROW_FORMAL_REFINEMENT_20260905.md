# Finite economic rows: checked accounting bridge

This W04/W09 result extends integration subject
`04f0d32b6b6679aa23da645263ec6575f7872c4e`. It is a mathematical model with
bounded runtime comparison. It does not close formal-core or production gates.

## Proved obligations

`Proofs/FiniteEconomicRowProjectionV1.lean` keeps the complete
`(asset, owner, custodyDomain)` key. Admitted rows have unique keys and positive
u128 amounts. Admitted projections separate account and custody domains, name
every holding's supply, and require exact per-asset physical totals.

The finite lookup theorem derives the sum of observed holdings from row totals.
`accepted_projection_derived_lookup_supply` constructs its key enumeration from
the admitted rows, so the caller supplies neither coverage nor uniqueness.
`unionKeys_unique_and_covers` derives a complete, unique pre/post support,
including newly created and removed holdings. `assetDeltaSum_eq_total_difference`
then proves:

```text
sum over complete keys of (post holding - pre holding)
  = post physical asset total - pre physical asset total
```

Accepted projections naming the same asset supply therefore have zero summed
delta. Each individual conversion to an i128 delta still requires the explicit
representability condition of `checked_keyed_delta`; u128 holdings alone do not
establish it. Zero-row elision preserves aggregation. It does not repair the
first-match interpretation of invalid duplicate keys.

## Replay

```bash
python3 -m pytest -q tests/formal/test_lean_finite_economic_row_projection_v1.py
python3 -m ruff check tests/formal/test_lean_finite_economic_row_projection_v1.py
python3 -m mypy tests/formal/test_lean_finite_economic_row_projection_v1.py
```

The focused suite passed **9 tests**. It freshly compiles the actual module and
`CheckedSignedDeltaRefinementV1` with installed, version-checked Lean 4.27.0,
warnings treated as errors. It audits all 38 theorem declarations for standard
axioms and rejects placeholders. The count includes supporting lemmas and
executable witnesses; it is not a count of completed product obligations.

Runtime comparison executes 15 transfer fixtures/histories, including maximum
u128 physical totals, large holdings with small signed changes, fee-owner aliases,
foreign assets, one owner in distinct custody domains, a new recipient, terminal
zero-row removal, and acceptance after a pure rejection. Independent integer
expectations check complete balances and emitted account effects. Lean observes
the actual pre/post rows, full-key lookup, derived union, supply sums and deltas.
Additional controls check 14 projection-admission cases and ten signed-delta
boundary pairs. Input bytes remain unchanged by these transitions.

Three semantic mutants first compile with an observable wrong result, then fail
the unchanged theorem packet: owner-only lookup, accepting duplicate row keys,
and omitting keys present only in the predecessor. A separate control records
the canonical-order gap: the mathematical model accepts a row permutation that
the runtime constructor rejects. Missing/duplicated external enumerations and
zero elision on invalid duplicate rows also have explicit pressure cases.

## Exact source

| Artifact | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/FiniteEconomicRowProjectionV1.lean` | `62c5aaed7c89fd70e74982915d889b9818aefdbc636cc9aeff7bab15bfeca49f` |
| `lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean` | `3a0b3e18a069b14c8fec4e705178a73cb1b3356d9813195e5e7c35b09cf74a4d` |
| `tests/formal/test_lean_finite_economic_row_projection_v1.py` | `58bc05b95af7c76bef0183426204fe720567fd626ac23c817de43e77745e1375` |

Astra supplied the base and union-support proofs; a separate mathematical review
examined the finite-row premises; parent integration added the derived static
enumeration corollary, runtime bridge and semantic mutants and replayed the gate.
Review is advisory; Lean and executable observations supply the scoped evidence.

## Remaining obligations

The model does not prove canonical token decoding, sorting, row-count ceilings,
root serialization, source/compiler refinement, authenticated snapshot capture,
or publication. Runtime comparisons are bounded, not a universal implementation
refinement theorem. The custody frame is checked on the runtime fixtures and
has an identity theorem for an unchanged list; a general command-to-row update
proof must still derive that frame from the transition. Other lanes, route
occurrence ownership, historical version transitions, datastore recovery and
complete writer mediation remain separate V3 obligations.

No full Mathlib, guest, CUDA or production qualification build ran. The next
mathematical step is a finite row-update refinement for actual accepted commands,
composed with this complete-support sum and the existing authorization theorem.
