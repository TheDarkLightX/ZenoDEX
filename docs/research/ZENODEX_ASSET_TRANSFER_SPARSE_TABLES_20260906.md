# Constructive transfer accounting tables

This W09 follow-up starts at `5bc940e04a4f3cf29ea923fd8214cb8db9d3801a`.
`Proofs/AssetTransferSparseTablesV1.lean` connects the selected-policy transfer
model to the exact economic table relation used by the epoch proof. It grants
no release or publication authority and does not close the formal core.

## Construction and theorem

The model derives the local balance lookup from the finite source rows. It
runs the existing transfer guard and alias-coalesced delta model, then applies
each role's delta to the corresponding `(owner, asset, accounts)` key. Each
update checks unsigned 128-bit bounds, removes zero balances, and preserves
unrelated keys. The final constructor checks the 4,096-row ceiling and sorts
by `(asset, owner)`.

Account movement and fee allocation rows are constructed from the accepted
leaf's effects and sorted by `(kind token, asset, principal, domain)`. Only the
account table changes in the projected global state. Other global tables and
metadata form an explicit unchanged frame. The constructed plan contains the
accounting rows; it is not a complete module or route plan with conservation,
journal, occurrence and receipt commitments.

`accepted_sparse_transfer` proves:

```text
unique complete source balance keys
+ positive unsigned-128-bit source balances in the accounts domain
+ successful constructed sparse transfer
=> ExactEconomicTables for balance, custody, liability and reserve tables
   + ExactSupplyEffects
   + unique, positive, bounded, strictly sorted post balances
   + post balance row count <= 4096
   + unchanged non-balance frame
   + sender = supplied context subject
```

The exact table relation and canonical output are conclusions. Neither is an
assumed postcondition. A finite principal enumeration is also unnecessary:
the source rows supply the complete balance table. Rejection returns the exact
input state and an empty projected plan.

`disclosed_tables_refine` then lifts the result to independently supplied
endpoints whose balance, other table and supply equalities match the constructed
result and its frame. The supplied plan must carry those exact accounting rows.
These are the table equality checks required at the allocation boundary; the
corollary does not assume the delta equation it proves. Its metadata remains
outside the accounting theorem.

## Implementation relation

The Python correspondence surface is
`src/core/asset_transfer_module_v1.py` (`_transfer_deltas`, `_post_balances`,
`_effect_rows`), its exact typed constructors, the table/frame checks in
`src/core/asset_transfer_global_allocation_v1.py`, and the endpoint delta checker
in `src/core/global_economic_state_delta_v1.py`.

This advances the per-route premise of the checked epoch table-composition
theorem. The custody successor retains the same account and fee movement rows,
so the accounting construction applies to that family after its separate
execution binding. Its conservation fields, release selection and receipts
remain separate obligations. The installed isolated pipeline still selects the
legacy transfer implementation.

The existing sender-as-fee-owner limitation is retained: a positive fee can be
locally conserved while its fee owner has a net debit, causing the global
fee-mirror guard to reject. The theorem does not establish complete global
admission for that alias and changes no fee, rounding or wire value.

## Constructed command histories

`Proofs/AssetTransferSparseTraceV1.lean` extends the construction to arbitrary
finite attempt histories under one fixed selected policy and module release.
Each accepted step supplies its constructed post-state to the next attempt and
retains its accounting plan in order. Each rejected attempt contributes no plan
and leaves the state supplied to later attempts unchanged.

`run_table_chain` derives the exact table relation for every accepted step from
`accepted_sparse_transfer`. The initial premise is canonical source balances;
there is no caller-supplied table equation or assumed chain. The final balances
remain canonical, and accepted plan count cannot exceed attempt count.

`checked_history_exact_tables` applies the checked epoch composition theorem
to that constructed chain. Its conclusion covers every balance, custody,
liability and reserve key. Actual aggregate acceptance remains a premise.
`checked_history_iff_prefix_bounds` makes the remaining arithmetic condition
explicit: the checked result exists exactly when all ordered partial sums fit
the signed 128-bit bound. Per-command success does not remove those checks.

## Verification and replay

Independent root replay passed both focused suites:

```bash
python3 -B -m pytest -q tests/formal/test_lean_asset_transfer_sparse_tables_v1.py
python3 -B -m pytest -q tests/formal/test_lean_asset_transfer_sparse_trace_v1.py
```

The observed results are **9 passed in 43.58 seconds** and **7 passed in
32.27 seconds**. Each suite compiles its source-captured Lean 4.27.0 import
closure into a fresh temporary library with warnings treated as errors. The
trace closure has eleven proof modules. Separately restated principal theorem
types compile, and transitive axiom inspection for all 41 sparse and five trace
theorems permits only `propext`, `Classical.choice` and `Quot.sound`. A separate
root-authored sparse consumer also compiles against independently captured
sources. Independent Astra review of the trace source found no defect.

The sparse suite observes 19 complete leaf cases against independent signed
event arithmetic, the actual Python transition and the endpoint table checker.
It also reaches unsigned holding and signed effect bounds, accepted replacement
at 4,096 rows, rejected growth, exact rejection/no-op outcomes and a stateful
sequence. The trace suite compares complete balances and every accepted effect
row for three six-attempt histories, each containing two accepted transfers.
The fee-owner classes are distinct, sender and recipient. A positive consumer
constructs the initial canonicality proof and applies the history theorem.

Six temporary definitions-only Lean mutations compile and execute. The sparse
mutants retain zero rows, omit the asset coordinate from row erasure, or remove
the row ceiling. The history mutants discard later work on rejection, omit an
accepted plan, or reuse the old state for following work. Each produces a
different observation from the actual Python controls. These are executed model
mutants, not mutation execution against a deployed publisher.

Both new test files pass Ruff and scoped MyPy. No full Mathlib build, Rust guest
build, Kani campaign, RISC0 receipt generation or GPU work was run. Source and
test pins, including the full Lean closure and imported test helper, are in
`tests/evidence/test_hygiene/THV1-20260906-sparse-transfer-accounting-trace-v1.json`.
Regenerate the declaration with:

```bash
python3 -B -m experiments.v3_completion_followup_v1.render_evidence
```

Rendering records source subjects; it does not run the tests.

## Remaining obligations

Selected-policy membership, token and constructor admission, canonical bytes,
hashes, exact-command authentication, full conservation/claimant ownership,
release/image selection, receipts and publication are separate boundaries.
The source-key and positivity premises do not establish those conditions.
Finite Python comparisons do not prove universal Python/Rust/compiler
refinement. The list-based construction makes no complexity or performance
claim about the runtime's dictionaries. Full lane lifecycles and whole-program
formal/runtime refinement remain open.
