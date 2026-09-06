# Sparse transfer policy selection and constructor premises

This W09 increment extends `d52e7efe05005fe2b69957eb7396b49c60d69988`.
It connects the existing constructed sparse transfer to a pre-state policy
table. Each request selects its own asset policy, so a history can transfer
different assets with different fees and fee recipients. Runtime economics,
wire formats and publication authority are unchanged.

## Contract

`AssetTransferPolicySelectionV1.lean` wraps the existing sparse transition with
the runtime's first-match lookup. The front door rejects a module-release
mismatch first, an unknown command kind second, and an absent asset policy
third. A selected row then enters the existing transfer guard sequence.
The lookup establishes both membership in the pre-state policy table and an
exact asset match. Unique policy keys make it the only matching member.

`StateAdmitted` describes the modeled quantitative constructor premises:

- Canonical, positive account balances with unique keys and at most 4,096 rows.
- Canonical policy and supply tables with unique asset keys, at most 256 rows
  each, and u128 fees and supplies.
- Equal ordered asset lists in the policy and supply tables.
- Account balances for every asset bounded by that asset's supply.

The last clause is related in both directions to the runtime's separate
requirements that every balance asset be registered and each listed supply
cover its account total. The equivalence uses positive sparse balance rows,
unique supply keys and nonnegative supplies. These premises prevent missing
assets or duplicated supply rows from disappearing in the abstraction.
Registered assets with zero supply and no balances remain admissible, as in
the local runtime constructor. The stronger global sparse-state predicate
continues to exclude zero supply rows at its separate boundary.

The selected row and admitted tables supply the existing leaf model's balance,
supply and fee width premises. Supply uniqueness matters because the global
model sums matching supply rows, while the runtime local accessor returns one
row. The front-door contract derives the selected policy through lookup.

The preservation target is:

```text
StateAdmitted initial
=> StateAdmitted (run requests initial).post
```

The history also constructs `TableChain` from each accepted sparse step's
actual effects and post-state. Separate step and history theorems preserve
global quantity admission, physical owned supply and claimant backing from
their respective initial predicates. No postcondition or preconstructed
`Verified` witness is an input to these proofs.

Accounting and authorization are separate obligations. The debit theorem also
requires the command's constructor width premises and accepted execution; it
then identifies a decreased account with the command sender and context
subject. Context subject equality does not establish signature authenticity.
Rejected execution returns the exact modeled input state and empty plan, and
the history retains only accepted plans.

## Evidence and replay

Root replay of the focused harness recorded **6 passed in 47.50s**, with
identical source hashes before and after execution. The independent worker's
final replay recorded six passes in 48.06s. Ruff and single-file MyPy passed.
The harness builds a fresh Lean 4.27 dependency closure with warnings as errors,
independently restates all 30 public theorem signatures, and checks transitive
axioms against `propext`, `Classical.choice` and `Quot.sound`.

The nonempty witness starts with two assets, two distinct fees and fee owners,
and four account rows. A rejected request followed by EUR and USD transfers
reduces Alice's balances from 40 to 35 and from 50 to 45. Its initial admission
and owned-supply predicates are constructed explicitly; the new width,
preservation and debit-authorization theorems consume those premises. Custody
and liabilities are empty in this witness. The general preservation theorems
retain their explicit initial predicates for arbitrary admitted economic state.

Thirteen finite cases compare the public Python transition with the modeled
verdict, policy rows, supplies, balances and movement/fee rows. They cover a
later policy row, unknown and disabled assets, combined guard failures,
different fee limits, fee-owner aliases and signed-delta width neighbors.
Rejection checks require exact codes, equal roots, empty effects and unchanged
owned input bytes. The stateful reference computes endpoint balances from the
submitted commands and initial policies, independently of the emitted effects.

Separate Lean controls admit a registered zero-supply asset without balances
and reject duplicated supply keys whose summed value differs from either row.
The wrong-policy mutant first compiles as a well-typed lookup and returns EUR's
policy when asked for USD. The unchanged `policyFor_some` proof then fails on
the complete mutated source. Both stages use private source copies.

The long harness functions retain the complete Lean witnesses and their
observations together for review. They are test construction code outside the
economic runtime; no production complexity or algorithm changes are introduced.

The proof SHA-256 is
`6c330fb920885223089d774eaf6110a3007bd2790a3c69dc947f80255edff321`;
the harness SHA-256 is
`0c4a81c33797c398407871ee0fc1fee65ddfb0d2551617d9f0131b65cd263a51`.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_policy_selection_v1.py
python3 -m ruff check \
  tests/formal/test_lean_asset_transfer_policy_selection_v1.py \
  experiments/v3_transfer_policy_selection_v1/render_evidence.py
python3 -m mypy tests/formal/test_lean_asset_transfer_policy_selection_v1.py
python3 -B -m experiments.v3_transfer_policy_selection_v1.render_evidence
```

The renderer declares source and test pins in
`THV1-20260906-transfer-policy-selection-v1.json`. Rendering executes no proof
or test and grants no authority.

## Remaining boundary

`StateAdmitted` is an input premise over typed mathematical values. This step
does not implement the complete untrusted-input decoder, Python exact-class
checks, root/token syntax or constructor exception outcomes. Finite runtime
comparisons do not establish universal Python, Rust or compiler refinement.
The effect projection includes account movements and fee allocations; full
conservation rows, lane-root writes, occurrence consumption, canonical hashes
and journals remain outside it.

Local policy-table membership is separate from the governed registry check in
`asset_transfer_policy_registry_v1.py` and its lane binding consumer. This proof
does not authenticate the table, profile, grant, command or current store head.
The mathematical module release and policy rows are static across this history;
there is no policy migration, height advancement, replay consumption, receipt
verification or publication port.

No full Lake/Mathlib, Cargo, guest, CUDA or release-qualification gate ran.

The next output-contract obligation is to construct the full admitted effect
plan and its context-bound transition. Existing fee-mirror restrictions and
custody/profile admission remain binding. Other lane lifecycles, route proofs,
genuine custody receipt composition, deployment recovery and release assessment
remain open. This increment does not establish formal-core completion or
whole-program value safety.
