# Constructed sparse transfer state admission

This W09 increment extends `186fb2598bc7c83316d426f07d4b901c97b004d7`.
It derives the global model's quantity-admission predicate for the existing
sparse transfer constructor and its actual accepted/rejected history. It adds
a proof and independent harness; economic runtime code is unchanged.

## Proved contract

`AssetTransferSparseStateAdmissionV1.lean` proves:

```text
CanonicalBalances input.pre.balances
and StateQuantitiesAdmitted input.pre
=> StateQuantitiesAdmitted (step input).post
```

The accepted branch derives positive, u128-bounded, unique output balance rows
from the checked sparse update. The proof carries uniqueness from the sparse
key `(owner, asset, domain)` to the global key `(asset, owner, domain)` through
an injective coordinate permutation. The existing account-total theorem then
establishes the post-state physical owned-total bound. Every other state field
is framed by the actual `step`; rejection returns the exact initial state.

The history theorem inducts over `run` with only initial canonical balances and
initial state admission. It does not assume post-state admission, per-step
verified outcomes, or an externally supplied principal enumeration. Separate
step and history theorems preserve `OwnedMatchesSupply` and
`ClaimantLiabilitiesBacked` from their respective initial predicates. Liabilities
remain separate from physical balances, custody and reserves.

The nine declarations include supporting key and width lemmas. Their number
does not measure completed features. This closes a state-quantity preservation
obligation for the constructed sparse model; the general global `Verified`
constructor and runtime simulation remain separate obligations.

## Independent evidence

The harness captures the dependency sources, compiles them with installed Lean
4.27.0 and warnings treated as errors, and independently restates every new
theorem signature. Transitive axioms are restricted to `propext`,
`Classical.choice` and `Quot.sound`. It also requires registration in
`Proofs.lean` and pins the selected unchanged model and runtime sources.

The nonempty Lean witness includes balances, custody, liabilities, reserves,
an open terminal obligation, an oracle occurrence and a replay entry. A rejected
request and two accepted requests reduce Alice's ten account atoms to two;
the new theorems establish admission, owned supply and claimant backing for the
result. Initial predicates are constructed explicitly. A counterexample with
writer epoch `2^64` keeps canonical balances and accepts the leaf transfer while
both global states remain inadmissible. A separate key witness retains two
distinct owners of the same asset.

A Tier 1 owner-erasure mutant first compiles as a well-typed key definition and
visibly merges Alice's and Bob's keys. Compiling the complete mutated source
against the unchanged proof then fails. Both stages run on private copies;
the checked proof source stays unchanged.

The unchanged runtime backing tests provide eleven focused controls, including
claimant swaps, wrong-domain backing, aggregates at the u128 boundary and
overflow. The existing sparse-supply width test adds an accepted leaf whose
global physical total overflows: the global guard refuses both endpoints.
These twelve controls passed in root replay. They support the existing runtime
boundaries and do not prove equivalence to the new Lean predicate.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_sparse_state_admission_v1.py
python3 -B -m pytest -q -p no:cacheprovider \
  tests/core/test_global_economic_state_effect_refinement_v1.py -k claimant_relation
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_sparse_supply_v1.py::test_global_owned_width_guard_is_a_separate_runtime_boundary
python3 -m ruff check tests/formal/test_lean_asset_transfer_sparse_state_admission_v1.py
python3 -m mypy tests/formal/test_lean_asset_transfer_sparse_state_admission_v1.py
python3 -B -m experiments.v3_sparse_state_admission_v1.render_evidence
```

The last command regenerates only
`THV1-20260906-sparse-state-admission-v1.json`. Rendering records source pins and
test declarations; it executes no test and grants no authority.

Root replay of the new harness recorded **4 passed in 34.28s**, with identical
source hashes before and after execution. Ruff and single-file MyPy passed.
The independent worker replay also passed all four tests. The proof SHA-256 is
`82f54f4d5a5ba5e28a2ed2a96cd6b4155e70458c05d104b31eea0717aaae8649`;
the harness SHA-256 is
`7aa8186b3f24343b36feb10a4c3f19ec35424d17e557d76dd7c7f74af333767c`.

## Remaining boundary

The model fixes a selected policy and changes only sparse account rows. It
does not select a policy from the runtime registry, authenticate a command,
advance height, consume replay state, hash canonical bytes, construct a complete
effect plan or `Verified` witness, or prove Python/Rust/compiler refinement.
`StateQuantitiesAdmitted` is the exact existing mathematical predicate, not a
claim that every runtime constructor or resource ceiling has been modeled.

The Lean terminal record carries `liabilityDomain`. V1 runtime terminal rows
omit that field, and their state-visible necessary backing check aggregates
open terminals by asset and claimant. The positive witness is consequently
Lean-model evidence; it supplies no ownership-domain projection for runtime
terminals. Exact allocation remains tied to authenticated state and pinned
ownership evidence at its own admission boundary.

No full Lake/Mathlib, guest, CUDA or production qualification build ran. The
next formal step is to connect the constructed row transition to the complete
selected-policy input and output contracts, including metadata, effects and
runtime refinement. Other lanes and routes, genuine custody receipt composition,
deployment recovery and release assessment remain open. Neither formal-core
completion nor whole-program value safety is established.
