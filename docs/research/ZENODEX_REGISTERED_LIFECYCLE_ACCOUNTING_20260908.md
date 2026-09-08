# Registered supply reconstruction and finite lifecycle accounting

This W04/W07/W09 checkpoint closes two representation dependencies: recovering
the complete registered supply table from covered sparse quantities, and deriving
the managed-asset model's account total from actual finite balance rows. It adds
proofs and executable evidence. It changes no runtime, wire format, policy,
registration authority or publication path. A composition theorem connects the
two representations to preservation of all-asset physical holdings.

The integration base is `79c214dd5e5f10eec837a908c4b945b918dc6bc4`; runtime sources
remain those of `8217e2f9e3c7b50d6ac6d5df91752755badd472b`. Lean is pinned to 4.27.0.
The earlier [update checkpoint](ZENODEX_REGISTERED_SUPPLY_UPDATE_20260908.md)
remains a historical statement of its narrower complete-source domain.

## Arbitrary covered supply views

[`RegisteredSupplyViewV1.lean`](../../lean-mathlib/Proofs/RegisteredSupplyViewV1.lean),
SHA-256 `8bcdf3ab4444bbb96ad41c304eec6d35fb042528a81311e63616c00ba519ee1f`,
starts with independent input lists: carried policy keys P and numeric rows N.
Its input predicate requires unique strictly ordered keys in each list, nonzero
numeric amounts, and every numeric key in P. It contains no source-image
equation, desired successor or post-admission premise.

The proof establishes:

```text
encode(decode(P, N)) = (P, N)
numericRows(adjustComplete(a, d, decode(P, N))) = adjustSparse(a, d, N)
decode(P, adjustSparse(a, d, N)) = adjustComplete(a, d, decode(P, N))
```

The update equations require a in P. The computed successor remains a covered
canonical view with the same keys, so the theorem can be applied again after
creation, full burn and reissue. Numeric lookup changes by d at a and by zero
at every other asset. Pre-row U128 bounds and the computed selected post bound
give bounded complete and sparse successor quantities. Algebra is over Int;
command I128 admission is a separate condition. Explicit uniqueness is reusable
with existing lemmas; strict order already excludes duplicates.

Dormant keys before, between and after numeric support are retained. Controls
show exact roundtrip failure for uncovered support, duplicate numeric keys,
stored numeric zero and inconsistent list order. The empty-key unknown-asset
control preserves the distinction between a vacuous decode equality and the
stronger numeric correspondence that fails.

P is the exact carried policy-key observation, not every key in an outer
registry that may be a superset. This theorem establishes information
sufficiency. It does not authenticate those policies, their provenance or the
snapshot. Assets outside a selected policy domain must be explicitly framed;
the coverage assumption cannot be satisfied by silently discarding their rows.

## Finite account rows

[`ManagedAssetFiniteAccountingV2.lean`](../../lean-mathlib/Proofs/ManagedAssetFiniteAccountingV2.lean),
SHA-256 `5c81d4caca4f02930e4c20dd432fdecb808a8460f5da11e0e4fa3ce577e50795`,
projects both the balance function and selected-asset account total from one
finite row table. It reuses existing erase/put/sort operations to materialize
the accepted issue/burn balance update, including insertion and zero deletion.
V1-labelled helpers supply integer row algebra; there is no wire ABI conversion.

For a unique input table, accepted model execution derives the command/policy
asset binding and exactly matches the newly materialized balances, total and
scalar supply. Nonnegative source rows establish the essential inequality:

```text
selected balance b <= finite account total A <= supply s
accepted bounds: 0 <= b+d, s+d <= U128_MAX
therefore:       0 <= A+d <= s+d <= U128_MAX
```

This proves preservation of the existing model's state quantity invariant from
its actual finite representation. Positive accounts-domain input rows also
produce unique, nonzero, bounded accounts-domain rows. Unrelated asset lookups
and totals remain unchanged.

The retained counterexample shows why the representation condition matters:
the older model can independently carry balance 1, total 0 and supply 4. Those
quantity clauses admit a burn of 1 with a negative post total. The finite-row
projection computes total 1 and produces total 0; it excludes the bad model
input by construction. This is a formal-model coverage defect, not a
constructible Python state.

Runtime alignment uses the accounts-domain restriction from
[`managed_asset_lifecycle_state_v2.py`](../../src/core/managed_asset_lifecycle_state_v2.py)
and the actual dictionary update, zero deletion and total computation in
[`managed_asset_lifecycle_module_v2.py`](../../src/core/managed_asset_lifecycle_module_v2.py).
Generic row algebra permits broader inputs, so uniqueness alone is insufficient
for a runtime correspondence claim. Independent Astra review accepted the final
proof under these scoped conditions. The review prompted deletion of an unused
helper; no theorem premise or conclusion was weakened.

## Composed physical accounting

[`ManagedAssetRegisteredAccountingV2.lean`](../../lean-mathlib/Proofs/ManagedAssetRegisteredAccountingV2.lean),
SHA-256 `98a58eb4cc0b4ae14ece5cfac1dba0aa8c4ab31c9f11b3ff31f2dacf81aa0250`,
constructs the balance update and sparse supply update together. It proves
`OwnedMatchesSupply` for every asset from the initial equation, canonical
covered supply support, selected registration, and unique account keys:

```text
owned(a) = accounts(a) + custody(a) + reserves(a)
accounts'(a) = accounts(a) + d
supply'(a)   = supply(a) + d
custody' = custody; reserves' = reserves
```

Every other asset receives zero delta. Claimant liabilities are not counted as
additional physical holdings. An accepted-leaf corollary derives command/policy
asset binding from the actual model guard, then proves that projecting the
computed global accounting rows and sparse supply reproduces that leaf's post.
Its quantity well-formedness follows through the finite-row theorem. The
algebraic conservation theorem alone imposes no post bounds or authorization.

Controls retain ORD account 1, custody 1 and reserve 2 against supply 4, funded
EUR, and a dormant AUD identity. Both model issue and burn are accepted.
Mismatched balance/supply deltas and lost custody fail conservation. The
independent consumer additionally requires Lean to refute lost-reserve
conservation.

This is a constructed accounting projection. Existing global roots and
metadata are retained as a frame; the record is not claimed to pass global
successor admission. Effects, replay, fresh metadata and publication still need
their own construction and refinement. The theorem adds no consumer to a
publisher and no externally spendable authority.

Independent Astra review accepted the frozen composition under that scope. Its
consumer combines materialization, physical conservation, support closure,
retained keys and finite quantity bounds. It also refutes a stale selected-leaf
balance that disagrees with the actual input rows.

## Executable evidence

The [supply-view gate](../../tests/formal/test_lean_registered_supply_view_v1.py)
rebuilds a fresh five-module closure, pins canonicality to raw input facts,
checks independent signatures and standard axiom dependencies, consumes repeated
admitted updates, and requires Lean to refute five false roundtrip laws.

The [finite-account gate](../../tests/formal/test_lean_managed_asset_finite_accounting_v2.py)
rebuilds its pinned local dependency closure, consumes the preservation and
materialization signatures independently, retains the detached-total control,
and requires refutation of omitted creation, cross-asset leakage and stale
total laws. Fifteen actual V2 leaf steps compare complete account rows and
per-asset totals with the separately evaluated Lean row operations: creation,
growth, partial burn, full burn and reissue at three asset-order positions.

The [shared coordinator history](../../tests/core/test_asset_lane_dormant_lifecycle_v2.py)
starts with funded EUR, dormant managed USD, and dormant transfer-only ZZZ. It
executes issue 7, transfer 7, burn 7, reissue 2 and transfer 2. It checks both
fresh leaf projections, policy frames, complete zero supply identity, exact
effects and conservation vectors, and unchanged input bytes. Post-burn transfer
and burn reject with exact no-op outcomes. A test-local frozen managed aggregate
candidate triggers `PROJECTION_MISMATCH`. Outputs remain `SHADOW` and `NONE`.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider tests/formal/test_lean_managed_asset_finite_accounting_v2.py tests/formal/test_lean_registered_supply_view_v1.py tests/core/test_asset_lane_dormant_lifecycle_v2.py
python3 tools/scan_lean_proof_placeholders_v1.py --json lean-mathlib/Proofs/RegisteredSupplyViewV1.lean lean-mathlib/Proofs/ManagedAssetFiniteAccountingV2.lean
python3 -m ruff check --no-cache tests/formal/test_lean_managed_asset_finite_accounting_v2.py tests/formal/test_lean_registered_supply_view_v1.py tests/core/test_asset_lane_dormant_lifecycle_v2.py
```

The combined focused gate passed 15 tests. Kernel audits found only standard
`propext`, `Classical.choice` and `Quot.sound` dependencies. Placeholder scanning
and focused lint passed. The deterministic false-law checks require the actual
refutation diagnostic, not merely an unsuccessful compiler invocation.

The [composition gate](../../tests/formal/test_lean_managed_asset_registered_accounting_v2.py)
passed three further tests after rebuilding its complete nineteen-module local
closure. It independently pins ownership, accepted materialization and quantity
preservation signatures and checks nonvacuity and reserve-loss refutation.
The coordinator, its new history, and the existing supply-update runtime suite
passed 45 tests together after removal of redundant test-fixture copies.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider tests/formal/test_lean_managed_asset_registered_accounting_v2.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider tests/core/test_asset_lane_dormant_lifecycle_v2.py tests/core/test_asset_lane_coordinator_v2.py tests/core/test_registered_supply_update_runtime_v1.py
```

## Remaining obligations

These results do not establish full Python/Rust execution refinement,
canonical-byte or parser/order equivalence, resource-ceiling admission,
authenticated policy-list selection, complete shared-state lifecycle
continuation, effects and receipt construction, replay, migration, publication,
durability or deployment safety. The older abstract `replaceManaged` projection
still does not model the coordinator's changed shared transfer view; the runtime
history is finite evidence, not its general replacement proof.

The complete Lake project, Rust/Kani, ESSO, RISC0 and production qualification
were not run for these proof and test changes. Formal core, whole value movement
and whole product completion remain false; no value-movement gate or authority
is promoted by this checkpoint.

The active-plan and V3 graph checkers pass with those claim ceilings unchanged.
The broad `tools/check_claims_registry.py` gate still fails on missing
`tools/check_derivatives_authorization_matrix.py`. A provenance review recovered
its four-file evidence bundle in `fda433cb5beef0eb159737c0ee0871bc54dbc144`,
derived from `9e0659870f88753dda339d1ffdce1d18d054ae34`. Its referenced claims
also need 24 missing evidence paths; a required declaration document exists only
in the latter of those commits. Restoring the four files alone cannot qualify
that matrix or the broad registry. This separate branch-integration obligation
remains open; no registry or derivative evidence was changed here.
