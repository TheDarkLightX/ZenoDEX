# Finite transfer accounting and shared asset lifecycle

Date: 2026-09-08

Status: machine-checked mathematical projection and finite runtime controls.
This advances W04/W07/W09. `formal_core_complete=false` and
`whole_value_movement_safe=false` remain unchanged. No publication authority is
granted.

## Constructed finite transfer

[`AssetTransferFiniteAccountingV2.lean`](../../lean-mathlib/Proofs/AssetTransferFiniteAccountingV2.lean)
derives a transfer model's account lookup and account total from the same finite
balance table. It materializes the actual V2 transfer deltas through the existing
erase, put and sort operations. The accepted guards imply distinct sender and
recipient; the ordered role list also handles a fee owner who is the sender or
recipient. Role uniqueness prevents counting an aliased fee owner twice.

For every queried asset and account, the constructed table has precisely the
original lookup plus its command delta. Per-asset account totals are unchanged
for every asset. Accepted commands preserve unique positive bounded account rows,
and the computed selected-policy projection equals the V2 model's accepted post.
The V1-labelled helpers provide integer row algebra; they do not establish
V1/V2 guard, rejection-order or wire equivalence.

The finite construction folds distinct roles in reverse order. An independent
consumer proves that a forward fold has the same account observations when the
roles are unique. A duplicated-role control breaks the total. Exact runtime
serialization and complete control-flow refinement remain separate obligations.

## One source for both leaf views

[`AssetLaneSharedProjectionV2.lean`](../../lean-mathlib/Proofs/AssetLaneSharedProjectionV2.lean)
uses the existing global state as a finite-row carrier. Its two leaf views read
the same balances and supply lookup. The managed-policy membership filters for
both balances and supplies preserve the selected model; this includes registered
assets whose zero numerical supply has no sparse row.

An accepted managed issue or burn updates the transfer view. An accepted transfer
updates the managed view. The corresponding theorems preserve the other view's
quantity bounds under explicit canonical-supply, uniqueness, nonnegative-row,
selected-policy and pre-state assumptions. Unrelated assets and accounts are
framed. No independent sibling balance or detached account total is supplied.

The lane-specific equation is:

```text
sum(account rows for asset) = supply(asset)
```

This is stronger than general global accounting when custody or reserves are
nonzero. The preceding
[registered lifecycle checkpoint](ZENODEX_REGISTERED_LIFECYCLE_ACCOUNTING_20260908.md)
separately accounts for those physical locations. Claimant liabilities are not
additional physical holdings.

The retained sequence starts with a dormant ordinary asset, issues one atom to
Alice, transfers it to Bob, and burns it from Bob's fresh managed view. Freezing
the transfer view before issuance or the managed view before transfer changes
the next command from acceptance to insufficient-balance rejection. Mallory
receives no issued balance. The controls also retain an unrelated asset.

## Evidence and exact subjects

| Proof | SHA-256 |
| --- | --- |
| `AssetTransferFiniteAccountingV2.lean` | `ad3257cfdfbd1b9040e8312fc17c5181645c51e1637006df3641c156e4630b7d` |
| `AssetLaneSharedProjectionV2.lean` | `88645b58042f2272bb32898a13eeb8805403099f78f76e91143fc0f6cf08141c` |

The pinned checker is Lean `leanprover/lean4:v4.27.0`. The focused tests copy and
compile the required Std-only source closure into fresh temporary directories
with `warningAsError`. They check independent theorem signatures, standard
axioms, placeholders, reachable controls and false laws rejected by the kernel.
The transfer test also compares four independent fixed Python observations,
covering distinct and aliased fee owners, depletion and creation.

Replay from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_finite_accounting_v2.py \
  tests/formal/test_lean_asset_lane_shared_projection_v2.py
```

Qualification ran the initial combined suite with 10 passing tests, then retained
the independent reverse-lifecycle consumer and reran the shared suite with six
passing tests. The unchanged transfer suite contributes five tests: 11 distinct
final controls. Both test files passed Ruff. Independent reviews accepted the
exact proof subjects within scope and found only standard Lean axioms
(`propext`, `Quot.sound`, `Classical.choice`). No full Lake or RISC0 build was run.

## Remaining refinement

These are arithmetic and state-observation theorems. They do not establish:

- authentication or provenance of policy, registry, context or source snapshots;
- exact canonical equality between the coordinator's filtered-leaf merge and
  the constructed full-table update;
- complete finite row/byte admission or equality of every runtime outcome;
- command decoding, rejection precedence, roots, journals, replay or publication;
- universal Python/Rust refinement, guest execution or deployed value safety.

The current V2 arithmetic models omit post-state resource rejection. A valid
4,096-row aggregate can receive a fitting managed leaf candidate whose merged
post needs 4,097 rows. Thus arithmetic-model acceptance alone cannot imply
runtime acceptance. That concrete boundary requires its own typed outcome and
finite-state refinement; adding an unverified admission Boolean would not close
it.

The next mathematical step is exact canonical recomposition: prove that updating
the selected managed table and merging the unmanaged complement produces the
same complete rows as the global finite update. Resource-aware mixed traces
depend on that construction. Global fee-annotation admission, including the
sender/fee-owner alias case, also remains separate from transfer accounting.
