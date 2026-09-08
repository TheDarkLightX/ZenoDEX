# Derived account-row growth

Date: 2026-09-08

Status: exact finite row-count and capacity relations are proved, independently
reviewed and replayed. `formal_core_complete=false`; authority remains `NONE`.

The [recomposition proof](ZENODEX_ASSET_LANE_FINITE_RECOMPOSITION_20260908.md)
establishes exact full-table equality. This checkpoint derives the row count
from the actual erase, put and sort operations, so capacity need not be supplied
as an assumed post-state property.

## Proved contract

For the full account key `k = (owner, asset, accounts)`, let `N` and `N'` be
the source and result lengths, `old` its source lookup, and `delta` the signed
change. Indicator values below are either zero or one:

```text
N' + present(k, source) = N + nonzero(old + delta)
```

[AssetLaneFiniteRowGrowthV2.lean](../../lean-mathlib/Proofs/AssetLaneFiniteRowGrowthV2.lean)
proves this equality from unique source keys. It transports the equality through
the independently defined managed recomposition under the accounts-domain and
selected-managed-asset premises. No post bound or caller admission Boolean is
assumed.

The main results are `updateRows_length`, `recomposeBalances_length`,
`recomposeBalances_capacity_iff`, `account_lookup_zero_iff_absent`,
`full_burn_then_reissue_length`, `dormant_issue_at_4096_exceeds`, and
`accepted_managed_recomposition_length`. The accepted-model corollary derives
command/policy asset binding from the existing V2 guard model before applying
the count equation.

The retained independent consumer derives the exact overflow condition for an
initial source within capacity:

```text
N' > capacity
iff N = capacity and k is absent and old + delta is nonzero
```

It also proves that one row of headroom suffices for this one-account update.
The count is for the complete aggregate, including unmanaged rows. A filtered
leaf may fit while the aggregate cannot.

For canonical nonzero account rows, a zero lookup is equivalent to absence of
that exact key. A new owner's issue adds one row; an existing funded owner's
issue preserves the count; a full account burn removes one; reissue recreates
it. Another owner's balance or another asset's balance does not establish key
presence. Stored zero rows invalidate the zero-lookup shortcut, and duplicate
keys invalidate the single-removal indicator law.

## Executed evidence and scope

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_lane_finite_row_growth_v2.py
python3 -m ruff check tests/formal/test_lean_asset_lane_finite_row_growth_v2.py
```

All **eight tests passed**, rebuilding 23 pinned Lean modules in a fresh
temporary subject. The suite checks six exact theorem types, standard axioms,
the independent overflow/headroom corollaries, owner-specific growth, partial
and full burns, reissue and filtered-versus-aggregate capacity. Five deliberately
false statements are rejected with semantic false-proposition diagnostics.
The 4,096-to-4,097 result instantiates a symbolic theorem; it does not require a
4,096-row Lean fixture. The separate runtime tests use actual states at that
boundary. Ruff and formatting pass.

Independent Astra review compiled additional wrong-owner, stored-zero,
duplicate-key and custody-domain controls and an accepted-count consumer using
the actual filtered supply lookup. Its 30 audited source/consumer declarations
use only `propext`, `Classical.choice` and `Quot.sound`, with no placeholders.
The review is advisory; the compiler checks establish the stated theorems.

| Subject | SHA-256 |
| --- | --- |
| Proof source | `087a35bea18666fcb51c17285ad0846cfd54501d4f9c769522300d6c8baeb4cf` |
| Retained test harness | `5dfe7eea773f3dc4465c2ac4509e35613ff2904de0ee762ebd4fde1ebacc73b7` |

This count relation does not establish byte-size admission, complete constructor
validity, authorization provenance, transfer fee-role cardinality, complete
runtime outcomes or publication safety. The algebra also applies to inadmissible
integer quantities. Prior V2 model acceptance omits current runtime resource
guards, so the [typed resource outcome repair](ZENODEX_ASSET_LANE_RESOURCE_OUTCOMES_20260908.md)
still requires full formal/runtime outcome correspondence. No full Lake, Kani,
ESSO, RISC0 guest/proving build or production activation was performed here.
