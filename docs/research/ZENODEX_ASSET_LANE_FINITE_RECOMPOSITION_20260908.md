# Exact finite asset-lane recomposition

Date: 2026-09-08

Status: the finite-table correspondence is proved and independently reviewed.
W07/W09 remain open. `formal_core_complete=false`; authority remains `NONE`.

The [shared-source checkpoint](ZENODEX_SHARED_ASSET_LIFECYCLE_20260908.md)
established that managed issuance/burn and transfer read the same account rows.
This checkpoint proves the managed coordinator's next step: updating the filtered
leaf, restoring the unmanaged complement, and sorting yields exactly the full
balance and complete supply tables obtained by updating the original source.

## Construction and proved relation

[AssetLaneFiniteRecompositionV2.lean](../../lean-mathlib/Proofs/AssetLaneFiniteRecompositionV2.lean)
defines recomposition independently of the full-table operation:

```text
recompose(pre, command) =
  sort(unmanaged(pre) ++ update(managed(pre), command))
```

The proof first establishes a permutation and then exact ordered-list equality
using unique keys. The desired equality is neither a definition nor an input
assumption. Complete supply tables retain registered identities at zero; numeric
supply support omits zero quantities.

| Theorem | Premises and result |
| --- | --- |
| `managed_balance_recompose` | Unique account keys, accounts custody domain, and membership of the changed asset in the managed set imply equality of the entire recomposed and directly updated balance lists. |
| `managed_complete_supply_recompose` | Unique ordered complete supply keys and selected managed membership imply exact complete supply-list equality, including zero identities. |
| `managed_recomposition_support` | An arbitrary canonical key/numeric view and managed-key coverage yield exact sparse update correspondence, complete decoding, unchanged registered keys, and canonical numeric support. |
| `accepted_managed_recomposition` | Acceptance by the existing filtered selected-policy V2 Lean model derives the command/policy asset binding. The recomposed full tables project to that model's exact post-state. |

The balance identity does not need initially sorted source rows because both
constructions sort their output. Complete supply source order is required: the
direct map preserves its input order. Source uniqueness and the accounts-domain
premise establish the needed comparison-tie property without assuming global
injectivity of a key that omits the amount.

The retained independent consumer also proves the same balance recomposition
with the runtime tuple shape `(asset, owner, custody_domain)`. Its comparisons
agree with the two-field account helper under the common custody-domain premise.
This is a theorem about explicit tuple comparisons, with no claim about an
unverified parser, string library, compiler, or serialization implementation.

## Executed evidence

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_lane_finite_recomposition_v2.py
python3 -m ruff check tests/formal/test_lean_asset_lane_finite_recomposition_v2.py
```

All **nine tests passed**. The harness rebuilt 22 source-pinned Lean modules in
a fresh temporary subject using Lean 4.27.0 with warnings as errors. It checks
the four exact theorem signatures, standard transitive axioms, placeholder
absence, the independent runtime-key lemma and concrete lifecycle controls.
Six deliberately false row/identity laws fail with semantic false-proposition
diagnostics, rather than syntax or type errors. Ruff and formatting pass.

The controls include multiple managed assets, funded unmanaged assets, a dormant
selected asset and unrelated zero supply identities. They exercise an accepted
filtered issue, full burn and reissue to another owner. Missing complements,
duplicate funded rows, reassigned ownership, lost/duplicated zero identities and
incorrect order are distinguishable. Reassigned ownership preserves the asset
total; lost zero identities preserve numeric quantities. Exact tables expose both
defects.

An independent Astra review accepted the scoped statement after compiling a
separate consumer with different literal rows, the runtime tuple-key theorem,
and additional positive/negative controls. All audited theorem dependencies used
only `propext`, `Classical.choice` and `Quot.sound`. Review is advisory; Lean
checker acceptance establishes the stated mathematical result.

| Retained subject | SHA-256 |
| --- | --- |
| Proof source | `8ba5fdbc475acdf52261dacb55f103afca78f44ddbe28f1a57a4514716c91d5a` |
| Test harness | `73718cff01f21a96d943ad210c64c71ca34f8170734ef432f66e6425dff59226` |

## Remaining obligations

These identities use mathematical integers and also hold for quantities that
would be inadmissible at runtime. Acceptance of the selected-policy Lean model
does not include every current Python/Rust constructor or resource check.
The [resource outcome repair](ZENODEX_ASSET_LANE_RESOURCE_OUTCOMES_20260908.md)
separately exercises typed POST-state size rejection in both implementations.

Exact row-growth derivation, byte admission, full policy-list selection, initial
quantity bounds, canonical codecs and hashes, effects and receipt binding,
authenticated snapshot provenance, mixed runtime traces, and publication
mediation remain separate obligations. Reused V1 row algebra does not imply
equivalence of V1 and V2 guards or wire formats. No full Lake, ESSO, Kani, RISC0
guest/proving build or production activation was performed for this checkpoint.
