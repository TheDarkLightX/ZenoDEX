# Constructed transfer supply preservation and fee eligibility

This W09 increment proves physical conservation for the constructed sparse
transfer and its finite histories. It also characterizes the existing leaf's
fee-mirror restriction. It changes no fee, rounding, issuance, custody-owner,
authentication, or publication policy.

## Constructed conservation

`lean-mathlib/Proofs/AssetTransferSparseSupplyV1.lean` contains twelve theorems.
The proof sums the actual finite erase, put, and checked-update operations,
then cancels the sender, recipient, and fee-owner events using the leaf's
internally constructed role list. Both fee-owner aliases are included. It
assumes no per-transition conservation equation, exact table relation, or
externally supplied enumeration of principals.

The per-asset physical quantity is:

```text
owned(asset) = balances(asset) + custody(asset) + reserves(asset)
```

Source-key uniqueness and accepted execution imply unchanged physical totals.
Initial `OwnedMatchesSupply` therefore implies that property at the endpoint.
Positive accounts-domain rows additionally give the existing canonical output
guarantee. The history theorem carries canonicality and initial physical
equality through the actual `SparseTrace.run`, including rejected attempts.
Claimant liabilities remain separate from this physical sum.

The uniqueness premise is load-bearing. A retained duplicate-row model example
accepts and loses physical value when uniqueness is absent. The actual Python
state constructor rejects those duplicate source rows. A separate example
preserves mathematical totals while the global u128 total guard rejects both
endpoints. Neither mathematical equality nor an abstraction alone establishes
runtime admission.

## Fee-mirror eligibility

`lean-mathlib/Proofs/AssetTransferFeeMirrorEligibilityV1.lean` contains four
theorems over the existing well-formed accepted leaf. Its keyed movement sums
and emitted fee-allocation rows establish:

```text
fee_mirror_eligible <=> fee = 0 or fee_owner != sender
```

A positive sender-owned fee remains rejected by the existing global
fee-mirror checker. The theorem preserves that restriction. It does not change
policy to make the leaf acceptable. The model projects the signed aggregate
and allocation clauses; finite runtime comparisons also exercise the existing
zero-fee and residue checks on the actual emitted effects.

## Independent replay

The root replay passed nine tests, with fresh Lean 4.27.0 compilation of each
captured dependency closure and warnings treated as errors. Independent
consumers check all sixteen theorem signatures and their transitive axioms,
limited to `propext`, `Classical.choice`, and `Quot.sound`.

Supply evidence includes ten physical-row cases, a mixed rejected/accepted
history, a nonempty theorem consumer, the duplicate-source control, and the
separate u128 aggregate boundary. Fee evidence includes 21 alias/width cases:
twelve mirror acceptances, two positive sender-fee refusals, and seven adjacent
leaf overflow refusals. A temporary unconditional-eligibility mutant fails the
same negative Lean consumer. This is a model mutant, not a deployed-code
mutation campaign.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_sparse_supply_v1.py \
  tests/formal/test_lean_asset_transfer_fee_mirror_eligibility_v1.py
```

The proof hashes are `e2c056cba91173f6c454f4b60c1adc228d9ffd7df58a9cebcdbbc0e9b46a683d`
and `03ae7a9c1db3b8355fb2cd3f09206565cee524c3c735855a0af6c5287ecc5a10`,
respectively. The source-pinned hygiene packet records the full replay subject.

## Remaining obligations

These are universal model theorems with finite runtime correspondence.
Certified initialization, authenticated context, claimant backing, complete
route and receipt admission, policy/version transitions, universal
Python/Rust/compiler refinement, and publication remain separate obligations.
No full Lean/Mathlib, guest, Kani, solver, or genuine receipt build was run.
The formal core and whole V3 plan remain incomplete.
