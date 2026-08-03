# M6 zUSD protocol-fee claim realization V1

## Exact identity

```text
implementation_commit: a97db8f76c791e11a376cc2dfa9acf9ac47cfe81
implementation_tree:   7620c82ffa3e345cbb94098b74c9ac055909f6c5
implementation_parent: 11c6cc923865e5a186138e48786706f9297f15b7
functional_base:       14eaa2d8626bbdff8546f1dc88d84dd04bdfbc8e
posture:               IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint realizes an exact current zUSD protocol-fee claim into issued
ledger supply held by deterministic protocol escrow. The realization candidate
owns the claim reduction, escrow balance patch, downstream custody credit, and
debt/supply/claim certificate. M6, R13, current-state authority, publication,
and runtime mediation remain open.

## Closed local transition

The source contains one exact claim, the complete committed balance table, the
zUSD debt amount, the asset and custody identities, and the requested amount in
E8. The checker reconstructs the complete ledger supply for the zUSD asset and
requires the absolute pre-state identity:

```text
debt_pre_e8 = ledger_supply_pre_e8 + outstanding_claim_pre_e8
```

Only a positive whole-ledger-unit amount may be realized:

```text
amount_e8 = amount_units * 100_000_000
amount_e8 <= outstanding_claim_pre_e8
```

The controlled candidate then owns these exact changes:

```text
debt_post_e8 = debt_pre_e8
ledger_supply_post_e8 = ledger_supply_pre_e8 + amount_e8
outstanding_claim_post_e8 = outstanding_claim_pre_e8 - amount_e8
protocol_escrow_post_units = protocol_escrow_pre_units + amount_units
accrued_cumulative_post_e8 = accrued_cumulative_pre_e8
```

Both absolute endpoint identities and the transition-local delta identity are
recomputed at construction and verification:

```text
debt_post_e8 = ledger_supply_post_e8 + outstanding_claim_post_e8
debt_delta_e8 = ledger_supply_delta_e8 + outstanding_claim_delta_e8
```

An invalid absolute pre-state now rejects before a patch, credit, certificate,
or successor can escape. This regression was found during the final
model-to-runtime composition review.

## Exact residue owner

The current balance transport stores whole zUSD units while the monetary state
uses E8. Realization never rounds a claim. Any sub-whole residue stays in
`outstanding_e8` under the same exact claim identity. A retained test realizes
one whole zUSD from a claim of `100_000_001` E8 and proves that the final one E8
atom remains in the claim.

## Custody composition

The realization emits exactly one `ProtocolFeeCreditV2` whose source custody,
asset, and amount derive from the checked claim and balance transition. A
composition test feeds that owned credit and the realization's post-balances
into `apply_protocol_fee_distribution_v2` and checks exact same-asset
conservation.

That test establishes local type and value compatibility. The distribution
policy is still caller-supplied in the existing fee-custody reference machine.
Policy authentication, current-state binding, event occurrence lineage, and
atomic publication remain required before any runtime use.

## Authority boundary

`ZUSDProtocolFeeClaimRealizationSourceV1` is caller-constructible and carries no
authority. The accepted result uses controlled construction and owns one exact
claim transition, committed pre/post balance pair, canonical patch, custody
credit, and V2 certificate. The independent verifier rebuilds that result from
the externally supplied complete source instance and rejects crossed state,
identity, amount, custody, or certificate values.

The module has no mounted caller and cannot publish. Fee-bearing borrowing
remains blocked by the existing stop line.

## Counterexamples retained

Permanent negative evidence covers:

- invalid absolute `debt = supply + claim` pre-state;
- amount above the outstanding claim;
- zero, negative, Boolean, non-whole, or above-U256 amounts;
- whole-ledger supply overflow before candidate construction;
- caller-supplied mutable balance state;
- foreign claim and custody identity;
- hostile mutation of a frozen claim;
- crossed external pre-state during independent verification;
- caller construction or replacement of the controlled result;
- claim reduction without the exact escrow credit;
- changed or missing canonical balance patch;
- sub-whole residue erasure;
- downstream custody distribution that changes same-asset supply.

## Formal evidence

The ESSO model proves inductive preservation of:

```text
debt = ledger_supply + outstanding_claim
outstanding_claim <= accrued_cumulative
protocol_escrow <= ledger_supply
```

Exact bounded result:

```text
model:                 zusd_protocol_fee_claim_realization_v1.yaml
model sha256:          6cb0613fd393fd5e06203f10c35ca0a988f6726462e841b9da3e57a9becd1aea
IR sha256:             7abf92ebab3fc4446b439d7349a6ec745124d8471036931f1f10cb75c741c1fe
ESSO source commit:    1145cf77668b6d86cda83d79820b13a65fbde12f
solvers:               Z3 4.15.4, CVC5 1.1.2
queries:               4 / 4 verified
solver agreement:      PASS
determinism trials:    2
result fingerprint:    c1f84f6dad88d771aff4eca0ae20faf31ffa9e4563c6e4cf5365a8c718f482a2
```

The Lean companion proves balance preservation, claim validity, escrow
backing, exact supply-plus-claim conservation, exact escrow delta, and the
whole-unit scaling law. The exact theorem file compiled with no `sorry`,
`admit`, user `axiom`, or `unsafe` declaration. Its printed theorem
dependencies are limited to Mathlib's standard `propext`, `Quot.sound`, and,
for escrow backing, `Classical.choice`. The theorem is imported by the default
`Proofs.lean` aggregate and that membership has a permanent test.

## Executable evidence

```text
realization tests:                     14 passed
related zUSD and fee-custody tests:    91 passed
ESSO and Lean wrapper tests:            4 passed
production-boundary audit:             PASS
Ruff:                                  PASS
new-file format check:                 PASS
strict mypy on three source modules:   PASS
Python compilation:                    PASS
git diff --check:                      PASS
machine-local path scan:               PASS
security red flags on changed surface: 0 high, 0 medium, 0 low
```

The complete core suite reached 723 passes and one skip before failing on the
pre-existing stale `fcis_fee_apportionment_v2_golden.json` fixture. The first
failure is outside this source manifest. A broad integration collection also
encountered five pre-existing import mismatches outside the changed surface.

## Commands not completed

- the complete core suite, due to the stale fee-apportionment fixture;
- broad integration tests, due to unrelated collection-time import errors;
- full `lake build Proofs`; it was stopped after 603 of 8,162 build jobs to
  preserve low disk space after the exact theorem compiled;
- hosted CI;
- Rust, Tau, or ZenoLedger byte and transition parity;
- a production current-state and atomic-publication refinement;
- concrete crash, concurrency, migration, and destination-adapter tests;
- mounted no-bypass and global R13 proofs.

## Residual risks and nonclaims

- The source balance table is exact but is not proven datastore-current.
- The complete zUSD inventory premise is not mounted or deployment-attested.
- The fee policy is not authenticated or bound to the current state.
- Realization and distribution are two local candidates rather than one atomic
  publication transition.
- The V2 certificate is absent from the mounted acceptance receipt, commit
  bundle, reopen history, and outbox lineage.
- The E8-to-whole-unit restriction leaves sub-whole value in the claim until a
  future whole amount is realizable.
- Fee-bearing borrowing remains disabled.
- M6 and R13 remain incomplete and unmounted.

## Next safest step

Define one state-bound fee-settlement candidate that consumes the exact current
claim and current balance state, authenticates the active distribution policy,
derives the realization and distribution transitions, and owns their combined
patch and certificate lineage. Publish that candidate only through the unique
expected-head commit capability with canonical reopen and no-bypass evidence.
