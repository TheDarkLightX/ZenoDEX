# M6 zUSD protocol-fee claim V1

## Exact identity

```text
implementation_commit: f17fa72cfec0c4b9a2b65603c401caaf337747e5
implementation_tree:   f0a30529e97288f718a598578f44c948288e6a8b
implementation_parent: 43f302a454500e05fea98b499ece4a93971f45f9
posture:                IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint closes the local representation defect left by the earlier
zUSD supply-delta stop line. It introduces an exact current protocol-fee claim
and binds that claim into the monetary-state schema and transition
certificate. It does not complete R13, runtime refinement, mounted mediation,
or M6.

## Current-liability relation

The core's cumulative protocol-revenue counter is historical evidence. It
cannot determine the amount that is currently unissued. The new immutable
claim state records both values and derives the realized history:

```text
accrued_cumulative_e8
  = outstanding_e8 + realized_cumulative_e8

debt_e8
  = ledger_supply_e8 + outstanding_e8
```

The V2 transition certificate proves the exact local delta relation:

```text
debt_delta_e8
  = ledger_supply_delta_e8 + outstanding_claim_delta_e8
```

Certificate construction consumes one exact paired pre/post claim rather than
parallel roots, identities, and amounts. Claim identity, outstanding amount,
canonical roots, and action-specific transition laws are derived internally.
The independent checker reconstructs the certificate from the exact external
claim pair and exact debt and supply endpoints.

## State and migration rules

`ZUSDProtocolFeeClaimV1` is a controlled, frozen, slotted value. It binds:

```text
zUSD asset identity
deterministic protocol-fee custody identity
current outstanding amount in E8
cumulative accrued amount in E8
```

The monetary state now has an explicit V2 schema carrying this value. A V1
state with zero cumulative fee history has one deterministic migration to the
empty V2 claim. A V1 state with nonzero cumulative fee history rejects because
the split between realized and outstanding value cannot be recovered from the
cumulative counter.

The custody identity is derived from the configured chain identity. A foreign
asset or custody identity rejects before a successor, nonce, certificate, or
effect can escape.

## Stop-line rule

Fee-bearing borrowing remains disabled:

```text
nonzero borrowing fee
and no mounted atomic claim realization
-> Reject("zUSD borrowing fee claim settlement is not mounted")
```

The implementation can represent and verify fee accrual and settlement
candidates. It does not yet authorize a claimant, credit a protocol account,
select distribution recipients, or publish the claim and ledger update in one
atomic transition. Zero-fee borrowing continues to use the live monetary
bridge and carries an exact empty claim.

## Counterexamples retained

The permanent negative evidence covers:

- treating cumulative revenue as the current outstanding liability;
- guessing a V2 claim from a V1 state with nonzero fee history;
- substituting a foreign asset or custody identity;
- pairing claim amounts with independently supplied roots;
- using an accrual transition under a stutter or burn action;
- omitting or inventing a claim delta;
- Boolean values masquerading as protocol integers;
- direct constructor and frozen-object mutation attempts;
- zero-value settlement as a second state-transition spelling;
- fee-bearing mint before claim realization is mounted;
- a debt mutation without matching ledger supply or claim accrual;
- rejection with an escaped successor, nonce, or effect.

## Formal evidence

The ESSO model proves inductive preservation of:

```text
debt = ledger_supply + outstanding_claim
outstanding_claim <= accrued_cumulative
```

Exact bounded result:

```text
model:                 zusd_protocol_fee_claim_v1.yaml
model sha256:          f1f2433fbc049d9189ea52299cee18ec51262a1eb153c18d1c13c63dc5fc6fea
IR sha256:             e653501bf51bfccd6526f76d09cf9999b19907a33f5b191c33ac259526957ab7
ESSO source commit:    1145cf77668b6d86cda83d79820b13a65fbde12f
solvers:               Z3 4.15.4, CVC5 1.1.2
queries:               5 / 5 verified
solver agreement:      PASS
determinism trials:    2
result fingerprint:    9385398823ebd4b362847e5394d28d840cf559940f7d60df99502abd20740cca
```

The Lean companion proves mint, exact claim settlement, and repayment
preservation; the historical partition equation; signed delta exactness; and
delta composition. The exact theorem file compiled in the pinned local
Mathlib environment. The printed main theorem dependencies are `propext` and
`Quot.sound`. The placeholder scan found no `sorry`, `admit`, user `axiom`, or
`unsafe` declaration.

## Executable evidence

```text
focused claim and bridge tests: 17 passed
all zUSD core tests:             61 passed
all zUSD integration tests:      134 passed, 10 skipped
Ruff:                            PASS
strict mypy on changed sources:  PASS
Python compilation:              PASS
new-file format check:           PASS
git diff --check:                PASS
ESSO Z3/CVC5:                    PASS
Lean exact theorem file:         PASS
Lean placeholder scan:           PASS
```

The security scanner reported zero high findings, two medium broad-exception
findings, and three low raw-mapping findings. The medium findings are inherited
exception-to-reject boundaries in the existing monetary bridge. The raw
mappings are codec and normalization edges. The existing bridge remains a
large complexity hotspot and retains grandfathered formatting debt.

## Commands not run

- the complete repository test suite;
- hosted CI;
- full `Proofs.lean` aggregate compilation;
- Rust or Tau canonical-byte and transition parity;
- production Tau or ZenoLedger deployment tests;
- concrete crash, concurrency, migration, and destination-adapter tests;
- mounted no-bypass audit;
- global R13 value-lifecycle proof.

## Residual risks and nonclaims

- Fee claimant and recipient authority are not authenticated.
- Claim settlement is a deterministic candidate and has no mounted caller.
- The whole-unit zUSD `BalanceTable` cannot realize arbitrary E8 fees without
  a base-unit migration or an exact residue-owner rule.
- The V2 certificate is not yet carried through acceptance receipt, commit
  bundle, atomic publication, canonical reopen, and outbox lineage.
- The complete zUSD supply inventory and all external custody fibers remain
  outside this local theorem.
- Rust, Tau, ZenoLedger, and production-host refinements remain open.
- Runtime forward simulation and deployment-complete mediation remain open.

## Next safest step

Define the authenticated protocol-fee distribution policy and the exact
claimant account state. Add one atomic realization transition that reduces the
claim by exactly the amount credited to the ledger, handles E8 residue without
rounding ambiguity, and binds both changes through the receipt, bundle,
publication, reopen, and no-bypass surfaces. Only then may fee-bearing
borrowing be enabled.
