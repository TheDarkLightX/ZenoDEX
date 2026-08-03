# M6 zUSD supply-delta closure V1

## Exact identity

```text
implementation_commit: f0b35143e7a8d6271c956340fdaad42042dfea3f
implementation_tree:   38363dbe0fe92978058de33dab5f2681f3c37328
implementation_parent: f5c3d0e66852c8ec49112a7ed3a8119bab71bf47
posture:                IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint closes one local M6/R13 accounting defect at the zUSD monetary
bridge. It does not complete R13, runtime refinement, mounted mediation, or M6.

## Counterexample and stop-line rule

The monetary core increases debt by principal plus borrowing fee. The bridge
previously credited only principal to the zUSD ledger. The protocol-revenue
field is cumulative history; no mounted transition currently realizes it as an
outstanding fee claim or protocol-owned zUSD balance.

The bridge now rejects every nonzero borrowing-fee mint before any successor,
nonce, or effect can escape:

```text
nonzero borrowing fee
and no mounted fee-claim settlement
-> Reject("zUSD borrowing fee claim settlement is not mounted")
```

The existing zero-fee runtime remains executable. Fee-bearing borrowing remains
closed until an exact current claimant fiber and settlement transition exist.

## Closed transition relation

Every accepted monetary operation now carries an independently replayable
`ZUSDSupplyDeltaCertificateV1` satisfying:

```text
debt_delta = ledger_supply_delta + protocol_fee_accrual_delta
```

The certificate binds the exact action, amount, fee, pre/post debt, pre/post
ledger supply, and pre/post cumulative fee accrual. The verifier receives the
expected transition instance separately and reconstructs every derived field
and the canonical certificate root.

`ledger_supply` is the complete zUSD amount represented by the current
`BalanceTable`, including Stability Pool escrow accounts. This name avoids a
false claim that every ledger balance is transferable. Custody outside that
table remains a later global-composition obligation.

The current bridge stores zUSD ledger balances in whole units while the
monetary kernel uses E8. It therefore accepts only exact whole-unit transports
for debt, free debt, Stability Pool debt, protocol fee accrual, and individual
Stability Pool deposits. A fractional transport rejects rather than rounds.

## Formal evidence

The ESSO model is intentionally a signed-delta model. It proves preservation of
the transition relation without treating a cumulative revenue counter as a
current liability:

```text
model:                 zusd_supply_liability_delta_v1.yaml
model sha256:          cdfcaa6a230a3414f257176d96144b85a37c8e9643a450d05b831b8337a7f240
solvers:               Z3 4.15.4, CVC5 1.1.2
queries:               4 / 4 verified
solver agreement:      PASS
determinism trials:    2
result fingerprint:    3b1629dfe49162b4a6104a59b05dc2bc3e1c0efc3e1df43f238debcf7d6ffd56
ESSO source commit:    7f80c6216be85c827e8d1cc2fa08ee3107a74588
```

The Lean companion proves mint and burn balance preservation, exact delta
certificate construction, preservation from balanced pre-state, and
certificate composition. The exact theorem file compiled successfully in the
pinned local Mathlib environment. Its main theorems report only Mathlib's
standard `propext` and `Quot.sound` dependencies. The placeholder scan found no
`sorry`, `admit`, or equivalent proof placeholder.

The Lean `Balanced` predicate refers to an explicit current outstanding-fee
fiber. The cumulative runtime revenue counter does not satisfy that role by
itself.

## Executable evidence

The final focused gate reported:

```text
42 tests passed, 38 deselected
Ruff passed on the four changed Python and test files
strict mypy passed on both changed source modules
Python compilation passed
git diff --check passed
ESSO Z3/CVC5 verification passed
Lean theorem file compiled
Lean placeholder scan passed
```

Permanent negative evidence includes:

- omission of the fee-accrual delta from a fee-bearing certificate;
- Boolean values masquerading as certificate integers;
- crossed command/transition certificate substitution;
- decreasing cumulative fee accrual;
- fractional and whole-unit fee-bearing runtime mints without mounted claim
  settlement;
- a monkeypatched core that creates debt without matching ledger supply or fee
  accrual;
- rejection before successor state, nonce, or effects escape.

The security scanner reported zero high findings, two medium broad-exception
findings, and three low raw-mapping findings. Those findings are inherited
imperative-shell surfaces in the existing bridge and are not proof of safety.

## Baseline failure retained

`tests/chaos/test_live_surface_tau_network_chaos.py` fails at both this target
and the untouched parent because its fixture attempts to mutate a frozen
committed state snapshot. The exact error is:

```text
TypeError: committed state snapshot is immutable
```

This is recorded as inherited assurance debt. It was not weakened, skipped, or
rewritten for this checkpoint.

## Commands not run

- the complete repository test suite;
- hosted CI;
- full `Proofs.lean` aggregate compilation;
- Rust or Tau runtime parity;
- production Tau or ZenoLedger deployment tests;
- concrete crash, concurrency, migration, and destination-adapter tests;
- mounted no-bypass audit;
- global R13 value-lifecycle proof.

## Residual risks and nonclaims

- There is no exact current `OutstandingProtocolFeeClaimV1` or deterministic
  protocol-fee escrow in authoritative state.
- The existing borrowing-fee router has no mounted caller or exact claimant
  identities.
- The whole-unit zUSD `BalanceTable` cannot represent arbitrary E8 borrowing
  fees without a base-unit migration or exact residue owner.
- The delta certificate is bridge effect evidence. It is not yet bound through
  the acceptance receipt, commit bundle, publication transaction, reopen, or
  outbox lineage.
- Global custody still requires composition with Stability Pool, AMM/LP,
  perps, native-host, and any external-ledger fibers.
- Ambient configuration and complete authenticated execution context remain
  outside this checkpoint.
- The runtime forward-simulation theorem and mounted mediation proof remain
  open.

## Next safest step

Define an immutable current protocol-fee claim or escrow with exact claimant
identities and a deterministic realization transition. Bind it into the global
economic state, zUSD fee router, value-delta certificate, acceptance receipt,
and unique publication atom. Migrate zUSD accounting to base E8 units or prove
an exact residue-owner policy before enabling nonzero borrowing fees.
