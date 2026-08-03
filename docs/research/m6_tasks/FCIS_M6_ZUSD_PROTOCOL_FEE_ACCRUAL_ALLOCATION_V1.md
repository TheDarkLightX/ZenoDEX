# M6 zUSD protocol-fee accrual allocation V1

## Exact identity

```text
implementation_commit: 5cc236a6bf514369330da8ca31c9b51087454eb5
implementation_tree:   cdab351311a38657f2641d68ac5851ec8e53f917
implementation_parent: 7a66d410b4da38402c385baf354ad620138836be
posture:               LOCAL_ALGEBRA_PROVED_IMPLEMENTED_TESTED_UNMOUNTED
```

This checkpoint allocates each exact positive zUSD borrowing-fee occurrence
when the scalar claim accrues. It preserves the occurrence boundary required by
SRGD, retains the configuration and destination that created each role claim,
and carries no runtime or publication authority.

M6, R13, authenticated borrowing lineage, active-configuration authority,
current-state provenance, atomic publication, and mounted no-bypass remain
open.

## Representation repair

Allocating a scalar outstanding claim only when it is later realized is
incorrect because SRGD is stateful and occurrence-sensitive. At denominator
`10_000` with weights `(2_500, 2_500, 5_000)`:

```text
one occurrence of 3:    (1, 1, 1)
occurrences 1 then 2:   (1, 0, 2)
```

Both total three atoms. They are different semantic histories. The rejected
prototype would have erased that distinction by allocating the later aggregate.
The implemented transition applies SRGD once per supplied exact occurrence.

A second counterexample concerned policy rotation. Three unqualified role
totals would allow a later configuration to redirect earlier outstanding
claims. Each nonzero current entry now retains:

```text
(configuration_root, role, destination, outstanding_e8)
```

The aggregate separately retains cumulative buyback, treasury, and rewards
totals. A destination rotation creates new qualified entries without changing
the owners of older claims.

## Closed local relation

For scalar claim `C`, role-claim state `R`, and one conserved allocation `a`:

```text
C.outstanding_e8 = sum(R.outstanding_by_role_e8)
C.accrued_cumulative_e8 = sum(R.accrued_cumulative_by_role_e8)
sum(a.role_amounts_e8) = a.amount_e8
```

One accepted local transition adds the same occurrence amount to the scalar
current and cumulative claims and adds each role amount to its current and
cumulative role claims. Every role current claim remains at most its cumulative
accrual.

The role state also binds:

```text
fee distribution domain
zUSD asset identity
scalar-claim custody identity
canonical SRGD apportionment-state digest
```

These last two fields close two final adversarial-review counterexamples:

- a role partition from one custody identity paired with a scalar claim from
  another custody identity;
- an empty SRGD state substituted after nonempty fee history, resetting the
  cumulative rounding state while retaining the claims.

Both traces failed before the repair and remain permanent negative tests.

## Candidate and verifier boundary

`ZUSDProtocolFeeAccrualAllocationSourceV1` is caller-constructible data. It has
no authority. The deriver requires exact values, reconstructs one scalar claim
transition, runs one SRGD transition, constructs the configuration-qualified
role successor, and checks both scalar-to-role partition equations.

The controlled candidate contains:

```text
self-consistent configuration claim
scalar claim transition
one fee contribution
pre/post role claims
pre/post SRGD state through the apportionment transition
one allocation
```

The independent verifier recomputes the complete candidate from the external
source instance. The candidate exposes no balances, patch, current-state root,
authority header, receipt, bundle, outbox, or publication capability. Its
`occurrence_root` is the scalar-claim transition identity and is explicitly not
a commit receipt.

The configuration check proves internal B1A consistency only. It does not prove
that the configuration is active for the current committed state.

## Formal evidence

The ESSO model has twelve bounded state variables, eight actions, and six
invariants. Z3 and CVC5 agree that initialization and every action preserve:

```text
scalar outstanding = sum of role outstanding
scalar cumulative = sum of role cumulative
each role outstanding <= that role cumulative
an inconsistent configuration, crossed custody, or crossed SRGD lineage
cannot produce an accepted transition
```

Exact bounded result:

```text
model sha256:       f7f419b39e1d5a88fa7133dc8d339753b7258a0ea45efebca4893054af8700f9
ESSO IR sha256:     4485edf34ece4bacef9a4710b8fa7b036be72c63307cc41a70a303ee296e4aaa
ESSO source commit: 1145cf77668b6d86cda83d79820b13a65fbde12f
solvers:            Z3 4.15.4, CVC5 1.1.2
queries:            9 / 9 verified
solver agreement:   PASS
determinism trials: 2
result fingerprint: f7c2c7f563b93fdcb2963007532b0b9b7dd5b5b8b9ad26af47033ad142aced9d
```

Nine ESSO tests include eight semantic mutants covering the configuration,
custody, lineage, and conservation guards plus the four scalar/role cumulative
updates.

The Lean companion proves one-step preservation of the two partition equations,
role-current bounds, their conjunction, and induction over an ordered occurrence
word. It compiled without `sorry`, `admit`, a user `axiom`, or `unsafe`.
Printed dependencies were Mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`.

The Lean theorem deliberately assumes the role allocation is conserved. It does
not prove SRGD selection, U256 refinement, authenticated occurrence extraction,
configuration activation, destination authority, or runtime refinement.

## Executable evidence

```text
focused core, ESSO, and Lean tests:     24 passed
broader fee/config/zUSD test selection: 110 passed, 1 pre-existing failure
Ruff format and lint:                   PASS
strict mypy on changed modules:         PASS
configured repository mypy:            PASS; 25 source files
Python compilation:                     PASS
production-boundary audit:              PASS within its declared checks
git cached diff check:                  PASS
machine-local path scan:                PASS
security red flags on changed surface:  0 high, 0 medium, 0 low
```

The broader selection's sole failure is the pre-existing source-hash drift in
`tests/fixtures/fcis_fee_apportionment_v2_golden.json`: the fixture records an
older digest for `fcis_fee_apportionment_allocator.py`. This slice did not touch
that allocator and did not regenerate unrelated release evidence.

## Luna completeness review

Five read-only GPT-5.6 Luna passes reviewed economic scope, authority/runtime
refinement, durability and resilience, mounted no-bypass/user stories, and
cross-model composition/promotion.

Four worker wrappers completed normally. The durability worker emitted a valid
structured final result before its 600-second wrapper timeout. The independent
packet-shape checker accepted all five payloads. The official fleet verifier
remains `FAIL` because one worker record timed out. The reviews are advisory and
do not promote a claim.

Confirmed local findings repaired here:

- scalar-custody identity could be crossed;
- SRGD entitlement history could be reset;
- the original ESSO mutation suite did not exercise enough guards or updates.

Confirmed M6-wide gaps retained for future formal specifications:

1. No closed global custody identity covers user balances, AMM reserves, LP
   ownership, perps collateral and fee pools, zUSD claims, reward budgets,
   buy-and-burn custody, and sealed-bid escrow.
2. Fee accrual is not extracted from one authenticated accepted borrowing
   occurrence and current state.
3. The active fee configuration and destinations are not state-bound.
4. Scalar accrual, role allocation, debt/supply changes, history, nullifier,
   receipt, and outbox are not one atomic production transition.
5. ZenoLedger's canonical writer, finality, Tau outage/rejoin policy, reopen,
   and outbox acknowledgment are not one mounted formal state machine.
6. Runtime-to-formal projections and forward simulation remain incomplete.
7. The production entrypoint and credential inventory is incomplete, so R12
   no-bypass and R13 whole-system value safety remain open.

## Formal-spec queue for the next Luna cycle

The next spec-writing cycle should proceed in dependency order and require a
separate adversarial pass before accepting each model:

1. `GlobalCustodyStateV1`: all managed assets and every custody/liability/burn
   bucket, with complete transfer and terminal-drain actions.
2. `AuthenticatedBorrowFeeOccurrenceV1`: accepted borrow lineage, exact fee
   amount, current pre/post roots, active policy, and replay/nullifier identity.
3. `StateBoundFeeAccrualAllocationV2`: one paired scalar, role, SRGD, and
   configuration transition with total runtime projection.
4. `RoleQualifiedFeeRealizationV2`: consume exact qualified entries and forbid
   scalar-only settlement from leaving the partition inconsistent.
5. `SovereignAvailabilityV1`: ZenoLedger canonical authority, optional Tau
   observation, outage/censorship/rejoin, finality, and single-writer epochs.
6. `AtomicEconomicPublicationV1`: one expected-head linearization point for
   state, history, nullifier, receipt, economic certificate, epoch, and outbox.
7. `MountedMediationV1`: deployment-derived entrypoint and credential inventory,
   unique commit capability, and complete day-one BDD/BVA/stateful coverage.
8. A small Lean/Tau composition theorem whose premises remain explicit for
   cryptography, oracle authority, inventory completeness, and storage
   durability.

Each model must include named semantic mutants, minimized counterexamples,
runtime projection fields, and explicit nonclaims. Solver success cannot replace
runtime refinement or mounted evidence.

## Residual risks and nonclaims

- The amount is supplied candidate data rather than derived from an authenticated
  accepted borrow.
- The scalar and role pre-states are exact values but are not proven datastore-current.
- A B1A-valid configuration is not necessarily active for the current state.
- The SRGD digest binds local lineage but does not provide current-state authority.
- Configuration-qualified claims are not yet consumed by the existing scalar
  realization candidate. Mounting both paths would allow the scalar claim to
  shrink while the role partition remained unchanged.
- Rust, Tau, and ZenoLedger canonical-byte and transition parity are absent.
- No receipt, commit bundle, reopen history, outbox, crash refinement, or
  no-bypass proof contains this candidate.
- Fee-bearing borrowing remains disabled.
- M6 and R13 remain incomplete, unmounted, and non-promotable.

## Current M6 position

The exact-head Research Kernel ledger records meaningful research evidence for
R01-R07, abstract models for R09-R11, and open R08, R12, and R13. Its promotion
authority remains `NONE`.

Under the strict completion rule requiring `PROVED`, `IMPLEMENTED`, `MOUNTED`,
and `TESTED` for the same promotion subject, the score remains `0 / 13`.

## Next safest implementation step

Define and verify `AuthenticatedBorrowFeeOccurrenceV1` plus an exact
`StateBoundActiveFeeConfigurationV2`. Compose those values with this local
transition in one candidate whose pre-state is the current ZenoLedger head.
Then replace scalar-only realization with exact role-entry consumption before
connecting the result to the unique atomic publication capability.
