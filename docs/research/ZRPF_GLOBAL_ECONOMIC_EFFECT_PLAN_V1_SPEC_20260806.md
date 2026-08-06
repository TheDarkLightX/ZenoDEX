# ZRPF Global Economic Effect Plan V1

Status: implemented and tested structural contract; research-only, unmounted,
and without proof-verification, settlement, or publication authority.

Date: 2026-08-06

## Purpose

`GlobalEconomicStateV1` commits whole-economy partition roots and a
state-bound command now has one independently derived governed route. The
remaining structural gap was an explicit, canonical representation of the
complete global effects proposed for that command.

`GlobalEconomicEffectPlanV1` closes that representation gap. It supplies one
closed tagged row registry, exact per-asset reconciliation summaries, bounded
canonical encoding, and a constructor-private witness that binds the plan to a
`StateBoundEconomicCommandOccurrenceV1`.

The contract is proof-neutral. A future guest must authenticate every declared
row against pre-state openings, execute lane semantics, and establish the
post-state root before a release-aware verifier may create epoch authority.

## ShapeForge model

The exact PR stack contained the promoted ShapeForge seed and lacked the other
promoted baseline artifacts. ShapeForge was used for typed Phi preflight and
gap discipline. No dirty or incomplete promoted artifact was imported.

```text
Phi := <
  M = global_economic_effect_plan_v1,
  S = one_state_bound_command_effect_proposal,
  A = global_effect_completeness,
  T = canonical_bounded_effect_plan_plus_structural_reconciliation,
  V = application, domain, profile, writer_epoch, occurrence, route,
      pre_root, post_root, closed_effect_rows, per_asset_reconciliations,
  O = construct_rows, canonicalize, derive_roots, reconcile, bind_occurrence,
  G = nonempty_bounded_rows, sorted_unique_ids, nonzero_or_changing_effects,
      per_asset_conservation, custody_claim_equality, fee_allocation_equality,
      liability_and_reserve_delta_equality, exact_replay_rows,
      external_only_outbox, route_issue_burn_policy,
  Obs = GlobalEconomicEffectPlanV1_or_typed_reject,
  K = semantic_effect_commitment_plus_full_plan_commitment,
  E = failure_first_regression, AAA, BVA, overflow, mutation,
      canonical_codec, compile_fail_witness_tests, source_closure,
  Gap = authenticated_state_openings, lane_economic_semantics, proof_guest,
        route_composer, epoch_recursion, release_aware_verifier, migration,
        atomic_publisher,
  N = omitted_asset_summary, duplicate_row, arithmetic_overflow,
      internal_outbox, unmatched_outbox_value, stale_envelope,
      wrong_authorization, wrong_replay_row, forbidden_issue_or_burn,
  Delta = opaque_effect_commitment_refined_by_an_explicit_bound_plan
>
```

Strongest evidence class: `contract`.

## Functional-core contract

```text
GlobalEconomicEffectBodyInputV1
  -> typed reject
   | canonical GlobalEconomicEffectBodyV1

GlobalEconomicEffectPlanV1
+ StateBoundEconomicCommandOccurrenceV1
  -> typed reject
   | OccurrenceBoundGlobalEconomicEffectPlanV1
```

The constructors are deterministic and perform no I/O. Rows and plans are
immutable owned values. The occurrence-bound witness borrows exact inputs, has
private fields, and is not serializable.

## Closed effect row registry

The eleven V1 row kinds are:

1. account movement;
2. authorized issue or burn;
3. custody and claimant transition;
4. liability transition;
5. named reserve transition;
6. fee charge, allocation, and residue;
7. authorized reward or slash movement;
8. lane object write;
9. occurrence object or grant-spend consumption;
10. terminal-obligation transition;
11. external outbox enqueue.

Every row has a domain-separated canonical ID. The body constructor sorts rows
by ID, rejects duplicates, sorts reconciliation rows by asset ID, and rejects
missing, duplicate, or extraneous asset summaries. Rows with explicit pre/post
state reject a second write to the same typed lane target because V1 provides
no intra-plan sequence field. Exact decoding revalidates canonical order,
unique write targets, and all equations.

## Structural equations

For each asset, account movements and reward/slash movements contribute equal
debit and credit. Issue contributes one authorized issue and one credit. Burn
contributes one debit and one authorized burn.

```text
debit + authorized_issue = credit + authorized_burn

owned_and_custodied_post
  = owned_and_custodied_pre + authorized_issue - authorized_burn

supply_post
  = supply_pre + authorized_issue - authorized_burn
```

The implementation uses checked addition on both sides so subtraction and
underflow cannot enter the consensus contract.

Changed liability and reserve rows reconcile their deltas to the per-asset
summary:

```text
liabilities_pre + changed_liability_post
  = liabilities_post + changed_liability_pre

named_reserves_pre + changed_reserve_post
  = named_reserves_post + changed_reserve_pre
```

Each custody row independently enforces:

```text
custody_pre = claimant_entitlements_pre + unencumbered_reserves_pre
custody_post = claimant_entitlements_post + unencumbered_reserves_post
```

Each fee row independently enforces:

```text
fee_charged = allocated + carried_residue
```

Zero amount flows, self-transfers, nonchanging writes, arithmetic overflow, and
nonchanging global roots reject.

## Semantic and full commitments

The action record already commits an `effect_commitment`. Action authorization
bindings and grant-spend nullifiers are derived from that action record. A
single root containing both values would create a circular construction.

V1 therefore uses two explicit roots:

- `effect_semantics_root` commits stable economic meaning. It excludes
  occurrence-consumption rows and excludes action-derived authorization
  bindings and outbox funding-row IDs. It still commits the issue/burn or
  reward/slash kind, lane, asset, amount, buckets, authority scope, outbox
  destination, payload, and all other economic fields.
- `effect_rows_root` commits every complete row, including authorization,
  replay, and exact outbox-to-value-effect references.

The action's `effect_commitment` binds the post-state root, semantic root, and
reconciliation root. The plan commitment additionally binds the full row root,
application, domain, profile, writer epoch, occurrence, route, and pre-state.
The occurrence binder checks the action commitment, authorization rows,
consumed objects, exact grant spend, and governed route issue/burn policy.

## Outbox rule

An outbox row must name `EXTERNAL_CUSTODY`, use a destination domain different
from the local domain, and reference one exact value-effect row with the same
asset and amount. One value effect may fund at most one outbox row. Same-ledger
movement remains in ordinary account rows and cannot enter the external
outbox.

Destination registration and finality policy require authenticated registry
openings and remain future guest obligations.

## Preflight and pattern record

- Authority owned: canonical effect data and structural reconciliation.
- Authority excluded: lane economics, state opening authentication, receipts,
  current-head checks, durable replay insertion, and publication.
- Ownership: rows, bodies, and plans are immutable owned data.
- Construction: row constructors reject invalid local shapes; body and plan
  constructors establish cross-row and envelope invariants.
- Mutation: sorting uses only constructor-local vectors before immutable values
  exist.
- Rejection: no witness, state mutation, receipt, replay update, outbox
  delivery, or publication capability is returned.
- Complexity: at most 1,024 effect rows and 256 reconciled assets; exact plan
  input is capped at 1 MiB.
- Compatibility: this additive research ABI is unmounted and changes no active
  profile or historical proof.

## Executable evidence

The Rust contract tests use explicit Arrange, Act, and Assert phases. They
cover:

- every one of the eleven closed row variants;
- zero, one, and `u128::MAX` amount boundaries;
- custody, fee, owned, supply, liability, and reserve neighbor mutations;
- aggregate arithmetic overflow;
- duplicate rows and missing, duplicate, or extraneous reconciliations;
- duplicate unsequenced writes to one typed lane target;
- canonical sorting, identity separation, exact round trip, trailing bytes,
  and mutated version bytes;
- exact outbox funding, duplicate funding, and internal destination rejection;
- exact application, domain, profile, writer epoch, occurrence, route,
  pre-state, semantic effect, authorization, consumed-object, grant-spend, and
  route issue/burn bindings;
- semantic commitment invariance under action-derived binding and outbox
  reference changes while the full row root changes;
- private-constructor and non-serializable compile-fail checks.

## Nonclaims

- The reconciliation rows are explicit declarations. V1 does not authenticate
  their values against balance, supply, custody, liability, reserve, replay,
  terminal, or outbox partition openings.
- Lane modules and route-composer guests still must derive these rows from the
  deterministic transition and prove exact pre/post state relations.
- The contract does not establish external destination registration, bridge
  finality, acknowledgment, timeout, refund, or destination idempotency.
- The contract does not prove terminal coverage, coexistence across module
  releases, migration continuity, Oracle policy, or perps/zUSD solvency.
- No Python/Tau/Lean/Kani refinement, RISC0 guest, receipt, epoch recursion,
  release-aware verifier, current-head check, ZenoLedger commit, API/UI mount,
  value movement, RC, production-readiness, formal-verification, or
  whole-economy settlement claim is added.

## Next proof-worthy gap

The additive lane-module transition journal now binds lane-write rows to
same-action sparse-Merkle openings and binds route-selected release metadata.
The next gap is a deterministic Asset Transfer module core and leaf guest that
derives every accepted effect row and rejected no-op from authenticated command
and state inputs. A release-aware receipt verifier must still authenticate the
exact image and journal before any coordinator or epoch layer can consume it.
