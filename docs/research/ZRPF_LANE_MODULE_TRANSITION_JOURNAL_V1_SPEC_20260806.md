# ZRPF Lane Module Transition Journal V1

Status: implemented and tested structural contract; research-only, unmounted,
and without guest-receipt, recursion, settlement, or publication authority.

Date: 2026-08-06

## Purpose

`GlobalEconomicEffectPlanV1` supplies canonical whole-command effect data. The
next narrow gap was an exact public statement for one route-selected lane
module and a deterministic relation between declared lane writes and the
committed lane state root.

`LaneModuleTransitionJournalV1` closes that structural gap. It binds one
economic action and lane to the exact module release, guest image, source and
toolchain roots, module schemas, route port schemas, lane pre-root, outcome,
and accepted effect/state commitments. `LaneStateTransitionWitnessV1` supplies
the proof-neutral same-action sparse-Merkle opening relation.

No constructor in this slice verifies a RISC0 receipt or grants ledger
authority.

## ShapeForge model

The exact PR stack contained the ShapeForge seed and lacked the remaining
promoted baseline artifacts. ShapeForge informed the typed Phi and explicit
gap record. No incomplete promoted artifact was imported.

```text
Phi := <
  M = lane_module_transition_journal_v1,
  S = one_route_selected_lane_occurrence,
  A = structural_lane_statement_binding,
  T = closed_journal_plus_same_action_sparse_openings,
  V = occurrence, route, lane, module_release, image, schemas, provenance,
      global_pre_post_roots, lane_pre_post_roots, effect_roots, port_roots,
      terminal_root, opening_witnesses, reject_code,
  O = construct, canonical_encode, derive_commitments, bind_release,
      bind_plan, validate_openings, compare_lane_writes,
  G = exact_profile_envelope, governed_route_dependency, exact_release,
      exact_module_and_route_schemas, bounded_journal, one_to_sixty_four,
      same_action, strict_unique_keys, continuous_roots, exact_write_pairing,
      rejected_shape_has_no_effect_or_post_state_fields,
  Obs = bound_lane_journal_or_typed_reject,
  K = journal_hash_plus_state_transition_commitment,
  E = failure_first_compile, AAA, BVA_0_1_64_65, mutation, malformed_codec,
      root_chain, route_release_metadata, resource_ceiling, source_closure,
  Gap = module_transition_core, authenticated_command_decode, guest_image,
        real_receipt, complete_partition_openings, lane_coordinator,
        route_composer, epoch_recursion, release_aware_verifier, publisher,
  N = wrong_action, wrong_lane, duplicate_or_reordered_key, broken_root_chain,
      mutated_effect_or_state_root, wrong_image_or_schema, excess_resource,
  Delta = declared_global_plan_refined_by_one_bound_lane_statement
>
```

Strongest evidence class: `contract`.

## Functional-core contracts

```text
LaneStateOpeningBatchInputV1
  -> typed reject
   | LaneStateOpeningBatchV1

LaneModuleTransitionJournalV1
+ OccurrenceBoundGlobalEconomicEffectPlanV1
+ LaneStateTransitionWitnessV1
  -> typed reject
   | BoundLaneModuleTransitionJournalV1
```

Rejected journals use the state-bound occurrence directly and require a
nonzero `LaneModuleRejectCodeV1`. Their outcome variant contains no global
post-root, lane post-root, effect root, state-transition root, port value root,
or terminal-obligation root.

The constructors and binders are deterministic, perform no I/O, and return no
effect application capability. The bound witness has private fields, borrows
the exact inputs, and is not serializable.

## Journal statement

Every journal commits:

- application and domain;
- profile and writer epoch;
- occurrence, route release, and economic action;
- lane and exact content-derived module release;
- guest image, state/command/effect/private-port schemas, command variants,
  specification, source, and toolchain roots;
- route-specific receipt journal, input-port, and output-port schemas;
- global and lane pre-state roots;
- one accepted or rejected outcome.

An accepted outcome additionally commits:

- global post-state root and full global effect-plan commitment;
- lane post-state root and lane-local effect-row root;
- lane state-transition commitment;
- private input and output port value roots;
- lane-local terminal-obligations root.

The journal hash is domain-separated and includes every field. Exact Postcard
decoding rejects empty, oversized, trailing, malformed, noncanonical, or
self-inconsistent inputs.

## Same-action lane state openings

A changed lane transition carries 1-64 existing validated
`SparseMerkleCellTransitionWitnessV1` values. The batch requires:

```text
for every witness w:
  w.economic_action_id = batch.economic_action_id

first.claimed_pre_root = lane_pre_state_root
last.claimed_post_root = lane_post_state_root

for each adjacent pair (a, b):
  a.claimed_post_root = b.claimed_pre_root

cell_key[0] < cell_key[1] < ... < cell_key[n-1]
```

The strict key order provides unique writes without introducing an implicit
intra-command rewrite order. A changed batch rejects equal lane pre/post roots.
An unchanged transition has no openings and commits one identical lane root.

During accepted binding, lane-write rows are projected from the already bound
global effect plan, sorted by object ID, and compared exactly to opening key,
pre-value hash, and post-value hash. A changed opening count must equal the
lane-write count. An unchanged transition requires zero lane-write rows.

## Release and route binding

The caller cannot select release metadata independently. The binder derives
the lane dependency from the occurrence's governed route and resolves the
exact module release from the profile-bound lane registry. It checks:

- release ID and lane;
- guest image and module schema/provenance roots;
- route receipt, input-port, and output-port schema roots;
- encoded journal size against the module ceiling and the necessary
  per-journal route ceiling.

The binder also checks the exact occurrence envelope, state root, action ID,
global effect plan, lane effect rows, state-transition commitment, terminal
obligations, and lane writes.

## Executable evidence

The Rust tests use explicit Arrange, Act, and Assert sections. They cover:

- lower and upper accepted opening counts at 1 and 64;
- typed rejection at 0 and 65;
- same-action enforcement, duplicate and reordered keys, skipped root-chain
  links, and changed-root identity rejection;
- unchanged-transition identity and commitment separation;
- exact state-transition and journal codec round trips, empty/trailing/excess
  input, and mutated versions;
- nonzero reject codes and disjoint accepted/rejected binders;
- every occurrence envelope field;
- module release, image, module schema/provenance, and route port schemas;
- module journal-byte ceilings;
- independent mutations of accepted global, effect, lane, state-transition,
  and terminal roots;
- exact lane-write/opening equality;
- private-constructor and non-serializable compile-fail checks.

## Nonclaims

- Sparse-Merkle openings authenticate only the declared lane cells and roots.
  They do not establish complete lane-state coverage or validate other global
  partitions.
- The global post-state and non-lane-write effect rows remain declared values.
  A deterministic module core and guest must derive them from authenticated
  inputs.
- Private-port value roots are committed public outputs. Port value pairing and
  cross-lane economics require coordinator and route-composer proofs.
- The lane binder does not prove the route's aggregate journal-byte ceiling.
  The route composer must sum all selected module journals and enforce it.
- No receipt kind, RISC0 image execution, assumption resolution, recursion,
  proof-shape registry, verifier revocation, data availability, finality,
  current-head check, atomic persistence, outbox delivery, or migration is
  implemented here.
- No API, CLI, UI, Tau bridge, recovery path, legacy writer, or ZenoLedger
  publisher is mounted to this contract.
- This slice adds no value movement, RC status, production-readiness,
  formal-verification, or whole-economy settlement claim.

## Next proof-worthy gap

Implement the deterministic Asset Transfer lane transition core and import the
same Rust function into its first leaf guest. The guest must derive accepted
effects and rejected no-op outcomes from authenticated command and state data.
Then add a release-aware host verifier that accepts only the exact governed
image and canonical journal bytes and still returns no publication capability.
