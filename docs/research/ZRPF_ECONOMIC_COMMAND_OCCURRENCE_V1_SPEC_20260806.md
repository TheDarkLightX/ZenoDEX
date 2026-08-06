# ZRPF EconomicCommandOccurrenceV1 Contract

Status: implemented and tested structural contract; research-only, unmounted,
and without settlement authority.

Date: 2026-08-06

## Purpose

`EconomicActionRecordV1` commits semantic action identity, authorization
subject and scope, nonce, validity, pre-state, action semantics, effects, and
consumed objects. Its identity deliberately excludes proof-envelope details.
It does not identify where the command occurs or which governed whole-economy
profile and route must interpret it.

`EconomicCommandOccurrenceV1` closes that specific gap without changing the
existing action or nullifier ABIs. It adds:

- canonical `(height, tx_index, op_index)` position;
- exact `EconomicProfileIdV1`;
- exact writer epoch;
- exact `RouteReleaseIdV1`;
- the complete existing `AuthorizedEconomicActionV1` as one owned aggregate.

The profile binder recomputes all structural relations before producing a
constructor-private, non-serializable
`ProfileBoundEconomicCommandOccurrenceV1`.

## ShapeForge model

```text
Phi := <
  M = zenodex_economic_command_occurrence_v1,
  S = profile_route_occurrence_binding,
  A = guard,
  T = contract_strengthening,
  V = position, profile_id, writer_epoch, route_release_id,
      authorized_action, active_profile, route_registry,
  O = derive_occurrence_id, bind_to_active_profile,
  G = exact_profile_id, exact_writer_epoch, exact_route_registry_root,
      governed_route_occurrence, exact_command_variant,
  Obs = occurrence_id, profile_bound_occurrence, bound_route,
  K = (height, tx_index, op_index),
  E = typed_contract, fixed_vectors, AAA_negative_tests,
      BVA_and_BVE_boundaries, compile_fail_architecture_tests,
  Gap = authenticated_command_witness, state_authenticated_object_release_pins,
        lifecycle_purpose_route_derivation, proof_guest, release_aware_verifier,
        epoch_composition, atomic_publisher,
  N = stale_profile_occurrence, wrong_writer_epoch, foreign_registry,
      unknown_route, wrong_command_variant, counterfeit_occurrence_id,
  Delta = ordinary_authorized_action_data cannot gain active_profile structural
          binding unless every implemented guard agrees
>
```

Strongest evidence class: `contract`.

The promoted claim is limited to the Rust construction boundary and exact
codec. No machine-checked theorem or runtime mount exists for this slice.

## Functional-core preflight

Artifact and authority:

- The new Rust file owns canonical occurrence structure, identity, decode, and
  active-profile structural binding.
- It does not own command authentication, economic effects, release activation,
  proof verification, or commit.
- The implementation is pure and `no_std`; it performs no I/O or mutation.

Construction and ownership:

- `EconomicCommandOccurrenceContentV1::new` consumes one owned
  `AuthorizedEconomicActionV1`.
- Subject, grant, nonce, pre-state, effects, and consumed objects have one owner
  in the nested action. No parallel occurrence fields can drift from them.
- The ordinary occurrence is cloneable protocol data.
- The profile-bound witness borrows the exact occurrence, checked active
  profile, and governed route; has private fields; is not `Clone`, `Copy`,
  `Serialize`, or `Deserialize`; and can only be returned by the binder. A
  witness cannot outlive the active-profile borrow used to construct it.

API and consumers:

- The change is additive. Existing action, nullifier, route, and profile hashes
  are unchanged.
- No current proof guest, verifier, settlement certificate, or publisher
  consumes the witness. Mounting remains a separate versioned change.

Semantics:

- Position is a total lexicographic key over `u64 x u32 x u32`.
- Zero coordinate values are valid. Integer maxima are valid.
- Consumed-object sorting, duplicate rejection, action validity, authorization
  identity, and grant-spend identity remain governed by
  `AuthorizedEconomicActionV1` and `EconomicActionRecordV1`.
- Binding rejection returns no alternate route, witness, effects, or state.

Encoding and proof binding:

- Postcard is bounded to 16,384 bytes.
- Decode requires complete consumption and exact canonical re-encoding.
- Serde map decoding rejects unknown fields.
- The profile-bound witness has no wire representation.
- The active-profile borrow participates in the witness lifetime; consumers
  cannot retain the witness after a lock-scoped profile borrow expires.

Commit and failure model:

- This contract has no commit point, replay store, outbox, or crash protocol.
- A future verifier must rebuild the structural witness against the current
  profile under the consensus/write lock before constructing stronger proof or
  publication authority.

Performance:

- Occurrence construction and identity are linear in the already-bounded
  authorized action encoding and consumed-object set.
- Governed route lookup is linear over at most 256 route releases. A future
  index may optimize lookup if it preserves the exact canonical registry and
  produces identical results.

Change separation:

- The existing economic-action ABI remains byte- and hash-stable.
- No lifecycle, effect, rounding, fee, migration, or publication behavior
  changes.

## Canonical identity

The occurrence ID is SHA-256 over this exact preimage:

```text
u16_be(len("zenodex.global_settlement.economic_command_occurrence_id.v1"))
|| "zenodex.global_settlement.economic_command_occurrence_id.v1"
|| u16_be(occurrence_version = 1)
|| u64_be(height)
|| u32_be(tx_index)
|| u32_be(op_index)
|| profile_id[32]
|| u64_be(writer_epoch)
|| route_release_id[32]
|| authorized_action_canonical_hash[32]
```

The authorized-action hash transitively binds application, chain/domain,
action type, subject, scope, nonce, validity, pre-state, semantic hash, effect
commitment, canonical consumed objects, grant, action-bound authorization
binding, and single-use grant-spend identity.

Pinned fixture vectors:

```text
occurrence_id = f15c1069c230bd6f31e298f581ab805176b4aeed8c3a53b318bcd212dd254f90
sha256(canonical_postcard_bytes) = 846358480fa068b6b865b5c0abe700f1227b62033865099f269297f7e36d5296
```

## Active-profile binding and rejection precedence

The binder checks, in order:

1. occurrence self-consistency and content-derived ID;
2. exact active profile ID;
3. exact active writer epoch;
4. exact route-registry root committed by the profile;
5. exact route-release membership in that registry;
6. equality between the route command-variant root and action type ID.

Only full success constructs `ProfileBoundEconomicCommandOccurrenceV1`.

This order makes stale-profile rejection deterministic and prevents a foreign
registry from being queried as if it were governed by the profile.

## Test design

The Rust suite follows explicit Arrange, Act, Assert phases and covers:

- independent occurrence-ID preimage reconstruction;
- fixed occurrence and canonical-byte vectors;
- field-separation mutation across position, profile, writer epoch, route, and
  nested action;
- BVA at coordinate zero and integer maxima;
- exact lexicographic position order;
- inherited canonical consumed-object ordering;
- active-profile acceptance;
- stale profile, wrong writer epoch, foreign registry, unknown route, and wrong
  command variant rejection;
- empty, trailing, and maximum-plus-one byte boundaries;
- wrong version, counterfeit ID, and unknown-field rejection;
- compile-fail checks that direct witness construction and serialization are
  unavailable.

The outcome partition is SETBVE-informed: every implemented binder outcome has
at least one representative, while closely related structural failures share
the smallest witness that distinguishes their rejection class.

## Negative knowledge and nonclaims

- Membership in a profile-bound route registry alone does not prove that the
  route was derived from authenticated creating-release pins. The later global
  state binder performs that derivation and rejects a proposed-route mismatch.
- `ActiveNew` versus `DrainOnly` lifecycle-purpose selection is not established
  by occurrence construction. It requires authenticated global-state object
  metadata and the governed resolver described in
  `ZRPF_LIFECYCLE_ROUTE_RESOLVER_V1_SPEC_20260806.md`.
- `AuthorizedEconomicActionV1` is canonical authorization data. This slice does
  not verify a signature, grant issuance, or durable nullifier uniqueness.
- The profile-bound witness is structural contract evidence. It is not a RISC0
  receipt, verified lane transition, route-composition proof, verified epoch,
  or settlement capability.
- No Python, Tau, Lean, Kani, SMT, guest, verifier, database, API, UI, migration,
  or publisher refinement is added here.
- No production-readiness, RC, whole-economy proof, or formal-verification claim
  is promoted.

## Next proof-worthy gap

Define a state-authenticated object-release-pin view and a closed command
lifecycle-purpose type. The governed resolver must derive one
`RouteSelectionKeyV1` from the command plus those pins, then prove that no caller
can select a different coexist-and-drain route. Only that resolver should feed
the occurrence constructor used by module and route proof journals.
