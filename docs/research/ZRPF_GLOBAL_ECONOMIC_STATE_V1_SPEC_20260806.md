# ZRPF GlobalEconomicStateV1 Contract

Status: implemented and tested structural contract; research-only, unmounted,
and without proof-verification or settlement authority.

Date: 2026-08-06

## Purpose

The whole-economy profile, release, route, and occurrence contracts identify
the governed interpretation of a command. They previously lacked one canonical
state commitment containing every stable economic lane and the common
cross-lane partitions needed by future proofs and publication checks.

`GlobalEconomicStateV1` closes that structural gap. It commits:

- application and chain/domain identity;
- height and writer epoch;
- the exact `EconomicProfileIdV1`;
- exactly twelve canonically ordered lane-state roots;
- named roots for balances, supplies, custody, liabilities, reserves, Oracle
  occurrences, replay state, terminal obligations, release observations,
  history, external outbox, and persistent-object release pins.

`EconomicObjectReleasePinV1` commits each persistent object's stable lane and
creating module release. A 256-level sparse-Merkle opening authenticates that
pin against the state snapshot. Constructor-private binding witnesses exist
only after state/profile/registry relations and consumed-object openings pass.

## ShapeForge model

```text
Phi := <
  M = zenodex_global_economic_state_v1,
  S = profile_state_occurrence_object_release_binding,
  A = guard,
  T = contract_strengthening,
  V = application_id, chain_or_domain_id, height, writer_epoch, profile_id,
      twelve_lane_roots, twelve_partition_roots, object_release_pins,
  O = derive_state_root, open_object_pin, bind_state_to_profile,
      bind_occurrence_to_state,
  G = canonical_lane_order, exact_profile_and_writer_epoch,
      exact_registry_roots, exact_application_domain_and_pre_state,
      exact_consumed_object_order, existing_release_admission,
  Obs = state_root, registry_bound_state, state_bound_occurrence,
  K = (application_id, chain_or_domain_id, height, writer_epoch, profile_id),
  E = fixed_preimages, fixed_codec_vectors, AAA_negative_tests,
      BVA_and_BVE_boundaries, compile_fail_architecture_tests,
  Gap = lifecycle_purpose_route_derivation, global_effect_plan,
        conservation_checker, module_and_composition_guests,
        release_aware_epoch_verifier, atomic_publisher,
  N = omitted_or_reordered_lane, omitted_partition, stale_profile,
      foreign_registry, wrong_application_or_domain, stale_pre_state,
      missing_extra_or_reordered_pin, counterfeit_pin_root,
      unknown_or_inadmissible_creating_release,
  Delta = ordinary_state_and_occurrence_data cannot gain structural
          state_binding unless every implemented guard agrees
>
```

Strongest evidence class: `contract`.

The promoted claim is limited to deterministic Rust construction, exact
encoding, content-derived commitments, and constructor-private structural
binding. No machine-checked theorem or mounted runtime consumer exists for this
slice.

## Correct-by-construction boundary

The implementation uses a functional core:

```text
validated ordinary values -> canonical state or typed reject
canonical state + exact registries -> private structural witness or typed reject
profile-bound occurrence + state-bound pins -> private structural witness or typed reject
```

Construction prevents these invalid states:

- a state with fewer or more than twelve lane roots;
- duplicate or noncanonically ordered lanes;
- an all-zero state root;
- a state whose root differs from its content;
- an object pin with an unknown version;
- a bound state whose profile, writer epoch, or registry roots drift;
- a bound occurrence whose application, domain, pre-state, consumed-object
  order, pin membership, creating release, or release lifecycle drifts.

The ordinary state and pin values remain protocol data. The private witnesses
are non-serializable and caller construction is unavailable. Neither type
contains receipt, consensus-head, database, or publication authority.

## Canonical state identity

The state root is SHA-256 over this exact preimage:

```text
u16_be(len("zenodex.global_settlement.global_economic_state_root.v1"))
|| "zenodex.global_settlement.global_economic_state_root.v1"
|| u16_be(state_version = 1)
|| application_id[32]
|| chain_or_domain_id[32]
|| u64_be(height)
|| u64_be(writer_epoch)
|| profile_id[32]
|| u8(lane_count = 12)
|| for each EconomicLaneIdV1::ALL lane in order:
     u8(lane_code) || lane_state_root[32]
|| balances_root[32]
|| supplies_root[32]
|| custody_root[32]
|| liabilities_root[32]
|| reserves_root[32]
|| oracle_occurrences_root[32]
|| replay_state_root[32]
|| terminal_obligations_root[32]
|| release_observations_root[32]
|| history_root[32]
|| external_outbox_root[32]
|| object_release_registry_root[32]
```

The closed lane order is:

```text
ASSET_TRANSFER, SPOT_LIQUIDITY, FARM_INCENTIVES, ZDEX_TOKENOMICS,
ZUSD_MONETARY, PERPS_MARKET, ORACLE_MARKET, SEALED_AUCTION,
STRATEGY_ESCROW, PROOF_REWARDS, EXTERNAL_CUSTODY, GOVERNANCE_MIGRATION
```

Pinned fixture vectors:

```text
state_root = f4b248f7b2e62dbd9b406f8e56ee15486f297732fc8954462066e33662c3b751
sha256(canonical_state_postcard) = da1d4137e917ede9b0b4d06662a60908441a966040313722996cf1b2ebf6a061
```

Each lane and partition position has an identity-separation regression. This
detects an omitted, duplicated, or reordered field in the root preimage.

## Persistent-object creating-release pin

The sparse-registry value hash is SHA-256 over:

```text
u16_be(len("zenodex.global_settlement.economic_object_release_pin_value.v1"))
|| "zenodex.global_settlement.economic_object_release_pin_value.v1"
|| u16_be(pin_version = 1)
|| object_id[32]
|| u8(lane_code)
|| creating_release_id[32]
```

Pinned fixture vectors:

```text
pin_value_hash = 965a9f7bcd593a1cbed6ea6b5afec4aea92c672b8b166bdc4b6333822b9e739b
sha256(canonical_pin_proof_postcard) = 38e5343b0f44c2e78069da41487e7125408f68015262c36e8363d29cbe9bb65e
```

The proof uses the existing fixed-depth, MSB-first sparse-Merkle contract. The
object ID is both the registry key and a committed field inside the value hash.
The state binder requires one opening per canonical consumed object in the same
order. Missing, extra, substituted, and wrong-root openings reject.

## Binding order and typed outcomes

State/profile binding checks, in order:

1. state self-consistency and content-derived root;
2. exact profile ID;
3. exact writer epoch;
4. the profile's exact lane, module-release, and route registries.

Occurrence/state binding then checks:

1. occurrence profile and writer epoch equal the state;
2. application and chain/domain equal the state;
3. action pre-state equals the content-derived state root;
4. pin-proof count equals consumed-object count;
5. each pin object ID equals the corresponding consumed object;
6. each sparse opening derives the committed object-release registry root;
7. each creating release exists in the pin's exact lane registry;
8. each creating release admits an existing-object transition, meaning
   `ACTIVE_NEW` or `DRAIN_ONLY`.

Only complete success constructs `StateBoundEconomicCommandOccurrenceV1`.
Rejection produces no witness, route substitution, effect plan, state change,
or publication capability.

## Encoding and resource bounds

- Canonical state Postcard input is bounded to 2,048 bytes.
- Canonical object-pin proof input is bounded to 8,512 bytes.
- The lane-vector decoder rejects a declared or observed thirteenth element
  before extending its bounded allocation.
- Decode requires complete consumption and byte-for-byte canonical re-encoding.
- Empty, one-byte malformed, oversized, trailing, nonminimal integer,
  wrong-version, counterfeit-root, and unknown-field inputs reject.
- State and pin construction are deterministic and perform no I/O.
- Pin verification currently carries one 256-sibling path per consumed object.
  Multiproof compression requires a separate versioned ABI.

## Test design

The Rust suite uses explicit Arrange, Act, Assert phases and covers:

- BVA at 11, 12, and 13 lanes and at height/writer values 0, 1, and `u64::MAX`;
- manual independent reconstruction of state-root and pin-value preimages;
- fixed canonical-byte digests;
- identity separation for every lane and every named partition root;
- profile, writer, registry, application, domain, and pre-state drift;
- zero, missing, extra, substituted, wrong-root, unknown-release, and
  lifecycle-disallowed object pins;
- exact malformed-input and nested unknown-field rejection;
- compile-fail checks for direct witness construction and serialization.

The binding outcome partition is SETBVE-informed: each typed accept/reject
class has a minimal distinguishing representative. The tests also target likely
mutations such as deleting a committed root, skipping one equality, accepting a
thirteenth lane, or allowing a shadow release.

## Negative knowledge and nonclaims

- A committed root does not prove that balances, custody, liabilities,
  reserves, terminal obligations, or outbox contents satisfy their economic
  invariants. Future transition guests and the common invariant checker must
  establish those relations.
- A valid object pin authenticates creating-release metadata against this
  snapshot. It does not prove that the command's governed route depends on that
  lane/release set or distinguish new-object creation from drain activity.
- The route already present in `EconomicCommandOccurrenceV1` remains checked
  only by the active-profile occurrence binder. A state-derived
  lifecycle-purpose resolver is still required.
- Zero consumed objects and zero pin proofs are structurally valid. Command
  semantics must decide whether a specific operation requires objects.
- The state root is a proof public input candidate. It is not itself a proof.
- No conservation theorem, Rust/Python refinement proof, Tau policy, Lean/Kani
  theorem, RISC0 guest, receipt verifier, epoch recursion, migration, current
  head check, durable nullifier store, atomic commit, or outbox delivery is
  implemented here.
- No production-readiness, RC, whole-economy settlement, or formal-verification
  claim is promoted.

## Next proof-worthy gap

Define a closed lifecycle-purpose type and a deterministic resolver that takes
the typed command plus state-authenticated creating-release pins and derives
exactly one `RouteSelectionKeyV1`. The resolver must reject caller-selected
coexist-and-drain routes. Its accepted output can then feed the canonical
global effect plan and conservation kernel.

After that contract stabilizes, an exact integer nullspace experiment can test
whether conservation rows `A * delta = b` admit a smaller basis
`delta = delta_0 + N * z`. Fourier or Walsh analysis remains a research aid for
discovering redundant Boolean policy dimensions and adversarial test
interactions; it carries no settlement or promotion authority.
