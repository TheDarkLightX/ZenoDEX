# FCIS M5-P4B5A B1B committed-configuration authority Revision 3.1

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_3_1`

**Supersedes:** Revision 3 at
`798f4ba862ff07cf1f92b54946c67e13e7a939b6`

**Review disposition:** `REVISE_BEFORE_B1B1`

**Research Kernel run:**
`zenodex-fcis-m5-p4b5a-config-authority-20260728`

**Accepted Revision 3 counterexamples:**
`result_b1b_rev3_provenance_loss_counterexamples_v1`

**Replacement hypothesis:**
`hypothesis_b1b_rev31_source_bound_authority_v1`

**Authority mount:** prohibited

## 1. Result

Revision 3 established the correct deployment bootstrap concept, deterministic
initial values, compact committed header, and separation between state binding
and current publication. Three source-provenance relations remained incomplete:

1. `VerifiedV1ToV2MigrationAuthorityV2` retained a manifest and its recomputed
   root after the independently pinned anchor had left the relation.
2. `StateBoundFeeDistributionConfigurationV2` retained a root, header, and
   configuration claim after the exact state that authenticated the header had
   left the relation.
3. The configuration-update law did not have an exhaustive complementary law
   requiring every ordinary successor header to preserve deployment identity
   and configuration root.

Coordinated hostile mutation can replace all mutually checking fields in the
first two aggregates. An ordinary transition can consistently construct a
successor containing a substituted configuration root in the third case. These
attacks require no hash collision.

Revision 3.1 closes the three gaps by carrying the independent source into
every authority use:

```text
pinned deployment verifier
  + untrusted manifest
  + exact current V1 state
  + validated initial configuration claim
    -> one freshly derived migration candidate

exact V2 pre-state
  + compact state-bound configuration
    -> fresh exact rebinding equality

authority-header transition
    = MigrationHeader
    | OrdinaryAdvance
    | ConfigurationUpdate
```

B1B-1 remains smaller than these later relations. It may implement only
untrusted canonical carriers, schemas, codecs, roots, and shared vectors. It
may not construct migration authority, committed V2 state, a state-bound
configuration, a migration successor, a receipt, a bundle, a proof input, or a
mounted value.

## 2. Preflight and authority record

### Artifact and claim level

This document is a review-only design correction. It changes no runtime,
accepted language, state root, migration, settlement, proof, datastore, or
mount. B1A at
`9fd7dd78ff410c72e9f40de7055da596f392a1d6` remains an unmounted
self-consistency validator carrying no protocol authority.

The proposed authority facts are:

```text
deployment bootstrap provenance
manifest identity
exact V1 source state
exact V2 source state
configuration identity
authority-header transition cause
publication currentness
```

Each fact has one declared source. No aggregate may recover a missing source by
checking only its own fields.

### Ownership and hostile-mutation model

Canonical carrier values use exact owned immutable fields. Python
`frozen=True`, slots, private constructors, and module allowlists remain
misuse barriers. They are not security proofs against hostile same-process
mutation.

Every authority derivation therefore recomputes from its independent source:

```text
migration use       -> independently pinned verifier + exact current V1 state
state-bound use     -> exact V2 pre-state
ordinary successor -> exact pre-header + closed transition cause
publication         -> exact store-current state inside the atomic operation
```

Arbitrary replacement of verifier code, the release-pinned verifier profile,
or the datastore implementation remains outside this data-mutation model and
is an explicit trusted-computing-base assumption.

### Canonical and cross-language boundary

All public carriers have closed field registries, exact types, full-consumption
decoding, unknown-field rejection, canonical JSON envelopes, domain-separated
roots, and byte-identical Python/Rust golden vectors. Public decoding never
constructs a pinned verifier, migration authority, state-bound authority, or
current-state authority.

## 3. Exact committed authority header

The selected header remains:

```text
FCISAuthorityHeaderV2(
    chain_deployment_id: ExactText,
    sequence: ExactU256,
    fee_distribution_configuration_root: Digest32,
)
```

It is part of canonical snapshot-v5 bytes and the V2 state root.

`fee_distribution_configuration_version` remains absent from the header. The
configuration root commits the complete body, including its version. Any
consumer derives the version from the exact nested body after recomputing the
root.

`FCISAuthorityHeaderV2` is exact data. A decoded or directly constructed header
has no current-state authority. Authority arises only when the header is inside
an admitted exact state whose root is authenticated by the applicable source
relation.

## 4. Public bootstrap and migration carriers

### Bootstrap-anchor claim

The public canonical carrier is explicitly untrusted:

```text
DeploymentBootstrapAnchorClaimV2(
    chain_deployment_id: ExactText,
    expected_migration_manifest_root: Digest32,
)
```

Its schema is:

```text
zenodex/fcis/deployment/bootstrap-anchor-claim/v2
```

Its optional audit root is:

```text
bootstrap_anchor_claim_root =
  sha256(
    domain_sep("fcis_deployment_bootstrap_anchor_claim", version=2)
    || canonical_bootstrap_anchor_claim_envelope_v2
  )
```

Decoding this claim supplies data for comparison. It cannot create a pinned
verifier.

### Migration manifest

The public canonical manifest carrier is:

```text
V1ToV2MigrationManifestV2(
    chain_deployment_id: ExactText,
    expected_v1_pre_root: Digest32,
    fee_distribution_domain_id: ExactText,
    expected_initial_configuration_root: Digest32,
    initial_sequence: ExactU256,
    initial_configuration_version: ExactU256Positive,
    initial_activation_sequence: ExactU256,
    source_snapshot_version: ExactU256,
    target_snapshot_version: ExactU256,
)
```

Its schema and root remain:

```text
schema =
  zenodex/fcis/migration/v1-to-v2-manifest/v2

migration_manifest_root =
  sha256(
    domain_sep("fcis_v1_to_v2_migration_manifest", version=2)
    || canonical_migration_manifest_envelope_v2
  )
```

The manifest is untrusted until the point-of-use verifier comparison succeeds.
No decoded manifest or manifest projection is migration authority.

## 5. Independently pinned deployment verifier

`PinnedDeploymentBootstrapVerifierV2` is a trusted verifier capability
established before transaction processing. It is not a canonical transaction
value and has no public decoder.

The pinning mechanism must be frozen in B1B-2 before implementation of migration
authority. Acceptable sources include an immutable genesis profile compiled
into the deployment verifier or a release-pinned migration profile whose exact
bytes and digest are part of release evidence. The selected mechanism must make
the following sources impossible:

```text
transaction or API input
the bootstrap-anchor claim being checked
the migration manifest being checked
candidate V1 or V2 state
configuration content storage
environment variables read during evaluation
mutable files read during evaluation
caller-selected resolver or registry
```

The capability provides the independently fixed pair:

```text
expected chain_deployment_id
expected migration_manifest_root
```

If the deployment has no independently pinned verifier, V2 migration is
unavailable.

Political, legal, and governance authorization for choosing the pin remain
external assumptions. B1B-2 must make the technical pinning interface
mechanical and source-pinned.

## 6. Source-bound migration relation

There is no durable
`VerifiedV1ToV2MigrationAuthorityV2` authority object in Revision 3.1.

The pure derivation is one operation:

```text
verify_and_derive_v1_to_v2_migration_v2(
    pinned_verifier: PinnedDeploymentBootstrapVerifierV2,
    manifest_claim: V1ToV2MigrationManifestV2,
    exact_v1_pre_state: FCISCommittedStateV1,
    initial_configuration_claim:
      ValidatedFeeDistributionConfigurationClaimV2,
)
  -> MigrationRejectV2
   | V1ToV2MigrationCandidateV2
```

The operation checks, in stable rejection order:

```text
1. exact types and recursive ownership of all data inputs
2. canonical manifest re-encoding and manifest-root recomputation
3. manifest root = pinned verifier expected manifest root
4. manifest deployment ID = pinned verifier deployment ID
5. exact V1 snapshot-v4 bytes and pre-root recomputation
6. V1 pre-root = manifest expected V1 pre-root
7. V1 scalar fee dust = 0
8. source snapshot version = 4
9. target snapshot version = 5
10. initial sequence = 0
11. initial configuration version = 1
12. initial activation sequence = 0
13. exact initial configuration claim and policy revalidation
14. configuration root = manifest initial configuration root
15. configuration deployment ID = manifest deployment ID
16. configuration domain ID = manifest domain ID
17. configuration version = 1
18. configuration activation sequence = 0
19. exact successor projection and snapshot-v5 root recomputation
```

The returned candidate owns the exact V1 pre-state, manifest claim, initial
configuration claim, successor, and recomputed roots as one lineage. It is
still a candidate. It does not make the V1 state current.

At publication, the store operation loads its exact current V1 state inside the
atomic transaction and reruns the same derivation with the independently pinned
verifier. Publication requires exact equality between the fresh result and the
bundle candidate plus:

```text
store current V1 root = candidate expected V1 pre-root
```

A bundle-carried copy of the V1 state cannot substitute for the store-current
state at this check.

This construction defeats coordinated manifest and root replacement because
the independently pinned expected manifest root remains an input at every
migration-authority use.

## 7. Exact V1-to-V2 namespace projection

The deterministic successor relation contains these explicit equalities:

```text
v2.authority_header.chain_deployment_id =
  manifest.chain_deployment_id
v2.authority_header.sequence = 0
v2.authority_header.fee_distribution_configuration_root =
  manifest.expected_initial_configuration_root

v2.balances = v1.balances
v2.pools = v1.pools
v2.lp_balances = v1.lp_balances
v2.nonces = v1.nonces
v2.vault = v1.vault
v2.oracle = v1.oracle
v2.perps = v1.perps

v1.fee_accumulator.dust = 0
v2.fee_apportionment = canonical_empty_fee_apportionment_v2
```

The V1 `fee_accumulator` field is absent from V2. The V2
`fee_apportionment` field is absent from V1. A state carrying both rejects.

No phrase such as `exact migration projections` can hide a conversion. If any
retained namespace changes type, schema, canonical bytes, or semantic meaning
between snapshots 4 and 5, that namespace requires a separately named
conversion relation, independent vectors, and review before migration can be
implemented.

Second migration and V2-to-V1 downgrade remain absent from the normal command
registry and must fail structural mutation tests.

## 8. Exact-state rebinding for state-bound configuration

The compact binder remains:

```text
bind_fee_configuration_to_state_v2(
    exact_pre_state: FCISCommittedStateV2,
    validated_configuration_claim:
      ValidatedFeeDistributionConfigurationClaimV2,
)
  -> StateBindingRejectV2
   | StateBoundFeeDistributionConfigurationV2(
         pre_state_root,
         authority_header,
         validated_configuration_claim,
     )
```

The binder revalidates the complete exact pre-state and nested claim, recomputes
the snapshot-v5 root and configuration root, compares deployment and
configuration roots, checks activation, and constructs one newly owned
aggregate.

Self-revalidation of the resulting wrapper is insufficient. Every consumer
must receive the exact pre-state and require:

```text
rebind_state_bound_configuration_v2(
    exact_pre_state,
    supplied_state_bound_configuration,
) =
    bind_fee_configuration_to_state_v2(
        exact_pre_state,
        supplied_state_bound_configuration.validated_configuration_claim,
    )
    == supplied_state_bound_configuration
```

Exact equality covers the complete typed aggregate and its canonical bytes.

This relation is mandatory at:

```text
fee evaluation
decision derivation
commit-bundle construction
proof-input construction
commit-time publication verification
```

The evaluation, decision, bundle, and proof lineages retain the exact admitted
pre-state. Commit-time publication uses the store's exact current state inside
the atomic operation and never relies solely on a bundle-carried state copy.

This construction defeats coordinated header and claim replacement while
retaining the legitimate pre-state root. Fresh binding reads the actual header
from the exact state committed by that root.

`StateBoundFeeDistributionConfigurationV2` continues to mean:

> This exact configuration is committed by this exact state.

Currentness remains solely a successful store-current-root comparison during
atomic publication.

## 9. Exhaustive authority-header transition algebra

All authoritative header changes belong to one closed transition sum:

```text
AuthorityHeaderTransitionV2 =
    MigrationHeaderV2
  | OrdinaryAdvanceV2
  | ConfigurationUpdateV2
```

In this section, `pre` and `next` denote exact `FCISAuthorityHeaderV2`
values.

The only controlled derivation functions are:

```text
initial_header_from_source_bound_migration_v2
advance_ordinary_header_v2
update_configuration_header_v2
```

No generic authority-header state write, patch atom, public authority
constructor, subclass hook, or open transition registry exists.

### Migration

Migration constructs:

```text
next.chain_deployment_id = point-of-use verified manifest deployment ID
next.sequence = 0
next.fee_distribution_configuration_root =
  point-of-use verified manifest initial configuration root
```

The source-bound relation in section 6 owns this constructor.

### Ordinary accept and committed failure

For both ordinary accept and typed committed failure:

```text
require pre.sequence < U256_MAX
next.chain_deployment_id = pre.chain_deployment_id
next.sequence = pre.sequence + 1
next.fee_distribution_configuration_root =
  pre.fee_distribution_configuration_root
```

Ordinary transitions cannot change deployment identity or configuration root.

### Configuration update

For a configuration-only update:

```text
require pre.sequence < U256_MAX
require active.configuration_version < U256_MAX

next.chain_deployment_id = pre.chain_deployment_id
next.sequence = pre.sequence + 1
next.fee_distribution_configuration_root =
  recomputed_root(new_configuration)

new.configuration_version =
  active.configuration_version + 1
new.activation_sequence = next.sequence
new.chain_deployment_id = pre.chain_deployment_id
new.fee_distribution_domain_id =
  active.fee_distribution_domain_id
```

The update cannot contain or compose with fee-bearing settlement. Balances,
pools, LP balances, nonces, vault, oracle, fee-apportionment deficits, and
perps remain unchanged. The new configuration first applies to a later
transition whose pre-state sequence equals the update successor sequence.

Ordinary weight, destination, and policy rotation is permitted. Stable domain
identity and exact deficit state are preserved.

Domain creation, domain-ID rotation, split, merge, retirement, and reuse remain
absent from the initial V2 language.

### Ordinary rejection

Ordinary rejection carries no successor, header change, patch, effect, receipt
authority, replay update, or outbox authority.

### Overflow precedence

After closed admission and recursive exact-value revalidation:

```text
1. SEQUENCE_EXHAUSTED
2. CURRENT_CONFIGURATION_BINDING_FAILED
3. CONFIGURATION_VERSION_EXHAUSTED
4. NEW_CONFIGURATION_BINDING_FAILED
5. CONFIGURATION_UPDATE_LAW_FAILED
```

If sequence and configuration version are both exhausted,
`SEQUENCE_EXHAUSTED` wins. Python and Rust use checked U256 arithmetic with no
wraparound or reset.

## 10. Content availability and replay

The committed header is the active content pointer. Configuration bodies,
anchor claims, manifests, archives, files, registries, and peers supply
untrusted bytes.

Only a support profile declaring a configuration read requires the active body.
Missing content returns `MISSING_FEE_CONFIGURATION_CONTENT` and produces no
successor authority. Unrelated V2 transitions do not acquire a hidden
configuration read.

Every published bundle that consumed a configuration carries the exact
canonical validated-claim bytes in its nested lineage. A configuration update
bundle carries both the active configuration claim and proposed configuration
claim because its transition reads both.

## 11. B1B-1 exact scope

B1B-1 may implement only:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2

their exact field registries
their exact schemas
their canonical Python and Rust codecs
their canonical claim or manifest roots
shared positive and negative golden vectors
structural checker coverage for this limited scope
```

B1B-1 must not implement or export:

```text
PinnedDeploymentBootstrapVerifierV2
VerifiedV1ToV2MigrationAuthorityV2
V1ToV2MigrationCandidateV2
FCISCommittedStateV2
StateBoundFeeDistributionConfigurationV2
a migration successor
a configuration update transition
a receipt
a commit bundle
a proof input
a runtime mount
```

The header carrier is not a generic state-write capability. The anchor claim
and manifest are not verified authority.

Required B1B-1 vectors include:

```text
exact anchor-claim bytes and optional audit root
exact authority-header bytes
exact manifest bytes and root
wrong, missing, duplicate, and unknown fields
Boolean in every U256 field
negative U256 and U256 + 1
zero, one, U256_MAX - 1, and U256_MAX
empty and over-bound identifiers
Unicode scalar identifiers
surrogate rejection
uppercase and malformed digests
source snapshot version other than 4
target snapshot version other than 5
initial sequence other than 0
initial configuration version other than 1
initial activation sequence other than 0
manifest deployment substitution
manifest V1-root substitution
manifest domain substitution
manifest initial-configuration-root substitution
Python/Rust byte and root equality
```

Admission may accept a structurally exact manifest carrying a semantically
wrong fixed constant if schema admission owns only type and range. The later
migration core must reject that value for the named semantic reason. Golden
vectors must distinguish admission validity from migration authority.

## 12. Required later counterexamples and mutants

The following negative witnesses are permanent:

```text
verified manifest and manifest root changed together
verified deployment and manifest root changed together
migration use without the pinned verifier
pinned verifier selected from decoded anchor bytes

state-bound header root and claim changed together
state-bound deployment, header, and claim changed together
pre-state root retained while nested header is replaced
state-bound use without exact-pre-state rebinding
commit rebind against bundle-carried state instead of store-current state

ordinary accept changes configuration root
committed failure changes configuration root
ordinary transition changes deployment ID
generic authority-header patch or constructor added

configuration update also settles fees
configuration update resets deficit state
configuration update skips configuration version
configuration update activates at N instead of N + 1

migration omits or transforms balances
migration omits or transforms pools
migration omits or transforms LP balances
migration omits or transforms nonces
migration omits or transforms vault
migration omits or transforms oracle
migration omits or transforms perps
migration admits nonzero legacy dust
migration retains both fee namespaces

B1B-1 exports a pinned verifier, verified authority, state-bound value,
committed V2 state, successor, receipt, bundle, proof input, or mount
```

Each mutant must fail for the intended named invariant. A stale outer artifact
hash does not count as killing a semantic mutant; mutation tests must recompute
all unrelated outer hashes so the targeted semantic check is reached.

## 13. Pattern and boundary record

**Chosen pattern:** untrusted canonical carriers; point-of-use deployment-pinned
migration derivation; compact state-bound value with exact-state rebinding;
closed authority-header transition algebra; one commit-time store-current CAS.

**Rejected alternatives:**

- durable verified migration authority without the pinned verifier at use;
- state-bound self-revalidation without the exact pre-state;
- generic authority-header patching;
- full configuration body duplicated in every state;
- mutable external active-configuration pointer;
- stable shell-created current-authority value;
- loose copied lineage fields.

**Mechanical guarantees after implementation and evidence:**

- coordinated carrier mutation cannot recreate missing deployment provenance;
- coordinated header/claim mutation cannot retain binding to an unrelated root;
- ordinary transitions preserve deployment and active configuration identity;
- migration copies every retained economic namespace under an explicit law;
- configuration and economic races remain visible under one current-root CAS.

**Explicit non-guarantees:**

- political, legal, or governance authorization of the bootstrap pin;
- secure release distribution of the pinned verifier;
- security after arbitrary verifier-code replacement;
- production datastore linearizability or crash recovery;
- external content-cache availability;
- mounted migration, settlement, proof, or publication behavior;
- governance authorization of later configuration updates;
- SHA-256 collision or preimage resistance beyond the cryptographic assumption.

## 14. Checkpoint sequence

```text
B1B-0R31  focused independent review of Revision 3.1
B1B-1     untrusted header, bootstrap-anchor-claim, and migration-manifest
           values; schemas; canonical Python/Rust codecs; shared vectors
B1B-2     mechanically pinned verifier interface and source-bound
           deterministic V1-to-V2 migration reference transition
B1B-3     committed V2 state, snapshot-v5 root, exact namespace migration,
           closed authority-header transition algebra, and state admission
B1B-4     controlled state-bound derivation and exact-pre-state rebinding
B1B-5     candidate, receipt, patch, proof-input, and bundle lineage
B1B-6     reference commit current-state rebinding, race, sequence, retry,
           replay, and hostile-mutation evidence
```

Every checkpoint remains unmounted. Production migration, shell, datastore,
proof-verifier, and runtime authority require separate promotion gates.

## 15. Promotion rule

Revision 3.1 remains a testable hypothesis until a focused independent review
attempts every counterexample in sections 6, 8, 9, and 12.

B1B-1 may begin only after the review returns exactly:

```text
APPROVE_B1B1_REVISION_3_1_UNMOUNTED
```

Any migration-authority use without the independently pinned verifier, any
state-bound use without the exact pre-state, any generic authority-header write,
any unspecified migration namespace, or any B1B-1 authority object is a
`NO_GO`.
