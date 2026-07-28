# FCIS M5-P4B5A B1B committed-configuration authority Revision 3

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_3`

**Supersedes:** Revision 2 at
`14f5cb535250858cc1cf0ce00b8f6f6ebcd6e2d7`

**Review disposition:** `REVISE_BEFORE_B1B1`

**Research Kernel run:**
`zenodex-fcis-m5-p4b5a-config-authority-20260728`

**Counterexample:**
`result_b1b_rev2_bootstrap_counterexample_v1`

**Replacement hypothesis:**
`hypothesis_b1b_rev3_authenticated_bootstrap_v1`

**Authority mount:** prohibited

## 1. Result

Revision 2 correctly placed the active configuration root and protocol sequence
inside the committed state root. It did not establish the deployment identity
of the first V2 state. A caller or faulty migration could construct a
self-consistent configuration, header, and state for deployment A while the
node was intended to operate deployment B. Every Revision 2 binding check would
pass because no independently trusted B value entered the relation.

The correction has three parts:

1. Commit the deployment identity in every V2 authority header.
2. Permit the first V2 header to arise only from a deterministic migration
   manifest checked against an independently pinned deployment bootstrap
   anchor.
3. Reserve current-state authority for the atomic store comparison. A pure
   state-bound value proves only that a configuration belongs to one exact
   state.

The full configuration body remains outside state. It is supplied as untrusted
content, revalidated, rehashed, and compared with the state header.

## 2. Exact committed authority header

The selected minimal header is:

```text
FCISAuthorityHeaderV2(
    chain_deployment_id: ExactText,
    sequence: ExactU256,
    fee_distribution_configuration_root: Digest32,
)
```

The V2 aggregate is:

```text
FCISCommittedStateV2(
    authority_header,
    balances,
    pools,
    lp_balances,
    nonces,
    vault,
    oracle,
    fee_apportionment,
    perps,
)
```

The header is part of canonical snapshot-v5 bytes and therefore the state root.
The deployment ID separates otherwise identical state histories. The sequence
separates successive committed states, including no-economic-change states.
The configuration root commits the complete active configuration body.

`fee_distribution_configuration_version` is removed from the header. It is
already inside the configuration body committed by
`fee_distribution_configuration_root`. State binding derives the version from
that exact body. This avoids a redundant independently swappable state field.

The V1 scalar `fee_accumulator` and V2 `fee_apportionment` namespaces remain
mutually exclusive.

## 3. Independent deployment bootstrap anchor

The first V2 state requires one external trust root:

```text
DeploymentBootstrapAnchorV2(
    chain_deployment_id: ExactText,
    expected_migration_manifest_root: Digest32,
)
```

This value is deployment-specific verifier configuration established before
transaction processing. It may come from an immutable genesis profile or a
release-pinned migration profile. It must not come from:

```text
transaction or API input
environment variables read during evaluation
mutable configuration files read during evaluation
configuration content storage
the candidate V1 or V2 state
the migration manifest being checked
```

The shell may retrieve anchor or manifest bytes. Decoding an anchor produces
only an untrusted anchor claim. Only a deployment bootstrap verifier
parameterized by the already-pinned anchor may construct:

```text
VerifiedV1ToV2MigrationAuthorityV2(
    manifest,
    manifest_root,
)
```

That controlled value is subject-bound evidence. Python module privacy and
Rust visibility support the boundary; the security premise is the independent
anchor comparison and point-of-use revalidation.

Selection and governance authorization of the bootstrap anchor remain an
explicit external assumption. If no independently pinned anchor exists, V2
migration is unavailable.

## 4. Deterministic V1-to-V2 migration manifest

The exact manifest is:

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

Its canonical root is:

```text
migration_manifest_root =
  sha256(
    domain_sep("fcis_v1_to_v2_migration_manifest", version=2)
    || canonical_migration_manifest_envelope_v2
  )
```

The bootstrap verifier requires:

```text
manifest_root = anchor.expected_migration_manifest_root
manifest.chain_deployment_id = anchor.chain_deployment_id
```

The migration core consumes:

```text
exact admitted V1 pre-state
VerifiedV1ToV2MigrationAuthorityV2
ValidatedFeeDistributionConfigurationClaimV2
```

and requires:

```text
recomputed_v1_pre_root = manifest.expected_v1_pre_root
V1 snapshot version = 4
V1 scalar fee dust = 0

manifest.source_snapshot_version = 4
manifest.target_snapshot_version = 5
manifest.initial_sequence = 0
manifest.initial_configuration_version = 1
manifest.initial_activation_sequence = 0

claim.body.chain_deployment_id = manifest.chain_deployment_id
claim.body.fee_distribution_domain_id =
  manifest.fee_distribution_domain_id
claim.body.configuration_version =
  manifest.initial_configuration_version
claim.body.activation_sequence =
  manifest.initial_activation_sequence
claim.configuration_root =
  manifest.expected_initial_configuration_root
```

The deterministic successor has:

```text
authority_header.chain_deployment_id =
  manifest.chain_deployment_id
authority_header.sequence = 0
authority_header.fee_distribution_configuration_root =
  manifest.expected_initial_configuration_root

fee_apportionment = canonical empty V2 state
all other economic namespaces = exact migration projections of V1 pre-state
```

The commit bundle carries the recomputed V1 pre-root as its expected root. The
atomic store operation decides whether that root is still current.

The state-version transition makes a second V1-to-V2 migration and a V2-to-V1
downgrade unrepresentable in the normal command registry. Structural and
mutation tests must also reject any added second-migration or downgrade route.

## 5. State binding is not currentness

The pure binding function does not accept a caller-declared expected root:

```text
bind_fee_configuration_to_state_v2(
    exact_pre_state,
    validated_configuration_claim,
)
  -> Reject(reason)
   | StateBoundFeeDistributionConfigurationV2(
         pre_state_root,
         authority_header,
         validated_configuration_claim,
     )
```

It performs:

1. exact-type and recursive pre-state revalidation;
2. snapshot-v5 byte and pre-state-root recomputation;
3. exact claim and nested policy revalidation;
4. policy-root and configuration-root recomputation;
5. equality between claim root and header configuration root;
6. equality between claim deployment ID and header deployment ID;
7. `claim.body.activation_sequence <= header.sequence`;
8. private construction of one newly owned state-bound aggregate.

The builder reconstructs the policy, body, and claim field by field from exact
immutable primitives. It uses no generic copy, deep copy, seal flag, mutable
base, or open admission type.

`StateBoundFeeDistributionConfigurationV2` means:

> This exact configuration is committed by this exact state.

It does not mean:

> This state is currently authoritative.

There is no durable `AuthenticatedFeeDistributionConfigurationV2` created by a
prior shell read. Currentness exists only inside the atomic operation:

```text
store.current_root = bundle.expected_pre_root
  -> publish the complete bundle
  | stale, publish nothing
```

A historical state can produce a valid state-bound value. Its bundle cannot
publish over a different current root.

A self-consistent foreign-deployment state can likewise produce a value bound
to that foreign state. The type does not relabel it as local. A deployment-
specific receipt, bundle, proof, or publication verifier must compare the
nested header deployment ID with its independently pinned expected deployment
ID, or verify a root descended from the deployment's authenticated migration.

## 6. Ownership and lineage

The state-bound aggregate retains one nested
`ValidatedFeeDistributionConfigurationClaimV2`. It does not copy the claim's
deployment ID, domain ID, policy root, version, activation sequence, algorithm,
accepted language, weights, or destinations into independently constructible
fields.

The candidate retains the state-bound aggregate as one lineage value. Receipts
and commit bundles retain the candidate or decision lineage. Reader-facing
projections may expose derived fields, but decoders never accept those
projections as independent authority.

Because hostile in-process code can bypass Python `frozen=True` with
`object.__setattr__`, every authority use recursively revalidates the aggregate
and recomputes its roots:

```text
state binding
fee evaluation
decision derivation
commit-bundle construction
commit-time publication verification
```

Any mutation produces a typed rejection before publication. Rust uses owned
values and private construction, with the same semantic checks and rejection
precedence.

## 7. Configuration update and activation

A fee-configuration update is a configuration-only command. It cannot contain
or compose with a fee-bearing settlement. For a pre-state sequence `N`:

```text
require N < U256_MAX
require active.configuration_version < U256_MAX

successor.authority_header.sequence = N + 1
successor.authority_header.chain_deployment_id =
  pre.authority_header.chain_deployment_id
successor.authority_header.fee_distribution_configuration_root =
  recomputed_root(new_configuration)

new.configuration_version =
  active.configuration_version + 1
new.activation_sequence = N + 1
new.chain_deployment_id =
  pre.authority_header.chain_deployment_id
new.fee_distribution_domain_id =
  active.fee_distribution_domain_id
```

The update transition leaves balances, pools, LP balances, nonces, vault,
oracle, fee-apportionment deficits, and perps unchanged. The new configuration
first authorizes a later transition whose pre-state sequence is `N + 1`.

Ordinary weight, destination, and policy rotation is permitted. It preserves
the stable distribution-domain ID and exact fee-apportionment state.

These topology changes remain forbidden in the initial V2 language:

```text
domain creation
domain-ID rotation
domain split
domain merge
domain retirement
domain reuse
```

A role permutation, denominator change, support-rule change, ranking-formula
change, fourth independently weighted role, algorithm version change, or
accepted-language version change requires a separately reviewed migration.

## 8. Sequence and overflow

Every committed accept and committed failure advances:

```text
next.authority_header.sequence =
  pre.authority_header.sequence + 1
```

Ordinary rejection carries no successor. When sequence is `U256_MAX`, no
ordinary or configuration transition can commit.

Configuration-update semantic rejection precedence, after closed admission and
recursive exact-value revalidation, is:

```text
1. SEQUENCE_EXHAUSTED
2. CURRENT_CONFIGURATION_BINDING_FAILED
3. CONFIGURATION_VERSION_EXHAUSTED
4. NEW_CONFIGURATION_BINDING_FAILED
5. CONFIGURATION_UPDATE_LAW_FAILED
```

If sequence and configuration version are both exhausted,
`SEQUENCE_EXHAUSTED` wins. Arithmetic uses checked U256 operations in Python and
Rust. Boundary vectors cover:

```text
sequence = U256_MAX - 1
sequence = U256_MAX
configuration_version = U256_MAX - 1
configuration_version = U256_MAX
both exhausted
```

Forward recovery from a sequence-exhausted V2 deployment requires a separately
reviewed state-version migration. No wraparound or reset exists.

## 9. Content availability and replay

The state header is the authoritative content pointer. Any file, cache,
registry, peer, proof packet, or archive that returns configuration bytes is an
untrusted source.

Only a transition whose support profile declares a fee-configuration read
requires the body. Missing content returns:

```text
MISSING_FEE_CONFIGURATION_CONTENT
```

and produces no successor authority. Unrelated V2 transitions do not acquire a
hidden configuration read.

Every published V2 bundle that consumed a configuration carries the exact
canonical validated-claim bytes in its nested candidate lineage. This is the
normative historical replay source. An immutable content-addressed archive may
provide an operational cache; it is not an authority source.

## 10. Canonical schemas and language parity

Revision 3 adds these exact schema families:

```text
zenodex/fcis/deployment/bootstrap-anchor/v2
zenodex/fcis/state/authority-header/v2
zenodex/fcis/migration/v1-to-v2-manifest/v2
zenodex/fcis/migration/verified-v1-to-v2-authority/v2
zenodex/fcis/state/committed-dex-state/v2
zenodex/fcis/state/committed-dex-snapshot/v5
zenodex/fcis/fee-distribution/state-bound-configuration/v2
```

The authority-header projection has this exact field registry:

```text
chain_deployment_id
sequence
fee_distribution_configuration_root
```

The bootstrap-anchor projection has:

```text
chain_deployment_id
expected_migration_manifest_root
```

The migration-manifest projection has exactly the nine fields in section 4.
Canonical JSON sorts object keys. The schema registry fixes field names, exact
types, required presence, and unknown-field rejection; in-memory insertion or
source order does not define canonical bytes.

Public decoding of bootstrap-anchor, migration-manifest, or
verified-migration-authority projection bytes cannot construct
`VerifiedV1ToV2MigrationAuthorityV2`. Only the verifier-pinned comparison in
section 3 owns that constructor.

Python and Rust must emit byte-identical values and roots for:

```text
authority header
migration manifest and root
verified migration authority
initial V2 state and snapshot root
state-bound configuration
configuration update successor
receipt and commit-bundle lineage
every typed rejection boundary
```

## 11. Required falsification and mutation evidence

The implementation packet must bind at least:

1. The exact Revision 2 `zenodex:A` versus `zenodex:B` bootstrap
   counterexample rejects.
2. Wrong deployment rejects at migration. Claim/header deployment mismatch
   rejects at state binding. A self-consistent foreign state remains labeled
   foreign and rejects at every local receipt, bundle, proof, and publication
   verifier.
3. Wrong domain or initial configuration root rejects at migration.
4. Wrong authenticated V1 root publishes nothing.
5. Initial sequence other than `0`, configuration version other than `1`, or
   activation sequence other than `0` rejects.
6. Nonzero legacy scalar dust blocks release migration.
7. A second migration and a V2-to-V1 downgrade reject structurally.
8. A historical state-bound value cannot create current-state authority.
9. A configuration update racing a settlement makes the settlement bundle
   stale under the single pre-root CAS.
10. Weight, destination, and policy rotation preserve the stable domain ID and
    exact fee-apportionment deficits.
11. Domain creation, ID rotation, split, merge, retirement, and reuse reject.
12. Every nested post-validation mutation rejects at the next use and at
    commit.
13. Header, state, state-root, migration, receipt, bundle, and reject bytes
    match across Python and Rust.
14. Removing any deployment-anchor comparison, pre-root comparison, sequence
    increment, version increment, activation boundary, nested-lineage binding,
    or point-of-use revalidation kills a named test.
15. Adding a public state-bound constructor, stable current-authority value,
    downgrade route, dual fee namespace, or configuration lookup inside the
    core fails the structural checker.

## 12. Pattern and boundary record

**Chosen pattern:** content-addressed configuration plus a deployment-scoped
committed header, verifier-pinned migration authority, subject-bound state
lineage, and one commit-time CAS.

**Rejected alternatives:**

- Full configuration body in every state: safe but duplicates content.
- Root-only Revision 2 header: fails deployment bootstrap authority.
- Mutable external active-configuration pointer: adds a second authority and
  requires an atomic dual comparison.
- Stable shell-created authenticated value: becomes stale immediately after a
  concurrent commit.
- Loose copied lineage fields: creates substitution surfaces.

**Mechanical guarantees:**

- configuration integrity and exact body identity from the committed root;
- deployment identity continuity after authenticated bootstrap;
- deterministic initial state;
- update and ABA detection through the single state root;
- typed separation between state binding and current publication;
- historical replay content in the published bundle.

**Explicit non-guarantees:**

- who is politically or legally authorized to select the bootstrap anchor;
- production datastore linearizability or crash recovery;
- external content-cache availability;
- mounted migration, settlement, proof, or publication behavior;
- governance authorization of later configuration updates.

## 13. Checkpoint sequence

```text
B1B-0R  focused independent review of Revision 3
B1B-1   header, bootstrap-anchor, and migration-manifest values,
         schemas, canonical Python/Rust codecs, and shared vectors
B1B-2   controlled migration authority and deterministic V1-to-V2
         migration reference transition
B1B-3   committed V2 state, snapshot-v5 root, and state admission
B1B-4   controlled state-bound derivation and hostile-mutation evidence
B1B-5   candidate, receipt, patch, proof-input, and bundle lineage
B1B-6   reference commit race, sequence, retry, and replay evidence
```

Every checkpoint remains unmounted. Production migration, shell, datastore,
proof-verifier, and runtime authority require separate promotion gates.

## 14. Promotion rule

Revision 3 remains a testable hypothesis until a focused independent review
attempts the counterexamples in section 11. A prose approval does not implement
the bootstrap anchor or migration. B1B-1 may begin only after the review
returns:

```text
APPROVE_B1B1_REVISION_3_UNMOUNTED
```

Any unresolved way for caller-selected deployment, manifest, pre-root,
configuration, sequence, or version values to create the first V2 authority is
a `NO_GO`.
