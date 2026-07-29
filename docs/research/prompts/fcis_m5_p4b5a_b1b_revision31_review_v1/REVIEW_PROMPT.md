# Independent review prompt: B1B Revision 3.1

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: fa22950b6691d646d04c49efb43e08c78b9ae4da
refuted Revision 3: 798f4ba862ff07cf1f92b54946c67e13e7a939b6
refuted Revision 2: 14f5cb535250858cc1cf0ce00b8f6f6ebcd6e2d7
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 3.1 retain every independent source fact until the exact
authority use that needs it, while preserving a narrow unmounted B1B-1?

The intended design is:

```text
untrusted canonical carriers
  -> point-of-use migration derivation with an independently pinned verifier
  -> exact per-namespace V1-to-V2 successor relation

exact V2 pre-state + configuration claim
  -> compact state-bound value
  -> fresh exact-pre-state rebinding at every use

authority header changes
  -> closed migration | ordinary advance | configuration update algebra

store-current exact state
  -> commit-time rederivation/rebinding
  -> one expected-pre-root atomic publication
```

The design must resist coordinated changes to all self-consistent wrapper
fields. Hash recomputation, private construction, frozen dataclasses, and a
current-root comparison cannot substitute for a missing independent source.

## Accepted Revision 3 counterexamples

### Counterexample 1: manifest and root change together

Revision 3 let migration consume:

```text
VerifiedV1ToV2MigrationAuthorityV2(manifest, manifest_root)
```

After the pinned anchor left the relation, hostile code could replace both
fields with a different self-consistent manifest/root. The migration core had
no independently pinned expected root left to compare.

### Counterexample 2: header and claim change together

Revision 3 let later consumers use:

```text
StateBoundFeeDistributionConfigurationV2(
    legitimate_pre_state_root,
    substituted_header,
    matching_substituted_claim,
)
```

The whole-state root is not an inclusion proof for the isolated substituted
header. Wrapper self-revalidation could not prove that the header was inside
the state committed by the retained root.

### Counterexample 3: ordinary successor changes configuration

Revision 3 required sequence advancement but did not exhaustively require
ordinary accept and committed failure to preserve deployment ID and
configuration root. A consistently constructed ordinary successor could
install a new configuration outside the dedicated update law.

Do not approve based only on new type names. Verify the complete source
relations.

## Mandatory falsification pass

### A. Pinned-verifier continuity

Trace the independently expected deployment ID and migration-manifest root from
deployment initialization through migration derivation and commit-time
rederivation. Try to invoke any migration-authority use without the pinned
verifier.

Reject a design in which decoded anchor bytes, the manifest, candidate state,
transaction context, an evaluation-time environment variable, a mutable file,
or a caller-selected resolver creates the pin.

### B. Capability substitution and threat model

Determine whether `PinnedDeploymentBootstrapVerifierV2` is a trusted verifier
capability rather than a publicly decoded data wrapper. Confirm that Revision
3.1 explicitly separates hostile mutation of carrier values from arbitrary
replacement of verifier code or its release-pinned profile.

If the later implementation would pass a caller-forgeable object satisfying a
public interface, report the missing construction restriction.

### C. Coordinated migration mutation

Attempt all of:

```text
manifest + manifest root changed together
deployment + manifest root changed together
V1 expected root retained while deployment/domain/configuration changes
bundle candidate changed after initial derivation
bundle-carried V1 state substituted for store-current V1 state
```

Confirm that the same point-of-use operation compares the manifest with the
pinned verifier and rederives from the store's exact current V1 state before
publication.

### D. Exact-state rebinding

Attempt coordinated replacement of:

```text
state-bound header root + configuration claim
state-bound deployment + header + claim
```

while retaining the legitimate `pre_state_root`.

Confirm that every consumer receives the exact pre-state and requires equality
with a fresh binder result. At commit time, the exact pre-state must be the
store's current state inside the atomic operation.

### E. Currentness and stale-state behavior

Construct a valid state-bound configuration for a historical or foreign state.
Confirm it remains bound to that state/deployment. It may become publishable
only when exact-state rebinding and the deployment-specific store-current-root
comparison both succeed.

### F. Exhaustive authority-header transition algebra

Try to create or write an authority header through any path other than:

```text
MigrationHeaderV2
OrdinaryAdvanceV2
ConfigurationUpdateV2
```

Check the full laws:

```text
ordinary accept:
  deployment preserved
  configuration root preserved
  sequence + 1

committed failure:
  deployment preserved
  configuration root preserved
  sequence + 1

configuration update:
  deployment preserved
  configuration root changes only to recomputed new body root
  sequence + 1
  version + 1
  activation = successor sequence
  no fee-bearing settlement
  all economic state and deficits preserved

ordinary rejection:
  no successor authority
```

Reject any generic header patch, public authority constructor, subclass hook,
or open transition registry.

### G. Exact migration projection

Check that migration explicitly preserves:

```text
balances
pools
LP balances
nonces
vault
oracle
perps
```

and requires zero V1 scalar dust plus canonical empty V2 apportionment state.
Search for a hidden type, schema, byte, or semantic conversion under the word
`projection`. Any real conversion needs its own named relation and evidence.

### H. B1B-1 scope isolation

Confirm B1B-1 contains only:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

It must not construct or export a pinned verifier, verified authority,
migration candidate, committed V2 state, state-bound value, migration
successor, configuration update, receipt, bundle, proof input, or mount.

### I. Carrier semantics and canonical parity

Check exact types, Boolean/integer alias rejection, U256 bounds, identifier
rules, digest canonicality, unknown/missing/duplicate fields, full-consumption
decoding, canonical envelopes, domain separation, and Python/Rust byte equality.

Confirm an admitted anchor claim or manifest remains untrusted data even when
all hashes recompute.

### J. Fixed constants, overflow, and rejection precedence

Distinguish structural admission from later migration semantics. A
structurally exact manifest carrying a wrong fixed constant may be decodable,
but migration must reject:

```text
source snapshot != 4
target snapshot != 5
initial sequence != 0
initial configuration version != 1
initial activation sequence != 0
```

Check `U256_MAX - 1`, `U256_MAX`, simultaneous sequence/version exhaustion,
sequence-first precedence, and absence of wraparound or reset.

### K. Rotation, topology, and content

Confirm ordinary weight, destination, and policy rotation preserves the stable
domain and exact deficit state. Confirm domain creation, ID rotation, split,
merge, retirement, and reuse remain absent from the first V2 language.

Check that content storage supplies untrusted availability only. A
configuration-update bundle must retain both active and proposed configuration
claims because it reads both.

### L. Smaller safe construction

Try to remove a carrier field, independent source input, rebind step, or header
transition variant while preserving deployment bootstrap, coordinated-mutation
resistance, migration determinism, exact state binding, update monopoly,
canonical parity, and one-root publication.

Also test whether the compact state-bound value can be eliminated entirely in
favor of fresh binding inside one larger owned evaluation lineage. Report
whether that is materially smaller or simply moves the same relation.

## Automatic no-go conditions

Return `NO_GO` if:

- a migration-authority use lacks the independently pinned verifier;
- decoded or transaction-selected data can create the pin;
- manifest and root can change together without comparison to the pin;
- a state-bound value can be used without the exact pre-state;
- commit-time rebinding uses only a bundle-carried state;
- an ordinary accept or committed failure can change deployment ID or
  configuration root;
- a generic header write or open constructor exists;
- migration leaves a retained namespace unspecified;
- B1B-1 exports any authority-bearing or successor-producing value;
- one untrusted input family supplies every fact needed to create local
  authority;
- Python and Rust cannot share exact canonical carrier bytes.

## Required report

Report:

1. exact target, packet commit, and manifest digest;
2. files and commands inspected, plus anything unavailable;
3. one verdict;
4. findings ordered by severity, each with a minimal witness;
5. a table disposing attacks A through L;
6. whether all three Revision 3 counterexamples are closed;
7. whether every independent source remains present at point of use;
8. exact B1B-1 values, schemas, vectors, and forbidden outputs;
9. residual non-claims;
10. the smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_1_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval authorizes only the narrow unmounted B1B-1 carrier, codec, root,
vector, and structural-checker checkpoint.
